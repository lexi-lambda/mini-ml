#lang racket/base

; This module implements /require scopes/, which provide a syntax introducer-like interface on top of
; `syntax-local-lift-require`. A require scope, created with `make-require-scope!`, encapsulates a set
; of scopes that provide access to a set of module imports, which can be flipped on, added to, or
; removed from a syntax object using `require-scope-introduce`. Creating a require scope immediately
; lifts one or more `#%require` forms to the top level of the module currently being expanded to make
; the imports available, whether or not the resulting require scope is applied to any syntax objects.

(require racket/contract
         racket/list
         syntax/parse
         "misc.rkt")

(provide (contract-out [require-scope? (-> any/c boolean?)]
                       [make-require-scope! (->* [(listof syntax?)]
                                                 [#:flip-scopes? any/c
                                                  #:origin (or/c syntax? #f)]
                                                 require-scope?)]
                       [require-scope-introduce (->* [require-scope? syntax?]
                                                     [(or/c 'flip 'add 'remove)]
                                                     syntax?)])
         phase-level)

;; ---------------------------------------------------------------------------------------------------
;; raw require spec normalization

; `make-require-scope!` accepts a list of multiple raw require specs, but `syntax-local-lift-require`
; only allows lifting a single spec at a time. This is unfortunate, as since there is no equivalent to
; `combine-in` for raw require specs, this potentially demands several lifts for a single call to
; `make-require-scope!`. Since each lifted `#%require` is associated with a fresh scope, a naïve
; implementation of `make-require-scope` would create a new scope for each spec. This enormous number
; of scopes has poor performance implications, and it can cause unbound or ambiguous identifier errors
; to become difficult to read (since they may have dozens of distinct “lifted-require” scopes).
;
; While avoiding multiple lifts per call to `make-require-scope!` is, in general, impossible, it is
; still possible to drastically reduce the number of separate lifts by grouping imports by phase.
; While it isn’t possible to include imports with two different phase shifts in a single spec, all
; imports with the same phase shift can be contained within a single `for-meta` form. Therefore, we
; normalize every raw require spec given to `make-require-scope!` to find its phase shift, then
; collect specs with the same phase shift into grouped specs prior to lifting.

(define-syntax-class phase-level
  #:description "phase level"
  #:commit
  #:attributes []
  [pattern _:exact-integer]
  [pattern #f])

(define-syntax-class (normalized-raw-require-spec #:allow-just-meta? [allow-just-meta? #t]
                                                  #:allow-phase-shift? [allow-phase-shift? #t])
  #:description (if (or allow-just-meta? allow-phase-shift?)
                    "raw require spec"
                    "phaseless raw require spec")
  #:commit
  #:attributes [[phase-restriction 1] [phase-shift 1] [phaseless-spec 1]]
  #:datum-literals [for-meta for-syntax for-template for-label just-meta]
  [pattern (just-meta ~! p:phase-level rs ...)
           #:declare rs (normalized-raw-require-spec #:allow-just-meta? #f
                                                     #:allow-phase-shift? allow-phase-shift?)
           #:fail-unless allow-just-meta? "invalid nesting"
           #:attr [phase-shift 1] (append* (attribute rs.phase-shift))
           #:attr [phaseless-spec 1] (append* (attribute rs.phaseless-spec))
           #:attr [phase-restriction 1] (make-list (length (attribute phaseless-spec)) #'p)]
  [pattern ({~or* {~seq for-meta ~! p:phase-level}
                  {~seq for-syntax ~! {~bind [p #'1]}}
                  {~seq for-template ~! {~bind [p #'-1]}}
                  {~seq for-label ~! {~bind [p #'#f]}}}
            rs ...)
           #:declare rs (normalized-raw-require-spec #:allow-just-meta? allow-just-meta?
                                                     #:allow-phase-shift? #f)
           #:fail-unless allow-phase-shift? "invalid nesting"
           #:attr [phase-restriction 1] (append* (attribute rs.phase-restriction))
           #:attr [phaseless-spec 1] (append* (attribute rs.phaseless-spec))
           #:attr [phase-shift 1] (make-list (length (attribute phaseless-spec)) #'p)]
  [pattern rs
           #:attr [phase-restriction 1] (list #f)
           #:attr [phase-shift 1] (list #'0)
           #:attr [phaseless-spec 1] (list #'rs)])

; Groups raw require specs by their relative phase shift, as described above. Returns a hash that maps
; phase levels to raw require specs.
(define (group-raw-require-specs-by-phase stxs)
  (for/fold ([phase=>specs (hasheqv)])
            ([stx (in-list stxs)])
    (syntax-parse stx
      #:context 'make-require-scope!
      [rs:normalized-raw-require-spec
       (for/fold ([phase=>specs phase=>specs])
                 ([phase-restriction (in-list (attribute rs.phase-restriction))]
                  [phase-shift (in-list (attribute rs.phase-shift))]
                  [phaseless-spec (in-list (attribute rs.phaseless-spec))])
         (define restricted-spec
           (if phase-restriction
               #`(just-meta #,phase-restriction #,phaseless-spec)
               phaseless-spec))
         (hash-update phase=>specs
                      (syntax-e phase-shift)
                      (lambda (specs) (cons restricted-spec specs))
                      '()))])))

;; ---------------------------------------------------------------------------------------------------

(define scopeless-stx (datum->syntax #f #f))

(struct require-scope (introducer))

(define (make-require-scope! raw-require-specs
                             #:flip-scopes? [flip-scopes? #t]
                             #:origin [origin #f])
  (unless (syntax-transforming?)
    (raise-arguments-error 'make-require-scope! "not currently expanding"))

  (define flipped-specs (if flip-scopes?
                            (map syntax-local-introduce raw-require-specs)
                            raw-require-specs))
  (define maybe-track (if origin
                          (lambda (stx) (macro-track-origin stx origin #:flip-scopes? flip-scopes?))
                          values))

  (define phase=>specs (group-raw-require-specs-by-phase flipped-specs))
  (define scoped-stx (for/fold ([scoped-stx scopeless-stx])
                               ([(phase specs) (in-hash phase=>specs)])
                       (define shifted-spec (maybe-track #`(for-meta #,phase #,@specs)))
                       (syntax-local-lift-require shifted-spec scoped-stx)))
  (require-scope (make-syntax-delta-introducer scoped-stx scopeless-stx)))

(define (require-scope-introduce rsc stx [mode 'flip])
  ((require-scope-introducer rsc) stx mode))
