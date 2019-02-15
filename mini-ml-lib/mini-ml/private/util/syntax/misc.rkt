#lang racket/base

(require (for-syntax racket/base)
         racket/contract
         racket/match
         syntax/parse
         syntax/parse/define
         syntax/srcloc
         threading)

(provide (contract-out [module-path-syntax? (-> syntax? boolean?)]
                       [module-path-submodule (->i ([mod-path (or/c module-path? module-path-syntax?)]
                                                    [submod-name (mod-path)
                                                                 (if (syntax? mod-path)
                                                                     (or/c symbol? identifier?)
                                                                     symbol?)])
                                                   [result (mod-path) (if (syntax? mod-path)
                                                                          module-path-syntax?
                                                                          module-path?)])]
                       [syntax-armed? (-> syntax? boolean?)]
                       [call-with-disarmed-syntax (->* [(and/c syntax? (not/c syntax-tainted?))
                                                        (-> (and/c syntax? (not/c syntax-armed?))
                                                            (and/c syntax? (not/c syntax-tainted?)))]
                                                       [#:use-mode? any/c
                                                        #:failure-proc (-> any)]
                                                       any)]
                       [syntax-property-extend (->* [syntax? any/c any/c]
                                                    [(-> any/c any/c any/c)]
                                                    syntax?)]
                       [adjust-property (-> syntax? any/c (-> any/c any/c) syntax?)]
                       [recursively-adjust-property (-> (and/c syntax? (not/c syntax-tainted?))
                                                        any/c
                                                        (-> any/c any/c)
                                                        syntax?)]
                       [make-renamed-identifier (->* [identifier? symbol?]
                                                     [#:phase (or/c exact-integer? #f)
                                                      #:srcloc source-location?
                                                      #:props (or/c syntax? #f)]
                                                     identifier?)]
                       [derived-id (-> string? syntax? string? syntax?)]
                       [macro-track-origin (->* [syntax? syntax?] [#:flip-scopes? any/c] syntax?)]
                       [introduce-everywhere (-> syntax? (-> syntax? syntax?) syntax?)])
         quote-syntax/launder)

;; ---------------------------------------------------------------------------------------------------
;; module paths

(define (module-path-syntax? stx)
  (and (syntax? stx) (module-path? (syntax->datum stx))))

(define (module-path-submodule base-path submod-name)
  (if (syntax? base-path)
      (syntax-parse base-path
        #:context 'module-path-submodule
        #:datum-literals [submod]
        [(head:submod ~! more ...)
         (datum->syntax this-syntax
                        `(,#'head ,@(attribute more) ,(datum->syntax #f submod-name))
                        this-syntax
                        this-syntax)]
        [_
         (datum->syntax this-syntax
                        (list (datum->syntax #'here 'submod)
                              this-syntax
                              (datum->syntax #f submod-name))
                        this-syntax
                        this-syntax)])
      (match base-path
        [(cons 'submod more)
         `(submod ,@more ,submod-name)]
        [_
         `(submod ,base-path ,submod-name)])))

;; ---------------------------------------------------------------------------------------------------
;; taints

(define (syntax-armed? stx)
  (define (tainted? v)
    (and (syntax? v) (syntax-tainted? v)))
  (or (syntax-tainted? stx)
      (match (syntax-e stx)
        [(list* as ... b)
         (or (ormap tainted? as) (tainted? b))]
        [(vector as ...)
         (ormap tainted? as)]
        [(hash-table [ks vs] ...)
         (ormap tainted? vs)]
        [(? prefab-struct-key (app struct->vector (vector _ as ...)))
         (ormap tainted? as)]
        [(box a)
         (tainted? a)]
        [_ #f])))

(define/contract (call-with-disarmed-syntax stx proc
                                            #:use-mode? [use-mode? #f]
                                            #:failure-proc [failure-proc #f])
  (->* [(and/c syntax? (not/c syntax-tainted?))
        (-> (and/c syntax? (not/c syntax-armed?))
            (and/c syntax? (not/c syntax-tainted?)))]
       [#:use-mode? any/c
        #:failure-proc (-> any)]
       any)
  (let ([disarmed-stx (syntax-disarm stx #f)])
    (if (syntax-armed? disarmed-stx)
        (if failure-proc
            (failure-proc)
            (raise-arguments-error 'call-with-disarmed-syntax "could not disarm syntax object"
                                   "syntax object" stx))
        (syntax-rearm (proc disarmed-stx) stx use-mode?))))

;; ---------------------------------------------------------------------------------------------------
;; properties

(define (syntax-property-extend stx key new-val [extend cons])
  (define old-val (syntax-property stx key))
  (syntax-property stx key (if old-val (extend new-val old-val) new-val)))

; Modifies the property of a syntax object by applying a procedure to its value. If the syntax object
; does not contain any such property, the original syntax object is returned. Otherwise, the
; property’s value is recursively traversed as a tree of cons pairs, and the procedure is applied to
; each leaf to produce a new result.
(define (adjust-property stx key proc)
  (let ([val (syntax-property stx key)])
    (if val
        (syntax-property stx key
                         (let loop ([val val])
                           (cond [(list? val) (map loop val)]
                                 [(pair? val) (cons (loop (car val)) (loop (cdr val)))]
                                 [else (proc val)])))
        stx)))

; Like adjust-property, but recursively walks the syntax object and applies the function to each
; subform. Handles arming and disarming as necessary.
(define (recursively-adjust-property stx key proc)
  (let loop ([stx stx])
    (call-with-disarmed-syntax
     stx
     (lambda (disarmed)
       (~> (match (syntax-e disarmed)
             [(list a ...) (map loop a)]
             [(list* a ..1 b) (append (map loop a) (loop b))]
             [a a])
           (datum->syntax disarmed _ disarmed disarmed)
           (adjust-property key proc))))))

;; ---------------------------------------------------------------------------------------------------
;; syntax binding sets

; A small wrapper around `syntax-binding-set-extend` and `identifier-binding` to make it possible to
; create an identifier with the same binding as another binding but with an arbitrary name.
(define (make-renamed-identifier internal-id external-sym
                                 #:phase [phase (syntax-local-phase-level)]
                                 #:srcloc [srcloc internal-id]
                                 #:props [props internal-id])
  (match (identifier-binding internal-id phase)
    [(list source-mod source-sym nominal-source-mod nominal-source-sym
           source-phase import-phase nominal-export-phase)
     (define binding-set (syntax-binding-set-extend (syntax-binding-set)
                                                    external-sym
                                                    phase
                                                    source-mod
                                                    #:source-symbol source-sym
                                                    #:source-phase source-phase
                                                    #:nominal-module nominal-source-mod
                                                    #:nominal-phase nominal-export-phase
                                                    #:nominal-symbol nominal-source-sym
                                                    #:nominal-require-phase import-phase))
     (define binding-stx (syntax-binding-set->syntax binding-set #f))
     (datum->syntax binding-stx external-sym (build-source-location-vector srcloc) props)]
    [other-binding
     (raise-arguments-error 'identifier->syntax-binding-set
                            "identifier is not bound to a module-level binding"
                            "identifier" internal-id
                            "binding" other-binding)]))

;; ---------------------------------------------------------------------------------------------------
;; cooperating with check syntax

; Unhygienically forges a new identifier from an existing one and adds an appropriate
; 'sub-range-binders property to track the relationship between the two.
(define (derived-id prefix id suffix)
  (define id-str (symbol->string (syntax-e id)))
  (define id-len (string-length id-str))
  (define new-id (datum->syntax id (string->symbol (string-append prefix id-str suffix))))
  (syntax-property new-id 'sub-range-binders
                   (vector (syntax-local-introduce new-id) (string-length prefix) id-len 0.5 0.5
                           (syntax-local-introduce id) 0 id-len 0.5 0.5)))

; A small wrapper around `syntax-track-origin` that extracts the identifier prepended to the 'origin
; property from the provided original syntax, assuming the new syntax was produced by a Racket-like
; macro transformation. By default, it applies `syntax-local-introduce` to the extracted identifier
; before passing it to `syntax-track-origin`.
(define (macro-track-origin new-stx orig-stx #:flip-scopes? [flip-scopes? #t])
  (define id-stx (syntax-parse orig-stx
                   #:context 'macro-track-origin
                   [x:id #'x]
                   [(head:id . _) #'head]))
  (syntax-track-origin new-stx
                       orig-stx
                       (if flip-scopes?
                           (syntax-local-introduce id-stx)
                           id-stx)))

; Applies the given syntax introducer procedure to both the given syntax object and all
; syntax objects inside syntax properties of the given syntax object that are used by Check Syntax.
(define (introduce-everywhere stx introduce)
  (define (introduce-stx v)
    (if (syntax? v) (introduce v) v))
  (~> (introduce stx)
      (recursively-adjust-property 'origin introduce-stx)
      (recursively-adjust-property 'disappeared-use introduce-stx)
      (recursively-adjust-property 'disappeared-binding introduce-stx)
      (recursively-adjust-property 'sub-range-binders
                                   (match-lambda
                                     [(vector (? syntax? id-1) start-1 span-1 x-1 y-1
                                              (? syntax? id-2) start-2 span-2 x-2 y-2)
                                      (vector (introduce id-1) start-1 span-1 x-1 y-1
                                              (introduce id-2) start-2 span-2 x-2 y-2)]
                                     [other other]))))

; Like `quote-syntax`, but adds a macro-introduction scope so that the syntax will not be original in
; the sense of `syntax-original?`, and Check Syntax will ignore it for the purpose of drawing binding
; arrows. Note that if the syntax will eventually end up in binding position, this is a bad idea,
; since the extra scope will prevent uses from seeing the binding.
(define-syntax-parser quote-syntax/launder
  [(_ stx)
   (datum->syntax this-syntax
                  (list #'quote-syntax
                        ((make-syntax-introducer) #'stx))
                  this-syntax
                  this-syntax)])
