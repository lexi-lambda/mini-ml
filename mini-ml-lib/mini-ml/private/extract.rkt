#lang racket/base

; This module defines the building blocks needed to implement /program extraction/, the system by
; which a language’s custom intermediate representation is translated into Racket core forms. For the
; most part, this process is direct: extraction is mostly implemented via straightforward, mechanical
; translation of the custom language’s core forms into their Racket equivalents — custom language
; definitions become Racket definitions, and custom language expressions become Racket expressions.
;
; There are, however, a few subtleties that make the process more complicated. Broadly speaking, there
; are two significant problems that arise from a naïve approach to program extraction.
;
;   1. Avoiding duplication of compile-time effects. When a program includes phase 1 (or higher) code,
;      in some way or another, the code is evaluated during the compilation of the program. Often, we
;      imagine this code as “disappearing” after it is evaluated — macros are expanded leaving a
;      macro-free program behind — but this is not always true. Module-level macro /definitions/ are
;      not “erased” in this sense, since they must be available to other modules that import them.
;      Therefore, some compile-time code may, indeed, be left behind in a fully-expanded program.
;
;      It is this non-erased code that can cause trouble. The code must be evaluated during expansion
;      of the program, yet it must /also/ be left behind in the expanded code. Ordinarily, the Racket
;      macroexpander will re-evaluate this fully-expanded code as it traverses the module’s expansion
;      a final time, and if the code has any side effects, this can lead to disaster. It will be
;      evaluated twice — once during the custom expansion process, and a second time during the Racket
;      expander’s final pass — leading to an unwanted duplication of effects.
;
;      The solution to this is /suspension/. We arrange for the evaluation of compile-time code to be
;      skipped (or “suspended”) during the Racket expander’s final pass, avoiding the duplication of
;      effects, but we ensure the code will still be re-evaluated on future visits to the module. The
;      machinery involved in this process is described later in this module, at the top of the section
;      that implements it.
;
;   2. Cooperation with Check Syntax. DrRacket’s Check Syntax tool (which is also used by other
;      tooling) is designed to extract static information about the structure of a module and present
;      it to the programmer to help them reason, explore, and structurally modify their program.
;      Compared to other programming languages, this is an especially daunting task in Racket: macros
;      can contort the program in any number of ways, so a development environment has no way of
;      knowing what any identifier in the program is even bound to without running arbitrary Racket
;      code.
;
;      To make Check Syntax’s task more tractable, the macroexpander cooperates by leaving information
;      behind about where pieces of syntax in a fully-expanded program came from. This is done through
;      a collection of syntax properties: 'origin, 'disappeared-use, 'disappeared-binding, and
;      'sub-range-binders. While the expander introduces some of these properties automatically, and
;      for most ordinary programs, the automatic mechanisms in place are enough for Check Syntax to
;      work well, the complexity of understanding the structure of a custom language requires some
;      extra cooperation on the part of the language author.
;
;      For simple cases, like when a macro inspects the transformer binding of an identifier or
;      matches an identifier literally, syntax/parse is capable of adding the necessary residual
;      properties automatically. However, for more complicated situations, additional care is needed.
;      Types are an example of one such situation, as they are erased in the extracted program. Care
;      must be taken to ensure that not only is the binding structure of the types themselves
;      preserved for Check Syntax, but the properties already present on the types (due to
;      macroexpansion at the type level) are also preserved. This module provides some simple
;      functions to make it easier to get things right.
;
; This module provides utilities to make solving both of the above two problems simpler.

(require (for-meta 2 racket/base)
         (for-syntax racket/base
                     racket/contract
                     racket/list
                     racket/syntax
                     syntax/id-set
                     syntax/parse/define
                     threading
                     "util/syntax.rkt")
         syntax/parse/define)

(begin-for-syntax
  (provide (contract-out
            ; suspension
            [suspenders? (-> any/c boolean?)]
            [make-suspenders (-> suspenders?)]
            [current-suspenders (parameter/c (or/c suspenders? #f))]
            [suspend-expression (->* [syntax?]
                                     [suspenders?
                                      #:phase exact-positive-integer?
                                      #:values exact-nonnegative-integer?]
                                     syntax?)]
            [suspend-racket-decl (->* [syntax?]
                                      [suspenders?
                                       #:phase exact-positive-integer?]
                                      syntax?)]
            [suspenders->racket-decl (->* [] [suspenders?] syntax?)]

            ; residual
            [residual? (-> any/c boolean?)]
            [make-residual (->* []
                                [(listof residual?)
                                 #:origin (or/c syntax? #f)
                                 #:uses (listof identifier?)
                                 #:bindings (listof identifier?)
                                 #:flip-scopes? any/c]
                                residual?)]
            [syntax-track-residual (-> syntax? residual? syntax?)])))

;; ---------------------------------------------------------------------------------------------------
;; suspension

; The process of suspension described at the top of this module is implemented in a conceptually
; simple way:
;
;   1. We keep track whether the current module is being expanded or if it is being visited.
;
;   2. We wrap all compile-time expressions in conditional expressions that only evaluate the
;      expression in the second case (when the module is being visited) but not the first (when the
;      module is being expanded).
;
; In practice, implementing this is more involved than it sounds.
;
; To keep track of whether or not the module is currently being expanded, we can define a compile-time
; variable, `is-suspended?`, which is initialized to `#f`. We then insert the form
;
;   (let-syntax ([_ (set! is-suspended? #t)]) (void))
;
; into the body of the module. This will cause the `is-suspended?` variable to be set to `#t` when the
; `let-syntax` form is expanded, but since the compile-time parts of `let-syntax` are erased in its
; expansion, the effect will /not/ be performed when the module is visited. We can then instrument
; expressions inside `define-syntaxes` or `begin-for-syntax` forms to conditionally branch upon the
; value of the `is-suspended?` variable.
;
; However, even this is not enough. Since `begin-for-syntax` forms may be nested, we actually need
; /several/ `is-suspended?` variables, one at each phase. Likewise, we need to `set!` each of these
; variables at the relevant phase. For example, for a module that has compile-time code at both
; phase 1 and phase 2, we want to produce the following declarations:
;
;   (begin-for-syntax
;     (define is-suspended?/1 #f)
;     (begin-for-syntax
;       (define is-suspended?/2 #f)))
;
;   (let-syntax ([_ (begin
;                     (set! is-suspended?/1 #t)
;                     (let-syntax ([_ (set! is-suspended?/2 #t)]) (void)))])
;     (void))
;
; The generation of these declarations is managed by /suspenders/. A set of suspenders, created with
; `make-suspenders`, encapsulates a mapping from compile-time phase levels to `is-suspended?`
; identifiers. The `suspend-expression` function generates a suspended version of an expression at a
; given phase, and it records in the set of suspenders which phases include suspended expressions.
; Likewise, the `suspend-racket-decl` function is like `suspend-expression`, except that it handles
; compile-time declarations, including nested uses of `begin-for-syntax`. The
; `suspenders->racket-decl` function generates the appropriate declaration of the above shape using
; the information recorded by calls to `suspend-expression` and `suspend-racket-decl`.

; When `suspenders->racket-decl generates a set of nested `let-syntax` forms, as described above,
; the form cannot actually be directly inserted into a module as-is. The reason for this is that
; the Racket expander attempts to expand module-level expressions last, after all `define-syntaxes`
; and `begin-for-syntax` forms have already been expanded. This is a problem, since it will delay the
; necessary side-effects until the compile-time expressions have already been evaluated, which is too
; late. This macro forces the expansion of the `let-syntax` forms as soon as it is expanded,
; intentionally defeating the expander’s partial expansion of module-level expressions, ensuring the
; side-effects occur when necessary.
(define-simple-macro (force-expansion e:expr)
  #:do [(local-expand #'e 'expression '())]
  (begin))

(begin-for-syntax
  (struct suspenders (ids))

  (define (make-suspenders)
    (suspenders (make-hasheqv)))

  (define current-suspenders (make-parameter #f))

  (define (is-suspended?-id phase [suspenders (current-suspenders)])
    (hash-ref! (suspenders-ids suspenders) phase (lambda () (generate-temporary 'is-suspended?))))

  ; When generating expressions at arbitrary phases, we have to be careful to arrange for the
  ; identifiers we introduce to actually be bound at the appropriate phase. To do this, we apply
  ; `syntax-shift-phase-level` to any pieces of syntax we introduce. We have to be careful, however,
  ; to restrict ourselves to introducing identifiers bound in '#%kernel, since otherwise, it’s
  ; possible the relevant module won’t actually be instantiated at the correct phase.
  ;
  ; Performing this shifting is noisy, so the `quasishift` macro helps to avoid the noise. It is like
  ; `quasisyntax`, except that the resulting syntax object is phase shifted. Syntax objects
  ; interpolated into the template using `unsyntax` or `unsytax-splicing` are /not/ shifted, which
  ; ensures the original expressions’ phases are left untouched.
  ;
  ; To interpolate syntax that /should/ be shifted into a template defined using `quasisyntax`, use
  ; syntax pattern variables instead of `unsyntax` or `unsyntax-splicing`, since these will be shifted
  ; along with the rest of the syntax object.
  (define-syntax-parser quasishift
    [(_ phase-shift-e:expr template)
     #:with shifting-template (let loop ([stx #'template])
                                (syntax-parse stx
                                  #:literals [unsyntax unsyntax-splicing]
                                  [(unsyntax ~! e:expr)
                                   #'#,(antishift e)]
                                  [(unsyntax-splicing ~! e:expr)
                                   #'#,@(map antishift e)]
                                  [(a ...+ . b)
                                   (datum->syntax this-syntax
                                                  (append (map loop (attribute a)) (loop #'b))
                                                  this-syntax
                                                  this-syntax)]
                                  [_
                                   this-syntax]))
     #`(let* ([phase-shift phase-shift-e]
              [phase-antishift (- phase-shift)])
         (define (antishift stx) (syntax-shift-phase-level stx phase-antishift))
         (syntax-shift-phase-level #`shifting-template phase-shift))])

  (define (suspend-expression stx [suspenders (current-suspenders)]
                              #:phase [phase (add1 (syntax-local-phase-level))]
                              #:values [num-vals 1])
    (define/with-syntax vals-expr (if (eqv? num-vals 1)
                                      #''#f
                                      #`(values #,@(make-list num-vals #''#f))))
    (quasishift phase (if #,(is-suspended?-id phase suspenders) vals-expr #,stx)))

  (define (suspend-racket-decl stx [suspenders (current-suspenders)]
                               #:phase [phase (add1 (syntax-local-phase-level))])
    (let loop ([stx stx]
               [phase phase])
      (call-with-disarmed-syntax
       stx
       (syntax-parser
         #:context 'suspend-racket-decl
         #:literal-sets [(kernel-literals #:phase phase)]
         [({~or #%require #%provide #%declare module} ~! . _)
          this-syntax]
         [({~and head {~or {~and define-values {~bind [stx? #f]}}
                           {~and define-syntaxes {~bind [stx? #t]}}}}
           ~! [x:id ...] e:expr)
          #:do [(define e-phase (if (attribute stx?) (add1 phase) phase))]
          (datum->syntax this-syntax
                         (list #'head
                               (attribute x)
                               (suspend-expression #'e #:values (length (attribute x)) #:phase phase))
                         this-syntax
                         this-syntax)]
         [(head:begin-for-syntax ~! d ...)
          (datum->syntax this-syntax
                         (cons #'head (map (lambda (d) (loop d (add1 phase))) (attribute d)))
                         this-syntax
                         this-syntax)]
         [_
          (suspend-expression this-syntax #:phase phase)]))))

  (define (suspenders->racket-decl [suspenders (current-suspenders)])
    (unless (zero? (syntax-local-phase-level))
      (raise-arguments-error
       'suspenders->racket-decl "only allowed when transforming relative phase level 0"
       "phase level" (syntax-local-phase-level)))

    (define ids (suspenders-ids suspenders))
    (cond
      [(hash-empty? ids)
       #'(begin)]
      [else
       (define max-phase (argmax values (hash-keys ids)))
       (define-values [defn-decl set-expr]
         (for/fold ([defn-decl (syntax-shift-phase-level #'(begin) max-phase)]
                    [set-expr (syntax-shift-phase-level #'(#%plain-app void) max-phase)])
                   ([phase (in-range max-phase 0 -1)])
           (define id (hash-ref ids phase #f))
           (values (quasishift (sub1 phase)
                               (begin-for-syntax
                                 #,@(if id (list (quasishift phase (define-values [#,id] '#f))) '())
                                 #,defn-decl))
                   (quasishift (sub1 phase)
                               (let-syntaxes
                                ([(_) #,(if id
                                            (quasishift phase (begin (set! #,id '#t) #,set-expr))
                                            set-expr)])
                                (#%plain-app void))))))
       #`(begin #,defn-decl (force-expansion #,set-expr))])))

;; ---------------------------------------------------------------------------------------------------
;; residual tracking

(begin-for-syntax
  (struct residual (origins uses bindings))

  (define (residual-merge rss)
    (residual (append-map residual-origins rss)
              (append-map residual-uses rss)
              (append-map residual-bindings rss)))

  (define (make-residual [rss '()]
                         #:origin [origin #f]
                         #:uses [uses '()]
                         #:bindings [bindings '()]
                         #:flip-scopes? [flip-scopes? #t])
    (define maybe-flip (if flip-scopes? syntax-local-introduce values))
    (residual-merge (cons (residual (if origin (list (maybe-flip origin)) '())
                                    (map maybe-flip uses)
                                    (map maybe-flip bindings))
                          rss)))

  (define (syntax-track-residual stx r)
    (~> (for/fold ([stx stx])
                  ([origin (in-list (residual-origins r))])
          (macro-track-origin stx origin #:flip-scopes? #f))
        (syntax-property-extend 'disappeared-use (residual-uses r) append)
        (syntax-property-extend 'disappeared-bindings (residual-bindings r) append))))
