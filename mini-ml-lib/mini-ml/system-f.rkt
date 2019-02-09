#lang racket/base

;; System F
;
; d ::=
;   (#%define x : t e)
;   (#%define-syntax x any)
;   (#%define-type (x x ...) (x t ...) ...)
;   (#%define-main e)
;   (#%begin d ...)
;   (#%begin-for-syntax any ...)
;
; e ::=
;   x
;   (#%datum literal)
;   (#%lambda [x : t] e)
;   (#%app e e)
;   (#%Lambda [x : t] e)
;   (#%App e t)
;   (#%case e [(x [x : t] ...) e] ...)
;
; t ::=
;   x
;   (#%app t t)
;   (#%forall [x : t] t)

(require (for-meta 2 racket/base
                     racket/syntax
                     syntax/parse/class/struct-id
                     "private/util/syntax.rkt")
         (for-syntax racket/base
                     racket/contract
                     racket/format
                     racket/list
                     racket/match
                     racket/set
                     racket/syntax
                     syntax/id-table
                     syntax/parse/class/local-value
                     syntax/parse/define
                     syntax-generic2
                     threading
                     "private/util/syntax.rkt")
         syntax/parse/define
         "private/extract.rkt"
         "private/namespace.rkt")

(provide (rename-out [system-f:#%module-begin #%module-begin]))

(define-namespace value #:unique)
(define-namespace type #:unique)

(provide/namespace namespace:value
                   (for-syntax decl-transformer
                               decl-id-transformer
                               expr-transformer
                               expr-id-transformer
                               type-transformer
                               type-id-transformer
                               require-spec-transformer
                               provide-spec-transformer)
                   (rename-out [#%require require]
                               [#%provide provide]
                               [system-f:shift shift]
                               [#%define define]
                               [#%define-syntax define-syntax]
                               [#%define-main define-main]
                               [#%begin begin]
                               [#%begin-for-syntax begin-for-syntax]
                               [#%lambda lambda]
                               [#%lambda λ]
                               [#%App App]
                               [#%Lambda Lambda]
                               [sysf:+ +]
                               [sysf:unit unit]
                               [sysf:println println]))

(provide/namespace namespace:type
                   (rename-out [#%forall forall])
                   Type -> Unit Integer String)

;; ---------------------------------------------------------------------------------------------------
;; reader

(module reader racket/base
  (require (submod "private/namespace.rkt" module-reader))

  (provide (rename-out [system-f:read read]
                       [system-f:read-syntax read-syntax])
           get-info)

  (define-values [system-f:read system-f:read-syntax get-info]
    (make-namespaced-module-reader 'mini-ml/system-f #:language-name 'system-f)))

;; ---------------------------------------------------------------------------------------------------
;; keywords

(begin-for-syntax
  (define-syntax-class system-f-keyword-class
    #:description #f
    #:attributes [-literals]
    [pattern
     x:id
     #:attr -literals (derived-id "core-" #'x "-literals")]))

(define-simple-macro (define-keywords [class:system-f-keyword-class (x:id ...)] ...)
  #:with [unique-x ...] (remove-duplicates (append* (attribute x)) bound-identifier=?)
  (begin
    (define-syntax unique-x (generics)) ...
    (begin-for-syntax
      (define-literal-set class.-literals [x ...]) ...)))

(define-keywords
  (type [#%type:app #%forall])
  (require-spec [#%binding #%union])
  (provide-spec [#%binding #%union]))

;; ---------------------------------------------------------------------------------------------------
;; `define-syntax-info`

; It’s common to want to attach compile-time information to an identifier, which is normally done
; using a struct that holds the information, but this becomes awkward if a single identifier needs to
; serve multiple meanings (such as, for example, a data constructor that serves as both a variable and
; a pattern). The traditional approach is to use structure type properties, but this can be
; cumbersome. Syntax generics make things easier, but they use dispatch machinery that makes them more
; awkward than necessary to match on with syntax/parse.
;
; `define-syntax-info` is a thin wrapper around syntax generics to better serve the above use case.
; The definitions are morally like structures, with fields containing data, but that data is actually
; just stored in a closure inside a generic definition. Accessing the data is done via a syntax class,
; which binds the fields as attributes.

(begin-for-syntax
  (define dispatch-on-id-only
    (syntax-parser
      [x:id #'x]
      [_ #f]))

  (define-simple-macro (define-syntax-info name:id [field:id ...]
                         {~alt {~optional {~seq #:name err-name:expr}
                                          #:defaults ([err-name #`'#,(symbol->string
                                                                      (syntax-e #'name))])}
                               {~optional {~seq #:constructor-name
                                                {~or ctor-id:id {~and #f {~bind [omit-ctor? #t]}}}}}}
                         ...)
    #:attr make-name (and (not (attribute omit-ctor?))
                          (or (attribute ctor-id) (derived-id "make-" #'name "")))
    #:with name? (format-id #'name "~a?" #'name)
    #:with expand-name (derived-id "expand-" #'name "")
    #:with name-id (derived-id "" #'name "-id")
    #:with [field-tmp ...] (generate-temporaries (attribute field))
    (begin
      (define-syntax-generic name #:dispatch-on dispatch-on-id-only)
      {~? (define (make-name field-tmp ...)
            (generics [name (lambda (stx) (values field-tmp ...))]))}
      (define (expand-name stx [sc #f])
        (apply-as-transformer name sc stx))
      (define-syntax-class (name-id [sc #f])
        #:description err-name
        #:commit
        #:attributes [field ...]
        [pattern x
                 #:when (name? #'x sc)
                 #:do [(define-values [field-tmp ...] (expand-name #'x sc))]
                 {~@ #:attr field field-tmp} ...])))

  ; Variables, type variables, and type constructors are really just special bindings with a type or
  ; kind attached. Module-level runtime variables also have an associated Racket binding, for use
  ; during program extraction.
  (define-syntax-info var (type)
    #:name "variable"
    #:constructor-name make-local-var)
  (define-syntax-info module-var (racket-id)
    #:constructor-name #f)
  (define (make-module-var type racket-id)
    (generics
     [var (lambda (stx) type)]
     [module-var (lambda (stx) racket-id)]))

  (define-syntax-info type-var (kind) #:name "type variable")
  (define-syntax-info type-constructor (kind) #:name "type constructor"))

;; ---------------------------------------------------------------------------------------------------
;; type operations

(begin-for-syntax
  (define-syntax-class type
    #:description "type"
    #:opaque
    #:attributes []
    [pattern _:expr])

  (define/contract type->string
    (-> syntax? string?)
    (syntax-parser
      #:context 'type->string
      #:literal-sets [core-type-literals]
      #:datum-literals [:]
      [x:id
       (~a (syntax-e #'x))]
      [(#%type:app ~! t1:type t2:type)
       (~a "(" (type->string #'t1) " " (type->string #'t2) ")")]
      [(#%forall ~! [x:id : k:type] t:type)
       (~a "(forall [" (syntax-e #'x) " : " (type->string #'k) "] " (type->string #'t) ")")]))

  (define/contract (type=! actual-t expected-t [sc #f] #:src src-stx)
    (-> syntax? syntax? (or/c scope? #f) #:src syntax? void?)
    (let loop ([actual-t actual-t]
               [expected-t expected-t]
               [ctx (make-immutable-free-id-table)])
      (syntax-parse (list actual-t expected-t)
        #:context 'type=!
        #:literal-sets [core-type-literals]
        #:datum-literals [:]
        [[{~var actual-x (type-var-id sc)} {~var expected-x (type-var-id sc)}]
         #:when (free-identifier=? #'actual-x #'expected-x)
         (void)]
        [[{~var actual-x (type-constructor-id sc)} {~var expected-x (type-constructor-id sc)}]
         #:when (free-identifier=? #'actual-x #'expected-x)
         (void)]
        [[actual-x:id expected-x:id]
         #:when (eq? (free-id-table-ref ctx #'actual-x) (free-id-table-ref ctx #'expected-x))
         (void)]
        [[(#%type:app actual-t1:type actual-t2:type) (#%type:app expected-t1:type expected-t2:type)]
         #:when (and (loop #'actual-t1 #'expected-t1 ctx)
                     (loop #'actual-t2 #'expected-t2 ctx))
         (void)]
        [[(#%forall [actual-x:id : actual-k:type] actual-t:type)
          (#%forall [expected-x:id : expected-k:type] expected-t:type)]
         #:when (and (loop #'actual-k #'expected-k ctx)
                     (loop #'actual-t #'expected-t
                           (let ([v (gensym)])
                             (free-id-table-set* ctx #'actual-x v #'expected-x v))))
         (void)]
        [[_ _]
         (raise-syntax-error
          'system-f "type error" src-stx #f '()
          (format "\n  expected type: ~a\n  actual type: ~a"
                  (type->string expected-t)
                  (type->string actual-t)))]))))

;; ---------------------------------------------------------------------------------------------------
;; expander

(begin-for-syntax
  (define (raise-invalid-thing-error thing stx)
    (define msg (string-append "not a valid " thing))
    (raise-syntax-error 'system-f msg stx))

  (define id-only
    (syntax-parser
      [x:id #'x]
      [_ #f]))

  (define pair-only
    (syntax-parser
      [(x:id . _) #'x]
      [_ #f]))

  (define-syntax-generic core-decl-pass-1)
  (define-syntax-generic core-decl-pass-2)
  (define-syntax-generic core-decl->racket-decl)
  (define-syntax-generic decl-transformer)
  (define-syntax-generic decl-id-transformer #:dispatch-on id-only)

  (define-syntax-generic core-expr)
  (define-syntax-generic core-expr->racket-expr)
  (define-syntax-generic expr-transformer)
  (define-syntax-generic expr-id-transformer #:dispatch-on id-only)

  (define-syntax-generic core-type)
  (define-syntax-generic core-type->residual)
  (define-syntax-generic type-transformer)
  (define-syntax-generic type-id-transformer #:dispatch-on id-only)

  (define-syntax-generic core-require-spec)
  (define-syntax-generic core-require-spec->racket-raw-require-spec)
  (define-syntax-generic require-spec-transformer #:dispatch-on pair-only)

  (define-syntax-generic core-provide-spec)
  (define-syntax-generic core-provide-spec->racket-raw-provide-spec)
  (define-syntax-generic provide-spec-transformer #:dispatch-on pair-only)

  ; FIXME: this comment is out of date!!!
  ; The common case of `prop:id-only?` is to implement a transformer like
  ; `make-variable-like-transformer`, which just expands to a particular piece of syntax, but it needs
  ; to do just a little bit extra in order to make the source locations nice. This implements that.
  (define (make-substituting-transformer replacement-stx)
    (define replacement-datum (syntax-e replacement-stx))
    (lambda (id-stx) (datum->syntax replacement-stx replacement-datum id-stx replacement-stx)))

  (struct e+t (e t) #:transparent)

  (define (e+t-e/t=! v t [sc #f] #:src src-stx)
    (type=! (e+t-t v) t sc #:src src-stx)
    (e+t-e v))

  (define (expand-module stxs)
    (define sc (make-definition-scope))

    (define (do-pass-1 stxs)
      (let loop ([stxs-to-go (map (lambda (stx) (in-scope sc stx)) stxs)]
                 [stxs-deferred '()])
        (match stxs-to-go
          ['()
           (reverse stxs-deferred)]
          [(cons stx stxs-to-go*)
           (syntax-parse stx
             #:literals [#%require #%begin]
             #:datum-literals [:]
             [{~var core (core-decl-pass-1 sc sc)}
              (loop stxs-to-go* (cons (attribute core.value) stxs-deferred))]
             [{~or {~var transformer (decl-id-transformer sc)}
                   {~var transformer (decl-transformer sc)}}
              (loop (cons (macro-track-origin (attribute transformer.value) this-syntax) stxs-to-go*)
                    stxs-deferred)]
             [(head:#%require ~! rs ...)
              #:with [expanded-rs ...] (append-map (lambda (rs) (expand-system-f-require-spec rs sc))
                                                   (attribute rs))
              #:with [racket-rs ...] (map system-f-require-spec->racket-require-spec
                                          (attribute expanded-rs))
              #:do [(define rsc (make-require-scope! (attribute racket-rs) #:origin this-syntax))
                    (define (rsc-introduce stx) (require-scope-introduce rsc stx 'add))]
              (loop (map rsc-introduce stxs-to-go*)
                    (map rsc-introduce (cons (datum->syntax this-syntax
                                                            (cons #'head (attribute expanded-rs))
                                                            this-syntax
                                                            this-syntax)
                                             stxs-deferred)))]
             [(#%begin ~! d ...)
              (loop (append (for/list ([d (in-list (attribute d))])
                              (macro-track-origin d this-syntax))
                            stxs-to-go*)
                    stxs-deferred)]
             [_
              (raise-invalid-thing-error "declaration" this-syntax)])])))

    (define (do-pass-2 stxs)
      (define-values [expanded-decls main-decls]
        (for/fold ([expanded-decls '()]
                   [main-decls '()])
                  ([stx (in-list stxs)])
          (syntax-parse stx
            #:literals [#%define-main]
            #:datum-literals [:]
            [{~var core (core-decl-pass-2 sc)}
              (values (cons (attribute core.value) expanded-decls) main-decls)]
            [(head:#%define-main ~! e:expr)
             #:do [(define e- (e+t-e (expand-expr #'e sc)))]
             (values (cons (datum->syntax this-syntax
                                          (list #'head e-)
                                          this-syntax
                                          this-syntax)
                           expanded-decls)
                     (cons this-syntax main-decls))]
            [_
             (raise-syntax-error 'system-f
                                 "internal error: unexpected form when expanding module body"
                                 this-syntax)])))
      (when (> (length main-decls) 1)
        (raise-syntax-error 'system-f "multiple main declarations" #f #f (reverse main-decls)))
      (reverse expanded-decls))

    (do-pass-2 (do-pass-1 stxs)))

  (define-syntax-class system-f-literal
    #:description #f
    #:commit
    #:attributes []
    [pattern _:exact-integer]
    [pattern _:string])

  (define (expand-expr stx [sc #f])
    (define (recur stx) (expand-expr stx sc))
    (syntax-parse stx
      #:datum-literals [:]
      [{~var core (core-expr sc)}
       (attribute core.value)]
      [{~or {~var transformer (expr-id-transformer sc)}
            {~var transformer (expr-transformer sc)}}
       (recur (macro-track-origin (attribute transformer.value) this-syntax))]
      [{~var x (var-id sc)}
       (e+t this-syntax (attribute x.type))]
      [lit:system-f-literal
       (recur (datum->syntax this-syntax
                             (list (datum->syntax #'here 'system-f:#%datum) #'lit)
                             this-syntax))]
      [(_ . _)
       (recur (datum->syntax this-syntax
                             (cons (datum->syntax #'here 'system-f:#%app) this-syntax)
                             this-syntax))]
      [_
       (raise-invalid-thing-error "expression" this-syntax)]))

  (define (expand-type stx [sc #f])
    (define (recur stx) (expand-type stx sc))
    (syntax-parse stx
      #:literal-sets [core-type-literals]
      [{~var core (core-type sc)}
       (attribute core.value)]
      [{~or {~var transformer (type-id-transformer sc)}
            {~var transformer (type-transformer sc)}}
       (recur (macro-track-origin (attribute transformer.value) this-syntax))]
      [{~var x (type-var-id sc)}
       (e+t this-syntax (attribute x.kind))]
      [{~var x (type-constructor-id sc)}
       (e+t this-syntax (attribute x.kind))]
      [(head:#%type:app ~! t1:type t2:type)
       #:do [(match-define (e+t t1- k1) (recur #'t1))
             (define-values [k2 kr]
               (syntax-parse k1
                 #:literal-sets [core-type-literals]
                 #:literals [->]
                 [(#%type:app (#%type:app -> k2:type) kr:type)
                  (values #'k2 #'kr)]
                 [_
                  (raise-syntax-error
                   'system-f "cannot apply a type that is not a constructor" this-syntax #'t1 '()
                   (~a "\n  expected kind: ((-> k1) k2)\n  actual kind: " (type->string k1)))]))]
       (e+t (datum->syntax this-syntax
                           (list #'head t1- (e+t-e/t=! (recur #'t2) k2 sc #:src #'t2))
                           this-syntax
                           this-syntax)
            kr)]
      [(head:#%forall ~! [x:id : k:type] t:type)
       #:do [(define sc* (make-expression-scope sc))
             (define k- (e+t-e/t=! (recur #'k) #'Type sc #:src #'k))
             (define x- (scope-bind! sc* #'x (make-type-var k-)))
             (match-define (e+t t- t-k) (expand-type (in-scope sc* #'t) sc*))]
       (e+t (datum->syntax this-syntax
                           (list #'head (list x- ': k-) t-)
                           this-syntax
                           this-syntax)
            t-k)]
      [(_ . _)
       (recur (datum->syntax this-syntax
                             (cons (datum->syntax #'here '#%type:app) this-syntax)
                             this-syntax))]
      [_
       (raise-invalid-thing-error "type" this-syntax)]))

  (define (shift-phase phase shift)
    (and phase shift (+ phase shift)))

  (define (calculate-phase-shift new-phase orig-phase)
    (and new-phase orig-phase (- new-phase orig-phase)))

  (define-syntax-class require-#%binding
    #:description #f
    #:no-delimit-cut
    #:attributes [head external-id external-phase ns-key mod-path internal-id internal-phase]
    #:literal-sets [core-require-spec-literals]
    #:datum-literals [=>]
    [pattern (head:#%binding ~! external-id:id #:at external-phase:phase-level
                             #:from {~or ns-key:id #f} #:in mod-path:module-path
                             => internal-id:id #:at internal-phase:phase-level)])

  (define (expand-system-f-require-spec stx [sc #f])
    (define (recur stx) (expand-system-f-require-spec stx sc))
    (syntax-parse stx
      #:literal-sets [core-require-spec-literals]
      #:datum-literals [=>]
      [{~var core (core-require-spec sc)}
       (attribute core.value)]
      [{~var core (require-spec-transformer sc)}
       (recur (macro-track-origin (attribute core.value) this-syntax))]
      [mod-path:module-path
       #:and ~!
       #:do [(define nss (module-exported-namespaces (syntax->datum #'mod-path)))]
       (for*/list ([ns (in-list (cons #f (set->list nss)))]
                   [ns-mod-path (in-value (if ns
                                              (namespace-exports-submodule-path #'mod-path ns)
                                              #'mod-path))]
                   [exports (in-list (syntax-local-module-exports ns-mod-path))]
                   [phase (in-value (car exports))]
                   [external-sym (in-list (cdr exports))])
         (define internal-id (datum->syntax this-syntax external-sym this-syntax this-syntax))
         (define ns-internal-id (if ns (in-namespace ns internal-id) internal-id))
         (datum->syntax #f
                        (list (datum->syntax #'here '#%binding)
                              external-sym '#:at phase
                              '#:from (and ns (namespace-key ns)) '#:in #'mod-path
                              '=> ns-internal-id '#:at 0)))]
      [:require-#%binding
       (list (datum->syntax this-syntax
                            (list #'head #'external-id '#:at #'external-phase
                                  '#:from (attribute ns-key) '#:in #'mod-path
                                  '=> (syntax-local-identifier-as-binding #'internal-id)
                                  '#:at #'internal-phase)
                            this-syntax
                            this-syntax))]
      [(#%union ~! rs ...)
       (for*/list ([rs (in-list (attribute rs))]
                   [expanded-rs (in-list (recur rs))])
         (macro-track-origin expanded-rs this-syntax))]
      [_
       (raise-invalid-thing-error "require spec" this-syntax)]))

  (define (local-expand-system-f-require-spec stx [sc #f])
    (datum->syntax #f (cons (datum->syntax #'here '#%union) (expand-system-f-require-spec stx sc))))

  (define-syntax-class provide-#%binding
    #:description #f
    #:no-delimit-cut
    #:attributes [head internal-id external-id phase ns-key]
    #:literal-sets [core-provide-spec-literals]
    #:datum-literals [=>]
    [pattern (head:#%binding ~! internal-id:id => external-id:id
                             #:at phase:phase-level #:in {~or ns-key:id #f})])

  (define (expand-system-f-provide-spec stx [sc #f])
    (define (recur stx) (expand-system-f-provide-spec stx sc))
    (syntax-parse stx
      #:literal-sets [core-provide-spec-literals]
      #:datum-literals [=>]
      [{~var core (core-provide-spec sc)}
       (attribute core.value)]
      [{~var core (provide-spec-transformer sc)}
       (recur (macro-track-origin (attribute core.value) this-syntax))]
      [x:id
       (list (datum->syntax #f
                            (list (datum->syntax #'here '#%binding)
                                  #'x '=> #'x '#:at 0 '#:in (namespace-key namespace:value))))]
      [_:provide-#%binding
       (list this-syntax)]
      [(#%union ~! ps ...)
       (for*/list ([ps (in-list (attribute ps))]
                   [expanded-ps (in-list (recur ps))])
         (macro-track-origin expanded-ps this-syntax))]
      [_
       (raise-invalid-thing-error "provide spec" this-syntax)]))

  (define (local-expand-system-f-provide-spec stx [sc #f])
    (datum->syntax #f (cons (datum->syntax #'here '#%union) (expand-system-f-provide-spec stx sc)))))

;; ---------------------------------------------------------------------------------------------------
;; core decls

(define-syntax #%require
  (generics
   [core-decl-pass-2 values]
   [core-decl->racket-decl
    ; requires are lifted during expansion, so we don’t need to do anything with them here
    (lambda (stx internal-introduce) #'(begin))]))

(define-syntax #%provide
  (generics/parse
   (head ps ...)
   [(core-decl-pass-1 sc) this-syntax]
   [(core-decl-pass-2)
    #:do [(define expanded-pss (append-map expand-system-f-provide-spec (attribute ps)))]
    (datum->syntax this-syntax
                   (cons #'head expanded-pss)
                   this-syntax
                   this-syntax)]
   [(core-decl->racket-decl internal-introduce)
    #`(begin #,@(map system-f-provide-spec->racket-decl (attribute ps)))]))

(define-syntax #%define
  (generics/parse
   #:datum-literals [:]
   (head x:id : t:type e:expr)
   [(core-decl-pass-1 sc)
    #:do [(define t- (e+t-e/t=! (expand-type (in-type-namespace #'t)) #'Type #:src #'t))
          (define x- (scope-bind! sc #'x (make-local-var t-)))]
    (datum->syntax this-syntax
                   (list #'head x- ': t- #'e)
                   this-syntax
                   this-syntax)]
   [(core-decl-pass-2)
    #:do [(define e- (e+t-e/t=! (expand-expr #'e) #'t #:src #'e))]
    (datum->syntax this-syntax
                   (list #'head #'x ': #'t e-)
                   this-syntax
                   this-syntax)]
   [(core-decl->racket-decl internal-introduce)
    #:with internal-x (internal-introduce #'x)
    #`(begin
        (define internal-x #,(~> (extract-racket-expr (internal-introduce #'e))
                                 (syntax-track-residual (system-f-type->residual #'t))))
        (define-syntax x (make-module-var (quote-syntax/launder t)
                                          (quote-syntax/launder internal-x))))]))

(define-syntax #%define-syntax
  (generics/parse
   (head x:id e)
   [(core-decl-pass-1 sc)
    #:with e- (local-transformer-expand #'e 'expression '() (list (scope-defctx sc)))
    #:with x- (scope-bind! sc #'x #'e-)
    (datum->syntax this-syntax
                   (list #'head #'x- #'e-)
                   this-syntax
                   this-syntax)]
   [(core-decl-pass-2) this-syntax]
   [(core-decl->racket-decl internal-introduce)
    #`(define-syntax x #,(suspend-expression #'e))]))

(define-syntax #%define-main
  (generics/parse
   (_ e:expr)
   [(core-decl-pass-1 sc) this-syntax]
   [(core-decl->racket-decl internal-introduce)
    #`(module* main #f
        (#%plain-module-begin
         #,(extract-racket-expr (internal-introduce #'e))))]))

(define-syntax #%begin (generics))

(define-syntax #%begin-for-syntax
  (generics/parse
   #:literals [#%plain-module-begin begin-for-syntax]
   (head d ...)
   [(core-decl-pass-1 sc)
    #:with (#%plain-module-begin (begin-for-syntax d- ...))
    (local-expand #'(#%plain-module-begin (begin-for-syntax d ...)) 'module-begin '())
    (datum->syntax this-syntax
                   (cons #'head (attribute d-))
                   this-syntax
                   this-syntax)]
   [(core-decl-pass-2) this-syntax]
   [(core-decl->racket-decl internal-introduce)
    #`(begin-for-syntax #,@(map suspend-racket-decl (attribute d)))]))

;; ---------------------------------------------------------------------------------------------------
;; core exprs

(define-syntax system-f:#%datum
  (generics/parse
   (_ lit:system-f-literal)
   [(core-expr)
    (e+t this-syntax (match (syntax-e #'lit)
                       [(? exact-integer?) #'Integer]
                       [(? string?) #'String]))]
   [(core-expr->racket-expr)
    #'(quote lit)]))

(define-syntax system-f:#%app
  (generics/parse
   (head f:expr e:expr)
   [(core-expr)
    ; TODO: share code with type application and kindchecking type ctor application
    #:do [(match-define (e+t f- f-t) (expand-expr #'f))
          (define-values [e-t r-t]
            (syntax-parse f-t
              #:literal-sets [core-type-literals]
              #:literals [->]
              [(#%type:app (#%type:app -> e-t:type) r-t:type)
               (values #'e-t #'r-t)]
              [_
               (raise-syntax-error
                'system-f "cannot apply a value that is not a function" this-syntax #'f '()
                (~a "\n  expected type: ((-> t1) t2)\n  actual type: " (type->string f-t)))]))]
    (e+t (datum->syntax this-syntax
                        (list #'head f- (e+t-e/t=! (expand-expr #'e) e-t #:src #'e))
                        this-syntax
                        this-syntax)
         r-t)]
   [(core-expr->racket-expr)
    #`(#%plain-app #,(extract-racket-expr #'f) #,(extract-racket-expr #'e))]))

(define-syntax #%lambda
  (generics/parse
   (head [x:id : t:type] e:expr)
   [(core-expr)
    #:do [(define t- (e+t-e/t=! (expand-type (in-type-namespace #'t)) #'Type #:src #'t))
          (define sc* (make-expression-scope))
          (define x- (scope-bind! sc* #'x (make-local-var t-)))
          (match-define (e+t e- e-t) (expand-expr (in-scope sc* #'e) sc*))]
    (e+t (datum->syntax this-syntax
                        (list #'head (list x- ': t-) e-)
                        this-syntax
                        this-syntax)
         #`(#%type:app (#%type:app -> #,t-) #,e-t))]
   [(core-expr->racket-expr)
    (~> #`(#%plain-lambda [x] #,(extract-racket-expr #'e))
        (syntax-track-residual (system-f-type->residual #'t)))]))

(define-syntax #%App
  (generics/parse
   (head e:expr t:type)
   [(core-expr)
    #:do [(match-define (e+t e- e-t) (expand-expr #'e))
          (define-values [x x-k unquantified-t]
            (syntax-parse e-t
              #:literal-sets [core-type-literals]
              #:literals [->]
              [(#%forall ~! [x:id : x-k:type] unquantified-t:type)
               (values #'x #'x-k #'unquantified-t)]
              [_
               (raise-syntax-error
                'system-f "cannot apply a value with a monomorphic type to a type"
                this-syntax #'e '()
                (~a "\n  expected type: (forall [x : k] t)\n  actual type: "
                    (type->string e-t)))]))
          (define t- (e+t-e/t=! (expand-type (in-type-namespace #'t)) x-k #:src #'t))
          (define sc* (make-expression-scope))
          (scope-bind! sc* x (generics [type-id-transformer (make-substituting-transformer t-)]))
          (define instantiated-t (e+t-e (expand-type (in-scope sc* unquantified-t) sc*)))]
    (e+t (datum->syntax this-syntax
                        (list #'head e- t-)
                        this-syntax
                        this-syntax)
         instantiated-t)]
   [(core-expr->racket-expr)
    (~> (extract-racket-expr #'e)
        (syntax-track-residual (system-f-type->residual #'t)))]))

(define-syntax #%Lambda
  (generics/parse
   (head [x:id : k:type] e:expr)
   [(core-expr)
    #:do [(define k- (e+t-e/t=! (expand-type (in-type-namespace #'k)) #'Type #:src #'k))
          (define sc* (make-expression-scope))
          (define x- (scope-bind! sc* (in-type-namespace #'x) (make-type-var k-)))
          (match-define (e+t e- e-t) (expand-expr (in-scope sc* #'e) sc*))]
    (e+t (datum->syntax this-syntax
                        (list #'head (list x- ': k-) e-)
                        this-syntax
                        this-syntax)
         #`(#%forall [#,x- : #,k-] #,e-t))]
   [(core-expr->racket-expr)
    (~> (extract-racket-expr #'e)
        (syntax-track-residual (make-residual (list (system-f-type->residual #'k))
                                              #:bindings (list #'x))))]))

;; ---------------------------------------------------------------------------------------------------

(define-syntax system-f:shift
  (generics
   [require-spec-transformer
    (syntax-parser
      #:literal-sets [core-require-spec-literals]
      [(_ phase-stx:phase-level rs ...)
       #:do [(define phase (syntax-e #'phase-stx))]
       #:with (#%union b ...) (local-expand-system-f-require-spec #`(#%union rs ...))
       #`(#%union #,@(for/list ([b-stx (in-list (attribute b))])
                       (define/syntax-parse b:require-#%binding b-stx)
                       (datum->syntax b-stx
                                      (list #'b.head #'b.external-id '#:at #'b.external-phase
                                            '#:from (attribute b.ns-key) '#:in #'b.mod-path
                                            '=> #'b.internal-id
                                            '#:at (shift-phase (syntax-e #'b.internal-phase) phase))
                                      b-stx
                                      b-stx)))])]
   [provide-spec-transformer
    (syntax-parser
      #:literal-sets [core-provide-spec-literals]
      [(_ phase-stx:phase-level ps ...)
       #:do [(define phase (syntax-e #'phase-stx))]
       #:with [(#%union b ...)] (local-expand-system-f-provide-spec #`(#%union ps ...))
       #`(#%union #,@(for/list ([b-stx (in-list (attribute b))])
                       (define/syntax-parse b:provide-#%binding b-stx)
                       (datum->syntax b-stx
                                      (list #'b.head #'b.internal-id '=> #'b.external-id
                                            '#:at (shift-phase (syntax-e #'b.phase) phase)
                                            '#:in (attribute b.ns-key))
                                      b-stx
                                      b-stx)))])]))

;; ---------------------------------------------------------------------------------------------------
;; extraction

; Once a module has been expanded to the System F core language, it needs to be translated into the
; corresponding Racket code that can actually be executed. We call this process “extraction” — a
; Racket program is “extracted” from the System F one. For the most part, this translation is
; direct — System F declarations are mapped to Racket definitions, System F expressions are mapped to
; Racket expressions, etc. — but there are some subtleties involved along the way.
;
; One such subtlety is the handling of typed bindings. System F types are erased, so the extracted
; Racket program does not include types, but what about provided bindings? If one System F module
; imports another, then it needs to know the type of each binding in order to ensure its use is
; well-typed. Therefore, each System F `#%define` is actually translated into two Racket definitions:
; one using `define` and another using `define-syntax`. The `define` binding is bound to the actual
; extracted Racket expression, while the `define-syntax` binding is bound to a `module-var` that
; references the `define` binding.
;
; The main subtlety in the above approach is ensuring the right bindings are referenced in the right
; places. Extracted expressions should refer to the `define` binding, since they are already
; typechecked and ought to refer to the ordinary Racket variable, but references inside `#%provide`
; declarations ought to refer to the `define-syntax` binding so that importing modules can access the
; type information. The solution is to use the same identifier for both bindings, but to add a fresh
; scope to the `define` bindings to make them distinct. The same scope is added to the extracted
; right-hand side of each `#%define` declaration, but nowhere else, which redirects exactly the
; appropriate references.

(begin-for-syntax
  (define (extract-racket-decl stx internal-introduce)
    (macro-track-origin (core-decl->racket-decl stx internal-introduce) stx))

  (define (extract-racket-expr stx)
    (macro-track-origin
     (syntax-parse stx
       [x:module-var-id
        (attribute x.racket-id)]
       [_:id
        this-syntax]
       [_
        (core-expr->racket-expr stx)])
     stx))

  (define system-f-type->residual
    (syntax-parser
      #:literal-sets [core-type-literals]
      #:datum-literals [:]
      [_:id
       (make-residual #:origin this-syntax)]
      [(#%type:app ~! t1:type t2:type)
       (make-residual (list (system-f-type->residual #'t1)
                            (system-f-type->residual #'t2))
                      #:origin this-syntax)]
      [(#%forall ~! [x:id : k:type] t:type)
       (make-residual (list (system-f-type->residual #'k)
                            (system-f-type->residual #'t))
                      #:origin this-syntax
                      #:bindings (list #'x))]
      [_
       (raise-syntax-error
        'system-f
        "internal error: unexpected type form found during extraction to racket"
        this-syntax)]))

  (define (system-f-require-spec->racket-require-spec stx)
    (macro-track-origin
     (syntax-parse stx
       [:require-#%binding
        #:with adjusted-mod-path (if (attribute ns-key)
                                     (let ([ns (make-namespace (syntax-e #'ns-key))])
                                       (namespace-exports-submodule-path #'mod-path ns))
                                     #'mod-path)
        #:with phase-shift (calculate-phase-shift (syntax-e #'internal-phase)
                                                  (syntax-e #'external-phase))
        #:with rename-spec #'(rename adjusted-mod-path internal-id external-id)
        #`(just-meta external-phase #,(if (zero? (syntax-e #'phase-shift))
                                          #'rename-spec
                                          #'(for-meta phase-shift rename-spec)))]
       [_
        (raise-syntax-error
         'system-f
         "internal error: unexpected require spec found during extraction to racket"
         this-syntax)])
     stx))

  (define (system-f-provide-spec->racket-decl stx)
    (macro-track-origin
     (syntax-parse stx
       [:provide-#%binding
        #:do [(define ns (and (attribute ns-key) (make-namespace (syntax-e #'ns-key))))]
        #:with racket-spec #'(for-meta phase (rename-out [internal-id external-id]))
        (if (attribute ns-key)
            #'(provide/namespace (make-namespace 'ns-key) racket-spec)
            #'(provide racket-spec))]
       [_
        (raise-syntax-error
         'system-f
         "internal error: unexpected provide spec found during extraction to racket"
         this-syntax)])
     stx))

  (define system-f-debug-print-decl?
    (syntax-parser
      #:literals [#%require #%define-syntax #%begin-for-syntax]
      [({~or #%require #%define-syntax #%begin-for-syntax} ~! . _) #f]
      [_ #t])))

(define-syntax system-f:#%module-begin
  (make-namespaced-module-begin #'do-module-begin namespace:value))

(define-syntax-parser do-module-begin
  [(_ decl ...)
   #:with [expanded-decl ...] (expand-module (attribute decl))
   #:do [(println (syntax-local-introduce
                   #`(#%module-begin
                      #,@(filter system-f-debug-print-decl? (attribute expanded-decl)))))]
   #:do [(define internal-introducer (make-syntax-introducer #t))
         (define (internal-introduce stx)
           (introduce-everywhere stx (lambda (stx) (internal-introducer stx 'add))))
         (define suspenders (make-suspenders))]
   #:with [racket-decl ...] (parameterize ([current-suspenders suspenders])
                              (for/list ([expanded-decl (in-list (attribute expanded-decl))])
                                (extract-racket-decl expanded-decl internal-introduce)))
   ; Add an extra scope to everything to “freshen” binders. The expander complains if an identifier
   ; bound by a module-level binding form has *exactly* the same scopes as an existing binding, since
   ; the new binding would conflict with the old one. By adding a new scope to everything, the
   ; bindings remain distinct. As a wrinkle, we also need to add the scope inside syntax properties
   ; used by Check Syntax, since otherwise the binding structure of the program will be inconsistent
   ; with the information contained in the properties.
   #:do [(define finalizer-introducer (make-syntax-introducer #t))]
   #:with [introduced-decl ...] (for/list ([racket-decl (in-list (attribute racket-decl))])
                                  (introduce-everywhere
                                   racket-decl
                                   (lambda (stx) (finalizer-introducer stx 'add))))
   #`(begin
       #,(suspenders->racket-decl suspenders)
       introduced-decl ...)])

;; ---------------------------------------------------------------------------------------------------

(define-syntax Type (make-type-var #'Type))
(define-syntax -> (make-type-var
                   #'(#%type:app (#%type:app -> Type) (#%type:app (#%type:app -> Type) Type))))
(define-syntax Integer (make-type-var #'Type))
(define-syntax String (make-type-var #'Type))
(define-syntax Unit (make-type-var #'Type))

(define-syntax-parser define-system-f-primitive
  [(_ x:id : t:type racket-id:id)
   #'(define-syntax x
       (make-module-var
        (e+t-e/t=! (expand-type #'t #f) #'Type #:src (quote-syntax t))
        #'racket-id))])

(define ((curried-+ a) b) (+ a b))
(define-system-f-primitive sysf:+ : ((-> Integer) ((-> Integer) Integer)) curried-+)
(define unit (void))
(define-system-f-primitive sysf:unit : Unit unit)
(define-system-f-primitive sysf:println : (#%forall [a : Type] ((-> a) Unit)) println)
