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
                     "private/util/stx.rkt")
         (for-syntax racket/base
                     racket/contract
                     racket/format
                     racket/list
                     racket/match
                     racket/set
                     racket/syntax
                     syntax/id-table
                     syntax/modcollapse
                     syntax/parse/class/local-value
                     syntax/parse/define
                     syntax/transformer
                     syntax-generic2
                     threading
                     "private/util/stx.rkt")
         syntax/parse/define
         "private/namespace.rkt")

(provide (rename-out [#%system-f:module-begin #%module-begin]))

(define-namespace value #:unique)
(define-namespace type #:unique)

(provide/namespace namespace:value
                   (rename-out [#%define define]
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

; Due to the way the namespacing system works, `#%module-begin` needs access to the module language in
; order to inject the appropriate `require`s to the relevant namespace submodules. Fortunately, this
; can be done fairly generically with a sufficiently careful `#lang` reader; unfortunately, this is
; surprisingly awkward to do with syntax/module-reader. The following reader does the necessary work
; to read an ordinary s-expression module while also providing the module language to the injected
; `#%module-begin`.

(module reader racket/base
  (require racket/path
           racket/sequence)

  (provide (rename-out [system-f:read read]
                       [system-f:read-syntax read-syntax])
           get-info)

  (define (system-f:read in)
    (raise-arguments-error 'system-f "cannot be used in ‘read’ mode"))

  (define (system-f:read-syntax src-name in reader-mod-path line col pos)
    (define stxs
      (parameterize ([read-accept-lang #f])
        (sequence->list (in-producer (lambda () (read-syntax src-name in)) eof-object?))))
    (define name (or (and (path? src-name)
                          (let ([filename (file-name-from-path src-name)])
                            (and filename (string->symbol
                                           (path->string (path-replace-extension filename #""))))))
                     'anonymous-module))
    (define lang-mod-path (datum->syntax #f 'mini-ml/system-f reader-mod-path reader-mod-path))
    (datum->syntax #f
                   (list (datum->syntax #f 'module)
                         (datum->syntax #f name)
                         lang-mod-path
                         (list* (datum->syntax #f '#%module-begin) lang-mod-path stxs))
                   (vector src-name line col pos
                           (and pos (let-values ([(l c p) (port-next-location in)])
                                      (and p (- p pos)))))))

  (define (get-info in mod-path line col pos)
    (lambda (key default)
      (case key
        [(module-language) 'mini-ml/system-f]
        [else default]))))

;; ---------------------------------------------------------------------------------------------------
;; require scopes

(begin-for-syntax
  (define scopeless-stx (datum->syntax #f #f))
  (struct require-scope (introducer))
  (define (make-require-scope! mod-path
                               #:flip-scopes? [flip-scopes? #t]
                               #:origin [origin #f])
    (define flipped-path (if flip-scopes? (syntax-local-introduce mod-path) mod-path))
    (define tracked-path (if origin
                             (macro-track-origin flipped-path origin)
                             flipped-path))
    (define scoped-stx (syntax-local-lift-require tracked-path scopeless-stx))
    (require-scope (make-syntax-delta-introducer scoped-stx scopeless-stx)))
  (define (require-scope-introduce rsc stx [mode 'flip])
    ((require-scope-introducer rsc) stx mode)))

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
  (decl [#%define #%define-syntax #%define-type #%define-main #%begin #%begin-for-syntax])
  (expr [#%system-f:datum #%lambda #%system-f:app #%Lambda #%App #%case])
  (type [#%type:app #%forall]))

;; ---------------------------------------------------------------------------------------------------
;; `define-syntax-info`

; Sometimes, it’s really useful to just attach some compile-time metadata to an identifier directly
; without having to deal with the dispatch machinery of syntax generics. `define-syntax-info` is a
; macro to make that simple: it defines both a struct and a syntax class for matching against
; identifiers bound to instances of the struct.

(begin-for-syntax
  (define-simple-macro (define-syntax-info name:id [field:id ...]
                         {~alt {~optional {~seq #:name err-name:expr}
                                          #:defaults ([err-name #`'#,(symbol->string
                                                                      (syntax-e #'name))])}
                               {~seq #:property prop:expr prop-val:expr}}
                         ...)
    #:with name-id (derived-id "" #'name "-id")
    #:with name? (format-id #'name "~a?" #'name)
    #:with [field-tmp ...] (generate-temporaries (attribute field))
    (begin
      (struct name [field ...]
        {~@ #:property prop prop-val} ...)
      (define-syntax-class (name-id [sc #f])
        #:description #f
        #:commit
        #:attributes [value field ...]
        [pattern {~var x (local-value name? (and sc (scope-defctx sc)) #:name err-name)}
                 #:attr value (attribute x.local-value)
                 #:do [(match-define (struct name [field-tmp ...]) (attribute value))]
                 {~@ #:attr field field-tmp} ...])))

  ; Variables, type variables, and type constructors are really just special bindings with a type or
  ; kind attached. Primitives are variables that are actually bound to something when extraction to
  ; Racket happens, instead of being locally-bound.
  (define-syntax-info var (type) #:name "variable")
  (define-syntax-info type-var (kind) #:name "type variable")
  (define-syntax-info type-constructor (kind) #:name "type constructor")

  (struct primitive var (racket-id)
    #:property prop:procedure
    (lambda (v stx)
      ((set!-transformer-procedure (make-variable-like-transformer (primitive-racket-id v))) stx))))

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

  (define/contract (type=! actual-t expected-t #:src src-stx)
    (-> syntax? syntax? #:src syntax? void?)
    (let loop ([actual-t actual-t]
               [expected-t expected-t]
               [ctx (make-immutable-free-id-table)])
      (syntax-parse (list actual-t expected-t)
        #:context 'type=!
        #:literal-sets [core-type-literals]
        #:datum-literals [:]
        [[actual-x:type-var-id expected-x:type-var-id]
         #:when (free-identifier=? #'actual-x #'expected-x)
         (void)]
        [[actual-x:type-constructor-id expected-x:type-constructor-id]
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
  (define (system-f-fallback thing)
    (define msg (string-append "not a valid " thing))
    (lambda (stx) (raise-syntax-error 'system-f msg stx)))

  (define-syntax-generic system-f-decl (system-f-fallback "declaration"))
  (define-syntax-generic system-f-expr (system-f-fallback "expression"))
  (define-syntax-generic system-f-type (system-f-fallback "type"))

  ; `make-variable-like-transformer` is an awkward way to solve a common problem: wanting a macro that
  ; only ever expands as a single identifier, not at the head of a list. Let’s try just baking that
  ; in, instead.
  (define-values [prop:id-only? id-only?? id-only?-ref] (make-struct-type-property 'id-only?))
  (define-syntax-class (id-only [sc #f])
    #:description #f
    #:commit
    #:attributes []
    [pattern {~var x (local-value id-only?? (scope-defctx sc))}
             #:do [(define id-only? (id-only?-ref (attribute x.local-value)))]
             #:when (if (procedure? id-only?)
                        (id-only? (attribute x.local-value))
                        id-only?)])
  (define (id-only? stx [sc #f])
    (syntax-parse stx
      [_:id-only #t]
      [(_:id-only . _) #t]
      [_ #f]))

  ; The common case of `prop:id-only?` is to implement a transformer like
  ; `make-variable-like-transformer`, which just expands to a particular piece of syntax, but it needs
  ; to do just a little bit extra in order to make the source locations nice. This implements that.
  (define (make-substituting-transformer replacement-stx)
    (define replacement-datum (syntax-e replacement-stx))
    (lambda (id-stx) (datum->syntax replacement-stx replacement-datum id-stx replacement-stx)))

  (struct e+t (e t) #:transparent)

  (define (e+t-e/t=! v t #:src src-stx)
    (type=! (e+t-t v) t #:src src-stx)
    (e+t-e v))

  (define (expand-module stxs)
    (define sc (make-definition-scope))

    (define (do-initial-defs+requires-pass stxs)
      (let loop ([stxs-to-go (map (lambda (stx) (in-scope sc stx)) stxs)]
                 [stxs-deferred '()])
        (match stxs-to-go
          ['()
           (reverse stxs-deferred)]
          [(cons stx stxs-to-go*)
           (syntax-parse stx
             #:literal-sets [core-decl-literals]
             #:datum-literals [:]
             [(head:#%define ~! x:id : {~type t:type} e:expr)
              #:do [(define t- (e+t-e/t=! (expand-type #'t #f) #'Type #:src #'t))
                    (define x- (scope-bind! sc #'x (var t-)))]
              (loop stxs-to-go* (cons (datum->syntax this-syntax
                                                     (list #'head x- ': t- #'e)
                                                     this-syntax
                                                     this-syntax)
                                      stxs-deferred))]
             [(head:#%define-syntax ~! x:id e)
              #:with e- (local-transformer-expand
                         #`(let ([transformer e])
                             (generics [dml-decl transformer]
                                       [dml-expr transformer]))
                         'expression
                         '()
                         (list (scope-defctx sc)))
              #:with x- (scope-bind! sc #'x #'e-)
              (loop stxs-to-go* (cons (datum->syntax this-syntax
                                                     (list #'head #'x- #'e-)
                                                     this-syntax
                                                     this-syntax)
                                      stxs-deferred))]
             [(head:#%begin ~! d ...)
              (loop (append (for/list ([d (in-list (attribute d))])
                              (macro-track-origin d this-syntax))
                            stxs-to-go*)
                    stxs-deferred)]
             [({~or #%define-type #%begin-for-syntax}
               ~! . _)
              (error "not yet implemented")]
             [({~or #;#%provide #%define-main} ~! . _)
              (loop stxs-to-go* (cons this-syntax stxs-deferred))]
             [_
              (loop (cons (macro-track-origin (apply-as-transformer system-f-decl sc this-syntax)
                                              this-syntax)
                          stxs-to-go*)
                    stxs-deferred)])])))

    (define (do-expand-exprs stxs)
      (define-values [expanded-decls main-decls]
        (for/fold ([expanded-decls '()]
                   [main-decls '()])
                  ([stx (in-list stxs)])
          (syntax-parse stx
            #:literal-sets [core-decl-literals]
            #:datum-literals [:]
            [(head:#%define ~! x:id : t:type e:expr)
             #:do [(define e- (e+t-e/t=! (expand-expr #'e sc) #'t #:src #'e))]
             (values (cons (datum->syntax this-syntax
                                          (list #'head #'x ': #'t e-)
                                          this-syntax
                                          this-syntax)
                           expanded-decls)
                     main-decls)]
            [(#%define-syntax ~! _:id _)
             (values (cons this-syntax expanded-decls) main-decls)]
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

    (do-expand-exprs (do-initial-defs+requires-pass stxs)))

  (define-syntax-class system-f-literal
    #:description #f
    #:commit
    #:attributes []
    [pattern _:exact-integer]
    [pattern _:string])

  (define (expand-expr stx sc)
    (define (recur stx) (expand-expr stx sc))
    (syntax-parse stx
      #:literal-sets [core-expr-literals]
      #:datum-literals [:]
      [{~var x (var-id sc)}
       (e+t this-syntax (attribute x.type))]
      [(#%system-f:datum ~! lit:system-f-literal)
       (e+t this-syntax (match (syntax-e #'lit)
                          [(? exact-integer?) #'Integer]
                          [(? string?) #'String]))]
      [lit:system-f-literal
       (recur (datum->syntax this-syntax
                             (list (datum->syntax #'here '#%system-f:datum) #'lit)
                             this-syntax))]
      [(head:#%system-f:app ~! f:expr e:expr)
       ; TODO: share code with type application and kindchecking type ctor application
       #:do [(match-define (e+t f- f-t) (recur #'f))
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
                           (list #'head f- (e+t-e/t=! (recur #'e) e-t #:src #'e))
                           this-syntax
                           this-syntax)
            r-t)]
      [(head:#%lambda ~! [x:id : {~type t:type}] e:expr)
       #:do [(define sc* (make-expression-scope sc))
             (define t- (e+t-e/t=! (expand-type #'t sc) #'Type #:src #'t))
             (define x- (scope-bind! sc* #'x (var t-)))
             (match-define (e+t e- e-t) (expand-expr (in-scope sc* #'e) sc*))]
       (e+t (datum->syntax this-syntax
                           (list #'head (list x- ': t-) e-)
                           this-syntax
                           this-syntax)
            #`(#%type:app (#%type:app -> #,t-) #,e-t))]
      [(head:#%App ~! e:expr {~type t:expr})
       #:do [(match-define (e+t e- e-t) (recur #'e))
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
             (define t- (e+t-e/t=! (expand-type #'t sc) x-k #:src #'t))
             (define sc* (make-expression-scope sc))
             (scope-bind! sc* x (generics #:property prop:id-only? #t
                                          [system-f-type (make-substituting-transformer t-)]))
             (define instantiated-t (e+t-e (expand-type (in-scope sc* unquantified-t) sc*)))]
       (e+t (datum->syntax this-syntax
                           (list #'head e- t-)
                           this-syntax
                           this-syntax)
            instantiated-t)]
      [(head:#%Lambda ~! [{~type x:id} : {~type k:type}] e:expr)
       #:do [(define sc* (make-expression-scope sc))
             (define k- (e+t-e/t=! (expand-type #'k sc) #'Type #:src #'k))
             (define x- (scope-bind! sc* #'x (type-var k-)))
             (match-define (e+t e- e-t) (expand-expr (in-scope sc* #'e) sc*))]
       (e+t (datum->syntax this-syntax
                           (list #'head (list x- ': k-) e-)
                           this-syntax
                           this-syntax)
            #`(#%forall [#,x- : #,k-] #,e-t))]
      [(#%case ~! . _)
       (error "not implemented yet")]
      [(_ . _)
       #:when (or (not (system-f-expr? this-syntax sc))
                  (id-only? this-syntax sc))
       (recur (datum->syntax this-syntax
                             (cons (datum->syntax #'here '#%system-f:app) this-syntax)
                             this-syntax))]
      [_
       (recur (macro-track-origin (apply-as-transformer system-f-expr sc this-syntax) this-syntax))]))

  (define (expand-type stx sc)
    (define (recur stx) (expand-type stx sc))
    (syntax-parse stx
      #:literal-sets [core-type-literals]
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
                           (list #'head t1- (e+t-e/t=! (recur #'t2) k2 #:src #'t2))
                           this-syntax
                           this-syntax)
            kr)]
      [(head:#%forall ~! [x:id : k:type] t:type)
       #:do [(define sc* (make-expression-scope sc))
             (define k- (e+t-e/t=! (recur #'k) #'Type #:src #'k))
             (define x- (scope-bind! sc* #'x (type-var k-)))
             (match-define (e+t t- t-k) (expand-type (in-scope sc* #'t) sc*))]
       (e+t (datum->syntax this-syntax
                           (list #'head (list x- ': k-) t-)
                           this-syntax
                           this-syntax)
            t-k)]
      [(_ . _)
       #:when (or (not (system-f-type? this-syntax sc))
                  (id-only? this-syntax sc))
       (recur (datum->syntax this-syntax
                             (cons (datum->syntax #'here '#%type:app) this-syntax)
                             this-syntax))]
      [_
       (recur (macro-track-origin (apply-as-transformer system-f-type sc this-syntax)
                                  this-syntax))])))

;; ---------------------------------------------------------------------------------------------------
;; extraction

(begin-for-syntax
  (define current-is-reexpanding?-id (make-parameter #f))

  (define (system-f-decl->racket-decl stx)
    (macro-track-origin
     (syntax-parse stx
       #:literal-sets [core-decl-literals]
       #:datum-literals [:]
       [(#%define ~! x:id : t:type e:expr)
        #`(begin
            (define-values []
              (begin (lambda () #,(system-f-type->residual-racket-expr #'t)) (values)))
            (define x #,(system-f-expr->racket-expr #'e)))]
       [(#%define-syntax ~! x:id e)
        #`(define-syntax x (if #,(current-is-reexpanding?-id) #f e))]
       [(#%define-main ~! e:expr)
        #`(module* main #f
            (#%plain-module-begin
             #,(system-f-expr->racket-expr #'e)))]
       [_
        (raise-syntax-error
         'system-f
         "internal error: unexpected declaration form found during extraction to racket"
         this-syntax)])
     stx))

  (define (system-f-expr->racket-expr stx)
    (macro-track-origin
     (syntax-parse stx
       #:literal-sets [core-expr-literals]
       #:datum-literals [:]
       [_:id
        this-syntax]
       [(#%system-f:datum ~! lit:system-f-literal)
        #'(#%datum . lit)]
       [(#%system-f:app ~! f:expr e:expr)
        #`(#%plain-app #,(system-f-expr->racket-expr #'f) #,(system-f-expr->racket-expr #'e))]
       [(#%lambda ~! [x:id : t:type] e:expr)
        #`(let-values ([() (begin (lambda () #,(system-f-type->residual-racket-expr #'t)) (values))])
            (#%plain-lambda [x] #,(system-f-expr->racket-expr #'e)))]
       [(#%App ~! e:expr t:type)
        #`(let-values ([() (begin (lambda () #,(system-f-type->residual-racket-expr #'t)) (values))])
            #,(system-f-expr->racket-expr #'e))]
       [(#%Lambda ~! [x:id : k:type] e:expr)
        (~> #`(let-values ([() (begin (lambda () #,(system-f-type->residual-racket-expr #'k))
                                      (values))])
                #,(system-f-expr->racket-expr #'e))
            (syntax-property 'disappeared-binding (syntax-local-introduce #'x)))]
       [_
        (raise-syntax-error
         'system-f
         "internal error: unexpected expression form found during extraction to racket"
         this-syntax)])
     stx))

  (define (system-f-type->residual-racket-expr stx)
    (macro-track-origin
     (syntax-parse stx
       #:literal-sets [core-type-literals]
       #:datum-literals [:]
       [x:id
        #''x]
       [(#%type:app ~! t1:type t2:type)
        #`(#%plain-app #,(system-f-type->residual-racket-expr #'t1)
                       #,(system-f-type->residual-racket-expr #'t2))]
       [(#%forall ~! [x:id : k:type] t:type)
        #`(#%plain-lambda [x]
                          #,(system-f-type->residual-racket-expr #'k)
                          #,(system-f-type->residual-racket-expr #'t))])
     stx))

  (define system-f-syntax-decl?
    (syntax-parser
      #:literal-sets [core-decl-literals]
      [(#%define-syntax ~! _:id _) #t]
      [(#%begin-for-syntax ~! _ ...) #t]
      [_ #f])))

; Defer to a secondary #%module-begin form to establish a lift target for requires (lifts are not
; legal in a 'module-begin context).
(define-syntax-parser #%system-f:module-begin
  [(_ decl ...)
   #'(#%plain-module-begin (#%system-f:inner-module-begin decl ...))])

(define-syntax-parser #%system-f:inner-module-begin
  [(_ lang-mod-path-stx decl ...)
   #:do [(define lang-mod-path (syntax->datum #'lang-mod-path-stx))
         (define lang-nss (module-exported-namespaces lang-mod-path))
         (define ns-rscs (for/list ([ns (in-set lang-nss)])
                           (make-require-scope!
                            (datum->syntax (in-namespace ns #'lang-mod-path-stx)
                                           (collapse-module-path
                                            `(submod "." ,(namespace-exports-submodule-name ns))
                                            lang-mod-path)
                                           #'lang-mod-path-stx
                                           #'lang-mod-path-stx))))]
   #:with [namespaced-decl ...] (for/fold ([decls (in-value-namespace #'[decl ...])])
                                          ([ns-rsc (in-list ns-rscs)])
                                  (require-scope-introduce ns-rsc decls 'add))
   #:with [expanded-decl ...] (expand-module (attribute namespaced-decl))
   #:do [(println (syntax-local-introduce
                   #`(#%system-f:module-begin
                      #,@(filter-not system-f-syntax-decl? (attribute expanded-decl)))))]
   #:with is-reexpanding?-id (generate-temporary 'is-reexpanding?)
   #:with [racket-decl ...] (parameterize ([current-is-reexpanding?-id #'is-reexpanding?-id])
                              (map system-f-decl->racket-decl (attribute expanded-decl)))
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
   #'(begin
       (define-for-syntax is-reexpanding?-id #f)
       (let-syntax ([_ (set! is-reexpanding?-id #t)])
         (void))
       introduced-decl ...)])

;; ---------------------------------------------------------------------------------------------------

(define-syntax Type (type-constructor #'Type))
(define-syntax -> (type-constructor
                   #'(#%type:app (#%type:app -> Type) (#%type:app (#%type:app -> Type) Type))))
(define-syntax Integer (type-constructor #'Type))
(define-syntax String (type-constructor #'Type))
(define-syntax Unit (type-constructor #'Type))

(define-syntax-parser define-system-f-primitive
  [(_ x:id : t:type racket-id:id)
   #'(define-syntax x
       (primitive
        (e+t-e/t=! (expand-type #'t #f) #'Type #:src (quote-syntax t))
        #'racket-id))])

(define ((curried-+ a) b) (+ a b))
(define-system-f-primitive sysf:+ : ((-> Integer) ((-> Integer) Integer)) curried-+)
(define unit (void))
(define-system-f-primitive sysf:unit : Unit unit)
(define-system-f-primitive sysf:println : (#%forall [a : Type] ((-> a) Unit)) println)
