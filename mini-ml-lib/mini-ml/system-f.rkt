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

(provide (rename-out [#%system-f:module-begin #%module-begin]))

(define-namespace value #:unique)
(define-namespace type #:unique)

(provide/namespace namespace:value
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
  (decl [#%require #%provide #%define #%define-syntax #%define-type #%define-main #%begin
                   #%begin-for-syntax])
  (expr [#%system-f:datum #%lambda #%system-f:app #%Lambda #%App #%case])
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
  (define (system-f-fallback thing)
    (define msg (string-append "not a valid " thing))
    (lambda (stx) (raise-syntax-error 'system-f msg stx)))

  (define pair-only
    (syntax-parser
      [(x:id . _) #'x]
      [_ #f]))

  (define-syntax-generic system-f-decl (system-f-fallback "declaration"))
  (define-syntax-generic system-f-expr (system-f-fallback "expression"))
  (define-syntax-generic system-f-type (system-f-fallback "type"))
  (define-syntax-generic system-f-require-spec (system-f-fallback "require spec")
    #:dispatch-on pair-only)
  (define-syntax-generic system-f-provide-spec (system-f-fallback "provide spec")
    #:dispatch-on pair-only)

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

  (define (e+t-e/t=! v t [sc #f] #:src src-stx)
    (type=! (e+t-t v) t sc #:src src-stx)
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
             #:literals [#%plain-module-begin begin-for-syntax]
             #:datum-literals [:]
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
             [(head:#%define ~! x:id : {~type t:type} e:expr)
              #:do [(define t- (e+t-e/t=! (expand-type #'t #f) #'Type sc #:src #'t))
                    (define x- (scope-bind! sc #'x (make-local-var t-)))]
              (loop stxs-to-go* (cons (datum->syntax this-syntax
                                                     (list #'head x- ': t- #'e)
                                                     this-syntax
                                                     this-syntax)
                                      stxs-deferred))]
             [(head:#%define-syntax ~! x:id e)
              #:with e- (local-transformer-expand
                         #`(let ([transformer e])
                             (generics [system-f-decl transformer]
                                       [system-f-expr transformer]))
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
             [(head:#%begin-for-syntax ~! d ...)
              #:with (#%plain-module-begin (begin-for-syntax d- ...))
              (local-expand #'(#%plain-module-begin (begin-for-syntax d ...)) 'module-begin '())
              (loop stxs-to-go* (cons (datum->syntax this-syntax
                                                     (cons #'head (attribute d-))
                                                     this-syntax
                                                     this-syntax)
                                      stxs-deferred))]
             [({~or #%define-type}
               ~! . _)
              (error "not yet implemented")]
             [({~or #%provide #%define-main} ~! . _)
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
            [({~or #%require #%define-syntax #%begin-for-syntax} ~! . _)
             ; already handled in first pass
             (values (cons this-syntax expanded-decls) main-decls)]
            [(head:#%provide ~! ps ...)
             #:do [(define expanded-pss (append-map (lambda (ps) (expand-system-f-provide-spec ps sc))
                                                    (attribute ps)))]
             (values (cons (datum->syntax this-syntax
                                          (cons #'head expanded-pss)
                                          this-syntax
                                          this-syntax)
                           expanded-decls)
                     main-decls)]
            [(head:#%define ~! x:id : t:type e:expr)
             #:do [(define e- (e+t-e/t=! (expand-expr #'e sc) #'t sc #:src #'e))]
             (values (cons (datum->syntax this-syntax
                                          (list #'head #'x ': #'t e-)
                                          this-syntax
                                          this-syntax)
                           expanded-decls)
                     main-decls)]
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
                           (list #'head f- (e+t-e/t=! (recur #'e) e-t sc #:src #'e))
                           this-syntax
                           this-syntax)
            r-t)]
      [(head:#%lambda ~! [x:id : {~type t:type}] e:expr)
       #:do [(define sc* (make-expression-scope sc))
             (define t- (e+t-e/t=! (expand-type #'t sc) #'Type sc #:src #'t))
             (define x- (scope-bind! sc* #'x (make-local-var t-)))
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
             (define t- (e+t-e/t=! (expand-type #'t sc) x-k sc #:src #'t))
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
             (define k- (e+t-e/t=! (expand-type #'k sc) #'Type sc #:src #'k))
             (define x- (scope-bind! sc* #'x (make-type-var k-)))
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
       #:when (or (not (system-f-type? this-syntax sc))
                  (id-only? this-syntax sc))
       (recur (datum->syntax this-syntax
                             (cons (datum->syntax #'here '#%type:app) this-syntax)
                             this-syntax))]
      [_
       (recur (macro-track-origin (apply-as-transformer system-f-type sc this-syntax)
                                  this-syntax))]))

  (define-syntax-class relative-path-string
    #:description "relative path string"
    #:commit
    #:opaque
    #:attributes []
    [pattern s:string #:when (relative-path? (syntax-e #'s))])

  (define-syntax-class literal-path
    #:description "literal path"
    #:commit
    #:opaque
    #:attributes []
    [pattern v #:when (path? (syntax-e #'v))])

  (define-syntax-class root-module-path
    #:description "root module path"
    #:commit
    #:attributes []
    #:datum-literals [quote lib file]
    [pattern (quote ~! _:id)]
    [pattern _:relative-path-string]
    [pattern (lib ~! _:relative-path-string ...+)]
    [pattern (file ~! _:string)]
    [pattern _:id]
    [pattern _:literal-path])

  (define-syntax-class module-path
    #:description "module path"
    #:commit
    #:attributes []
    #:datum-literals [submod]
    [pattern _:root-module-path]
    [pattern (submod ~! {~or _:root-module-path "." ".."} _:id ...+)])

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

  (define (expand-system-f-require-spec stx sc)
    (define (recur stx) (expand-system-f-require-spec stx sc))
    (syntax-parse stx
      #:literal-sets [core-require-spec-literals]
      #:datum-literals [=>]
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
       (recur (macro-track-origin (apply-as-transformer system-f-require-spec sc this-syntax)
                                  this-syntax))]))

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

  (define (expand-system-f-provide-spec stx sc)
    (define (recur stx) (expand-system-f-provide-spec stx sc))
    (syntax-parse stx
      #:literal-sets [core-provide-spec-literals]
      #:datum-literals [=>]
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
       (recur (macro-track-origin (apply-as-transformer system-f-provide-spec sc this-syntax)
                                  this-syntax))]))

  (define (local-expand-system-f-provide-spec stx [sc #f])
    (datum->syntax #f (cons (datum->syntax #'here '#%union) (expand-system-f-provide-spec stx sc)))))

(define-syntax system-f:shift
  (generics
   [system-f-require-spec
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
   [system-f-provide-spec
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
  (define (system-f-decl->racket-decl stx internal-introduce)
    (macro-track-origin
     (syntax-parse stx
       #:literal-sets [core-decl-literals]
       #:datum-literals [:]
       [(#%require ~! . _)
        ; requires are lifted during expansion, so we don’t need to do anything with them here
        #'(begin)]
       [(#%provide ~! ps ...)
        #`(begin #,@(map system-f-provide-spec->racket-decl (attribute ps)))]
       [(#%define ~! x:id : t:type e:expr)
        #:with internal-x (internal-introduce #'x)
        #`(begin
            (define internal-x #,(~> (system-f-expr->racket-expr (internal-introduce #'e))
                                     (syntax-track-residual (system-f-type->residual #'t))))
            (define-syntax x (make-module-var (quote-syntax/launder t)
                                              (quote-syntax/launder internal-x))))]
       [(#%define-syntax ~! x:id e)
        #`(define-syntax x #,(suspend-expression #'e))]
       [(#%begin-for-syntax ~! d ...)
        #`(begin-for-syntax #,@(map suspend-racket-decl (attribute d)))]
       [(#%define-main ~! e:expr)
        #`(module* main #f
            (#%plain-module-begin
             #,(system-f-expr->racket-expr (internal-introduce #'e))))]
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
       [x:module-var-id
        (attribute x.racket-id)]
       [_:id
        this-syntax]
       [(#%system-f:datum ~! lit:system-f-literal)
        #'(#%datum . lit)]
       [(#%system-f:app ~! f:expr e:expr)
        #`(#%plain-app #,(system-f-expr->racket-expr #'f) #,(system-f-expr->racket-expr #'e))]
       [(#%lambda ~! [x:id : t:type] e:expr)
        (~> #`(#%plain-lambda [x] #,(system-f-expr->racket-expr #'e))
            (syntax-track-residual (system-f-type->residual #'t)))]
       [(#%App ~! e:expr t:type)
        (~> (system-f-expr->racket-expr #'e)
            (syntax-track-residual (system-f-type->residual #'t)))]
       [(#%Lambda ~! [x:id : k:type] e:expr)
        (~> (system-f-expr->racket-expr #'e)
            (syntax-track-residual (make-residual (list (system-f-type->residual #'k))
                                                  #:bindings (list #'x))))]
       [_
        (raise-syntax-error
         'system-f
         "internal error: unexpected expression form found during extraction to racket"
         this-syntax)])
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
      #:literal-sets [core-decl-literals]
      [({~or #%require #%define-syntax #%begin-for-syntax} ~! . _) #f]
      [_ #t])))

; Defer to a secondary #%module-begin form to establish a lift target for requires (lifts are not
; legal in a 'module-begin context).
(define-syntax-parser #%system-f:module-begin
  [(_ decl ...)
   #'(#%plain-module-begin (#%system-f:inner-module-begin decl ...))])

(define-syntax-parser #%system-f:inner-module-begin
  [(_ lang-mod-path decl ...)
   #:do [(define lang-nss (module-exported-namespaces (syntax->datum #'lang-mod-path)))
         (define ns-rsc (make-require-scope!
                         (for/list ([ns (in-set lang-nss)])
                           (~>> (namespace-exports-submodule-path #'lang-mod-path ns)
                                (in-namespace ns)))))]
   #:with [namespaced-decl ...] (~> (in-value-namespace #'[decl ...])
                                    (require-scope-introduce ns-rsc _ 'add))
   #:with [expanded-decl ...] (expand-module (attribute namespaced-decl))
   #:do [(println (syntax-local-introduce
                   #`(#%system-f:module-begin
                      #,@(filter system-f-debug-print-decl? (attribute expanded-decl)))))]
   #:do [(define internal-introducer (make-syntax-introducer #t))
         (define (internal-introduce stx)
           (introduce-everywhere stx (lambda (stx) (internal-introducer stx 'add))))
         (define suspenders (make-suspenders))]
   #:with [racket-decl ...] (parameterize ([current-suspenders suspenders])
                              (for/list ([expanded-decl (in-list (attribute expanded-decl))])
                                (system-f-decl->racket-decl expanded-decl internal-introduce)))
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
