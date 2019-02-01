#lang racket/base

; This module defines syntactic namespaces, which are separate binding environments that can coexist
; within a single phase. (They have no relation to what Racket calls “namespaces”, which are used for
; reflective operations.) In a namespace-enabled Racket language, every binding in the program belongs
; to exactly one namespace, and definitions in a given namespace can only be referenced by uses in the
; same namespace.
;
; For example, in a typed language, types and values may be bound in separate namespaces. The `define`
; form in such a language would create new bindings in the value namespace, but a `define-type` form
; would create new bindings in the type namespace. This allows two definitions with the same name to
; coexist, even in the same scope, so long as they are in separate namespaces:
;
;   (define (Foo [x : Integer] [y : String])
;     (Tuple (* x 2) y))
;
;   (define-type Foo (Tuple Integer String))
;
; In the above example, `Foo` is defined both as a function in the value namespace and as a type alias
; in the type namespace. Also note that `Tuple` is *used* in two different ways, based on the
; containing namespace — it is applied as a function inside the body of the `Foo` function while also
; being used as a type constructor in the definition of the `Foo` type alias. These uses are
; unambiguous because the namespace each reference belongs to is syntactically determined: the body of
; an ordinary definition is always in the value namespace, and the right hand side of a type alias
; definition is always in the type namespace.
;
; Note, however, that the namespaces are not always entirely syntactically separate — individual
; subforms can be in a separate namespace from their surrounding context. For example, using the above
; example again, the `x` and `y` identifiers are bound in the value namespace, but their type
; annotations, `Integer` and `String`, are references in the type namespace. This interleaving of
; namespaces is not unique to definition forms; arbitrary expressions can also have some subforms
; remain in the value namespace while others may be in the type namespace. For example, in the
; type annotation expression
;
;   (: (Tuple 42 "hello") (Tuple Integer String))
;
; the first subform, (Tuple 42 "hello"), remains in the value namespace, while the second subform,
; (Tuple Integer String), is expanded in the type namespace.

(require (for-meta 2 racket/base
                     racket/syntax
                     "util/stx.rkt")
         (for-syntax net/base64
                     racket/base
                     racket/contract
                     racket/random
                     racket/set
                     racket/syntax
                     syntax/modcollapse
                     syntax/parse/define
                     "util/stx.rkt")
         syntax/parse/define)

(provide define-namespace provide/namespace)

(begin-for-syntax
  (provide (contract-out
            [make-namespace (-> symbol? namespace?)]
            [namespace-key (-> namespace? symbol?)]
            [in-namespace (-> namespace? syntax? syntax?)]
            [namespace-exports-submodule-name (-> namespace? symbol?)]
            [namespace-exports-submodule-path (->i ([mod-path (or/c module-path? module-path-syntax?)]
                                                    [ns namespace?])
                                                   [result (mod-path) (if (syntax? mod-path)
                                                                          module-path-syntax?
                                                                          module-path?)])]
            [module-exported-namespaces (-> module-path? (set/c #:cmp 'equal namespace?))])))

;; ---------------------------------------------------------------------------------------------------
;; core definitions

; Since Racket programs contain macros, it isn’t always straightforward to determine which namespace
; a particular program fragment belongs to, in the same way it isn’t always straightforward to
; determine which bindings are in scope. Racket solves the latter problem by attaching scoping
; information to every syntax object in the program, and namespaces solve the former problem the same
; way.
;
; In a non-namespaced program, a syntax object pairs a datum with a set of scopes. A namespaced
; program extends this with one additional piece of information: the syntax object’s namespace. A
; syntax object always belongs to exactly one namespace, which is the primary difference between
; namespaces and scopes: while adding a scope to a syntax object does not affect other scopes already
; on the object, moving a syntax object into a new namespace removes it from its old namespace.
;
; Aside from this difference, namespaces and scopes are identical in how they affect binding. A
; namespace can be thought of as nothing more than another scope on a given syntax object for the
; purposes of binding (and indeed, that is how they are currently implemented).

(begin-for-syntax
  (struct namespace (key introducer)
    #:property prop:object-name (struct-field-index key)
    #:property prop:custom-write
    (lambda (ns out mode)
      (fprintf out "#<namespace:~a>" (namespace-key ns)))
    #:property prop:equal+hash
    (list (lambda (ns-a ns-b recur) (eq? (namespace-key ns-a) (namespace-key ns-b)))
          (lambda (ns recur) (eq-hash-code (namespace-key ns)))
          (lambda (ns recur) (recur (namespace-key ns)))))

  (define all-namespaces (mutable-set))

  ; make-namespace : symbol? -> namespace?
  ;
  ; Creates a new namespace with the provided symbolic key. Two namespaces created with the same key
  ; refer to the same namespace. In other words, `make-namespace` is not generative in the same way
  ; that prefab structures are not generative. This is mostly an unfortunate artifact of the
  ; implementation, but the `define-namespace` form (see below) provides some support for avoiding
  ; accidental namespace key collisions.
  ;
  ; Internally, namespaces are implemented using interned scopes. A procedure returned by
  ; `make-interned-syntax-introducer` will manipulate the same scope as a namespace with the same key.
  ; Doing so can result in multiple namespace scopes being applied to the same syntax object, so this
  ; is strongly discouraged.
  (define (make-namespace key)
    (define ns (namespace key (make-interned-syntax-introducer key)))
    (set-add! all-namespaces ns)
    ns)

  ; in-namespace : namespace? syntax? -> syntax?
  ;
  ; Changes the namespace of a syntax object.
  (define (in-namespace new-ns stx)
    ((namespace-introducer new-ns)
     (for/fold ([stx stx])
               ([ns (in-set all-namespaces)]
                #:unless (equal? ns new-ns))
       ((namespace-introducer ns) stx 'remove))
     'add)))

;; ---------------------------------------------------------------------------------------------------
;; `define-namespace`

; The `define-namespace` form provides a shorthand for defining namespaces and namespace forms. The
; form
;
;   (define-namespace x)
;
; defines three new bindings: `namespace:x`, `in-x-namespace`, and `~x`. `namespace:x` is bound to a
; namespace value, which can be applied to a syntax object using `in-namespace`. `in-x-namespace` is
; bound to a procedure that applies the namespace to a syntax object. `~x` is bound to a syntax/parse
; pattern expander which applies the namespace to the syntax object before parsing any sub-patterns.
;
; To avoid key conflicts between namespaces, the `#:unique` option may be provided to
; `define-namespace`, which will automatically append a globally-unique identifier to the namespace
; key. This unique identifier will be regenerated each time the `define-namespace` form is compiled,
; but it will be consistent across multiple visits of the containing module.

(begin-for-syntax
  (define (random-uuid)
    (crypto-random-bytes 16))

  (define (random-uuid/base64)
    (bytes->string/utf-8 (subbytes (base64-encode (random-uuid) #"") 0 22))))

(define-simple-macro (define-namespace name:id
                       {~alt {~or {~optional {~seq #:key base-key:id}
                                             #:defaults ([base-key #'name])}
                                  {~optional {~and #:unique unique?}}}}
                       ...)
  #:do [(define name-len (string-length (symbol->string (syntax-e #'name))))]
  #:with {~var namespace:name} (derived-id "namespace:" #'name "")
  #:with in-name-namespace (derived-id "in-" #'name "-namespace")
  #:with {~var ~name} (derived-id "~" #'name "")
  #:with key (if (attribute unique?)
                 (format-id #f "~a-~a" #'base-key (random-uuid/base64))
                 #'base-key)
  (begin-for-syntax
    (define namespace:name (make-namespace 'key))
    (define (in-name-namespace stx)
      (in-namespace namespace:name stx))
    (define-syntax ~name
      (pattern-expander
       (syntax-parser
         [(_ {~describe "pattern" pat})
          #'{~and tmp {~parse pat (in-namespace namespace:name #'tmp)}}])))))

;; ---------------------------------------------------------------------------------------------------
;; importing and exporting namespaced bindings

; While interned scopes can be used to relatively cleanly implement namespaces within a single module,
; things get more complicated once multiple modules come into play. The trouble stems from the fact
; that modules do not really import and export identifiers, they export symbols — the rich scoping
; information associated with bindings is discarded when a binding is exported. This makes sense,
; since that scoping information includes the scope of the module the binding is declared in, among
; other things, so if the scopes were preserved when the binding was imported by another module, the
; importing module wouldn’t actually be able to access the binding. Similarly, the various namespace
; management features provided by `require` subforms such as `rename-in` and `except-in` become much
; more complicated if several identifiers can be exported from the same module with the same name.
;
; It is tempting to repurpose phases for the purpose of namespace management, since modules *can*
; export multiple identifiers with the same name so long as they are at different phases. However,
; this doesn’t really work, since phases are designed to be used to create entirely distinct
; evaluation environments, and the degree of separation they enforce is just too much for namespaces,
; which need to be able to support truly interleaved binding environments.
;
; An alternative solution is to use submodules. Instead of providing identifiers directly, modules
; provide them through submodules, with a different submodule for each namespace. It’s straightforward
; for two submodules to provide the same name at the same phase with different bindings, and by using
; lexically nested submodules (i.e. `module*` submodules with #f for the module language), submodules
; have access to the full, multi-namespace binding environment of the enclosing module.
;
; Finally, providing modules also declare a metadata submodule, named `exported-namespaces`, which
; provides information about which submodules actually hold the namespaced bindings. Importing modules
; inspect this submodule (if one exists) and redirect requires to the relevant submodules as
; necessary, renaming the bindings to local ones with the appropriate namespaces.
;
; As a final wrinkle, module languages that export namespaced identifiers require special care.
; Ordinarily, identifiers imported using `require` can shadow identifiers that come from the module
; language, which is important since users have no way to suppress imported identifiers that come from
; the module language. Therefore, rewriting imports from the module language to module-level
; `require`s is insufficient, since those imports would not be able to be shadowed. A workable
; approach is to instead use `syntax-local-lift-require` to indirectly declare the imports, since such
; imports can, in fact, be shadowed by module-level `require`s.

(begin-for-syntax
  (define namespaces-exported-from-current-module (mutable-set))

  ; namespace-exports-submodule-name : namespace? -> symbol?
  ;
  ; Returns the name of the submodule used to provide exported bindings in the given namespace.
  (define (namespace-exports-submodule-name ns)
    (format-symbol "~a-exports" (namespace-key ns)))

  (define (namespace-exports-submodule-path base-mod-path ns)
    (module-path-submodule base-mod-path (namespace-exports-submodule-name ns)))

  ; namespace->expression : namespace? -> syntax?
  ;
  ; Returns a syntax object that, when evaluated as a Racket expression, will produce a namespace with
  ; the same key as the given namespace.
  (define (namespace->expression ns)
    #`(make-namespace '#,(namespace-key ns)))

  ; module-exported-namespaces : module-path? -> (set/c namespace?)
  ;
  ; Given a module path, returns the set of namespaces in which the referenced module exports
  ; identifiers.
  (define (module-exported-namespaces mod-path)
    (unless (module-declared? mod-path #t)
      (raise-arguments-error 'module-exported-namespaces "submodule does not exist"
                             "module path" mod-path))
    (define exported-namespaces-mod-path (collapse-module-path '(submod "." exported-namespaces)
                                                               mod-path))
    (if (module-declared? exported-namespaces-mod-path #t)
        (dynamic-require exported-namespaces-mod-path 'exported-namespaces)
        (set))))

; A macro that handles kick-starting the namespacing system by exporting identifiers into a namespace
; from a module written in a non-namespaced language. Use of `provide/namespace` expand into
; submodules that provide namespaced identifiers indirectly, and they also arrange for the
; appropriate `exported-namespaces` submodule to be declared at the end of the module.
(define-syntax-parser provide/namespace
  [(_ ns-e:expr ps ...)
   #:fail-unless (eq? (syntax-local-context) 'module) "not at module level"
   #:with ns-e- (local-transformer-expand #'ns-e 'expression '())
   #:do [(define ns (syntax-local-eval #'ns-e-))
         (unless (namespace? ns)
           (raise-argument-error 'provide/namespace "namespace?" ns))
         (when (set-empty? namespaces-exported-from-current-module)
           (syntax-local-lift-module-end-declaration #'(declare-exported-namespaces-submodule)))
         (set-add! namespaces-exported-from-current-module ns)]
   #:with mod-name (namespace-exports-submodule-name ns)
   #'(begin
       (begin-for-syntax
         ; for check syntax
         (define-values [] (begin (lambda () ns-e-) (values))))
       (module+ mod-name
         (provide ps ...)))])

(define-syntax-parser declare-exported-namespaces-submodule
  [(_)
   #:with [ns-e ...] (set-map namespaces-exported-from-current-module namespace->expression)
   #'(begin-for-syntax
       (module* exported-namespaces #f
         (provide exported-namespaces)
         (define exported-namespaces (set ns-e ...))))])
