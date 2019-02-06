#lang racket/base

(require syntax/parse)

(provide module-path)

(define-syntax-class module-path
  #:description "module path"
  #:commit
  #:attributes []
  #:datum-literals [submod]
  [pattern _:root-module-path]
  [pattern (submod ~! {~or _:root-module-path "." ".."} _:id ...+)])

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
