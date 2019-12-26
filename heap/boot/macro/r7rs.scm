;;; Copyright (c) 2004-2019 Yoshikatsu Fujita / LittleWing Company Limited.
;;; See LICENSE file for terms and conditions of use.

(define read-file-to-include
  (lambda (path)
    (let ((abs-path (locate-include-file path)))
      (and (scheme-load-verbose) (format #t "~&;; including ~s~%~!" abs-path))
      (let ((port (open-script-input-port abs-path)))
        (with-exception-handler
        (lambda (c)
          (cond ((serious-condition? c)
                  (close-port port)
                  (raise c))
                (else
                  (raise-continuable c))))
        (lambda ()
            (let loop ((acc '()))
              (let ((form (core-read port (current-source-comments) 'include)))
                (cond ((eof-object? form) (close-port port) (reverse acc))
                      (else
                        (loop (cons form acc))))))))))))

(define expand-define-library
  (lambda (form env)

    (define permute-env
      (lambda (ht)
        (let loop ((lst (core-hashtable->alist ht)) (bounds '()) (unbounds '()))
          (cond ((null? lst) (append bounds unbounds)) ((unbound? (cdar lst)) (loop (cdr lst) bounds (cons (car lst) unbounds))) (else (loop (cdr lst) (cons (car lst) bounds) unbounds))))))

    (destructuring-match form
      ((_ library-name clauses ...)
       (let ((library-id (library-name->id form library-name)) (library-version (library-name->version form library-name)))
         (and library-version (core-hashtable-set! (scheme-library-versions) library-id library-version))
         (parameterize ((current-include-files (make-core-hashtable)))
             (let ((coreform
                     (let loop ((clauses clauses) (exports '()) (imports '()) (depends '()) (commands '()))
                       (if (null? clauses)
                           (let ((ht-immutables (make-core-hashtable)) (ht-imports (make-core-hashtable)) (ht-publics (make-core-hashtable)))
                             (for-each (lambda (a)
                                         (and (core-hashtable-ref ht-publics (cdr a) #f)
                                              (syntax-violation 'define-library "duplicate export identifiers" (abbreviated-take-form form 4 8) (cdr a)))
                                         (core-hashtable-set! ht-publics (cdr a) #t)
                                         (core-hashtable-set! ht-immutables (car a) #t))
                                       exports)
                             (for-each (lambda (a)
                                         (core-hashtable-set! ht-immutables (car a) #t)
                                         (cond ((core-hashtable-ref ht-imports (car a) #f)
                                                => (lambda (deno)
                                                     (or (eq? deno (cdr a))
                                                         (syntax-violation 'define-library "duplicate import identifiers" (abbreviated-take-form form 4 8) (car a)))))
                                               (else (core-hashtable-set! ht-imports (car a) (cdr a)))))
                                       imports)
                             (let ((ht-env (make-shield-id-table commands)) (ht-libenv (make-core-hashtable)))
                               (for-each (lambda (a)
                                           (core-hashtable-set! ht-env (car a) (cdr a))
                                           (core-hashtable-set! ht-libenv (car a) (cdr a)))
                                         (core-hashtable->alist ht-imports))
                               (parameterize ((current-immutable-identifiers ht-immutables))
                                 (expand-define-library-body form library-id library-version commands exports imports depends
                                   (extend-env private-primitives-environment (permute-env ht-env))
                                   (permute-env ht-libenv)))))
                           (destructuring-match clauses
                             ((('export export-spec ...) more ...)
                              (loop more (append exports (parse-exports form export-spec)) imports depends commands))
                             ((('import import-spec ...) more ...)
                              (loop more exports (append imports (parse-imports form import-spec)) (append depends (parse-depends form import-spec)) commands))
                             ((('include (? string? path)) more ...)
                              (loop (cons (cons 'begin (read-file-to-include path)) more) exports imports depends commands))
                             ((('include-library-declarations (? string? path)) more ...)
                              (loop (append (read-file-to-include path) more) exports imports depends commands))
                             ((('cond-expand _ ... ('else body ...)) more ...)
                              (loop (append body more) exports imports depends commands))
                             ((('begin body ...) more ...)
                              (loop more exports imports depends (append commands body)))
                             (_
                              (syntax-violation 'define-library "malformed library declarations" (abbreviated-take-form form 4 8) (car clauses))))))))
               (or (= (core-hashtable-size (current-include-files)) 0)
                   (core-hashtable-set! library-include-dependencies library-id (current-include-files)))
               coreform))))
      (_ (syntax-violation 'define-library "expected library name and declarations" (abbreviated-take-form form 4 8))))))

(define expand-define-library-body
  (lambda (form library-id library-version body exports imports depends env libenv)

    (define initial-libenv #f)

    (define internal-definition?
      (lambda (lst)
        (and (pair? lst)
             (pair? (car lst))
             (symbol? (caar lst))
             (let ((deno (env-lookup env (caar lst))))
               (or (macro? deno)
                   (eq? denote-define deno)
                   (eq? denote-define-syntax deno)
                   (eq? denote-let-syntax deno)
                   (eq? denote-letrec-syntax deno))))))

    (define macro-defs '())

    (define extend-env!
      (lambda (datum1 datum2)
        (and (macro? datum2)
             (set! macro-defs (acons datum1 datum2 macro-defs)))
        (set! env (extend-env (list (cons datum1 datum2)) env))
        (for-each (lambda (a) (set-cdr! (cddr a) env)) macro-defs)))

    (define extend-libenv!
      (lambda (datum1 datum2)
        (set! libenv (extend-env (list (cons datum1 datum2)) libenv))
        (current-template-environment libenv)))

    (define ht-imported-immutables (make-core-hashtable))

    (define expression-tag
      (let ((num 0))
        (lambda ()
          (set! num (+ num 1))
          (string->symbol (format ".e~a" num)))))

    (current-template-environment libenv)
    (for-each (lambda (b) (core-hashtable-set! ht-imported-immutables (car b) #t)) imports)
    (let loop ((body (flatten-begin body env)) (defs '()) (macros '()) (renames '()))
      (cond ((null? body) (rewrite-library-body form library-id library-version body (reverse defs) (reverse macros) renames exports imports depends env libenv))
            ((and (pair? body) (pair? (car body)) (symbol? (caar body)))
             (let ((deno (env-lookup env (caar body))))
               (cond ((eq? denote-begin deno) (loop (flatten-begin body env) defs macros renames))
                     ((eq? denote-define-syntax deno)
                      (destructuring-match body
                        (((_ (? symbol? org) clause) more ...)
                         (begin
                           (and (core-hashtable-contains? ht-imported-immutables org)
                                (syntax-violation
                                  'define-syntax
                                  "attempt to modify immutable binding"
                                  (car body)))
                           (let-values (((code . expr)
                                         (parameterize ((current-template-environment initial-libenv))
                                           (compile-macro (car body) clause env))))
                             (let ((new (generate-global-id library-id org)))
                               (extend-libenv! org (make-import new))
                               (cond ((procedure? code)
                                      (extend-env! org (make-macro code env))
                                      (loop more defs (cons (list org 'procedure (car expr)) macros) (acons org new renames)))
                                     ((macro-variable? code)
                                      (extend-env! org (make-macro-variable (cadr code) env))
                                      (loop more defs (cons (list org 'variable (car expr)) macros) (acons org new renames)))
                                     (else
                                       (extend-env! org (make-macro code env))
                                       (loop more defs (cons (list org 'template code) macros) (acons org new renames))))))))
                        (_
                          (syntax-violation
                            'define-syntax
                            "expected symbol and single expression"
                            (car body)))))
                     ((eq? denote-define deno)
                      (let ((def (annotate (cdr (desugar-define (car body))) (car body))))
                        (and (core-hashtable-contains? ht-imported-immutables (car def))
                             (syntax-violation 'define "attempt to modify immutable binding" (car body)))
                        (let ((org (car def)) (new (generate-global-id library-id (car def))))
                          (extend-env! org new)
                          (extend-libenv! org (make-import new))
                          (loop (cdr body) (cons def defs) macros (acons org new renames)))))
                     ((or (macro? deno) (eq? denote-let-syntax deno) (eq? denote-letrec-syntax deno))
                      (let-values (((expr new) (expand-initial-forms (car body) env)))
                        (set! env new)
                        (loop (append (flatten-begin (list expr) env) (cdr body)) defs macros renames)))
                     (else
                       (loop
                         (cons `(.define ,(expression-tag) ,(car body)) (cdr body)) defs macros renames)))))
            (else
              (loop (cons `(.define ,(expression-tag) ,(car body)) (cdr body)) defs macros renames))))))
#|
(define-library
  (foo)
  (export a b c)
  (import (rnrs))
  (begin (define a (lambda (x) (car x))) (define b (lambda (x) (cdr x))))
  (import (rename (core) (current-directory cd)))
  (include "include.ss")
  (begin (define c (lambda () (cd)))))
|#
#|
(define-library
  (foo)
  (export a b c)
  (import (rnrs))
  (begin (define a (lambda (x) (car x))) (define b (lambda (x) (cdr x))))
  (import (rename (core) (current-directory cd)))
  (include "include.ss")
  (begin (define c (lambda () (cd)))))
|#
#|
(define-library
  (foo)
  (include-library-declarations "decl.ss")
  (import (rnrs))
  (begin (define a (lambda (x) (car x))) (define b (lambda (x) (cdr x))))
  (import (rename (core) (current-directory cd)))
  (include "include.ss")
  (begin (define c (lambda () (cd)))))
|#
#|
(define-library
  (foo)
  (include-library-declarations "decl.ss")
  (import (rnrs))
  (begin (define a (lambda (x) (car x))) (define b (lambda (x) (cdr x))))
  (import (rename (core) (current-directory cd)))
  (include "include.ss")
  (cond-expand (scm) (else (begin (define c (lambda () (cd)))))))
|#