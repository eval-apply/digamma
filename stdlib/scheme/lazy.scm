;;; Copyright (c) 2004-2019 Yoshikatsu Fujita / LittleWing Company Limited.
;;; See LICENSE file for terms and conditions of use.

(define-library
  (scheme lazy)
  (import (rnrs) (only (core) tuple tuple? tuple-ref tuple-set!))
  (export delay
          force
          promise?
          delay-force
          make-promise)
  (begin

    (define-syntax delay
      (syntax-rules ()
        ((_ expr)
         (delay-force (make-promise expr)))))

    (define-syntax delay-force
      (syntax-rules ()
        ((_ expr)
         (tuple 'type:promise (cons #f (lambda () expr))))))

    (define make-promise
      (lambda (obj)
        (tuple 'type:promise (cons #t obj))))

    (define promise?
      (lambda (obj)
        (and (tuple? obj) (eq? (tuple-ref obj 0) 'type:promise))))

    (define promise-done?
      (lambda (obj)
        (if (promise? obj) (car (tuple-ref obj 1)) #t)))

    (define promise-value
      (lambda (obj)
        (if (promise? obj) (cdr (tuple-ref obj 1)) obj)))

    (define promise-datum
      (lambda (promise)
        (tuple-ref promise 1)))

    (define promise-datum-set!
      (lambda (promise datum)
        (tuple-set! promise 1 datum)))

    (define force
      (lambda (promise)
        (if (promise-done? promise)
            (promise-value promise)
            (let ((ans ((promise-value promise))))
              (cond ((promise-done? promise)
                     (promise-value promise))
                    (else
                     (promise-datum-set! promise (promise-datum ans))
                     (force promise)))))))
  )
) ;[end]