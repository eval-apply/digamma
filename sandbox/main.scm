<<<<<<< HEAD
=======
; digamma sandbox/main.scm

>>>>>>> master
(import (core)
        (digamma glcorearb)
        (digamma glfw)
        (digamma view)
        (digamma widget)
        (digamma c-ffi)
        (digamma c-types))

(define main
  (lambda ()
    (define error-callback
      (lambda (error description)
        (format #t "error: ~a~%~!" (utf8->string (make-bytevector-mapping description 1024)))))
    (define key-callback
      (lambda (window key scancode action mods)
        (and (= key GLFW_KEY_ESCAPE)
             (= action GLFW_PRESS)
             (glfwSetWindowShouldClose window GLFW_TRUE))))
    (glfwSetErrorCallback (c-callback void (int void*) error-callback))
    (let ((window (init-window 512 192 "Digamma")))
      (glfwSetKeyCallback window (c-callback void (void* int int int int) key-callback))
      (glfwMakeContextCurrent window)
      (glfwSwapInterval 1)
      (let ((m (make-bytevector 64))
            (p (make-bytevector 64))
            (mvp (make-bytevector 64))
            (width (make-c-int 0))
            (height (make-c-int 0))
            (widget0 (make-text-widget "sandbox/Roboto-Regular.ttf" 300)))
          (glEnable GL_BLEND)
          (glBlendFunc GL_SRC_ALPHA GL_ONE_MINUS_SRC_ALPHA)
          (let loop ()
            (cond ((= (glfwWindowShouldClose window) 0)
                   (glfwGetFramebufferSize window width height)
                   (glViewport 0 0 (c-int-ref width) (c-int-ref height))
                   (glClear GL_COLOR_BUFFER_BIT)
                   (mat4x4-identity m)
                   #;(mat4x4-rotate m m 0 0 -1 (glfwGetTime))
                   (let ((ratio (/ (inexact (c-int-ref width)) (inexact (c-int-ref height)))))
                     (mat4x4-ortho p (- ratio) ratio -1 1 1 -1))
                   (mat4x4-mul mvp p m)
                   (widget0 mvp 0.2 1.0 0.4 1.0 -1.5 0.2 0.3 "Quick brown fox jumps")
                   (widget0 mvp 0.2 1.0 0.4 1.0 -1.5 -0.2 0.3 "over the lazy dog")
                   (glfwSwapBuffers window)
                   (glfwPollEvents)
                   (loop))
                  (else
                   (glfwDestroyWindow window) (glfwTerminate) (exit 0))))))))

(main)
<<<<<<< HEAD

; digamma sandbox/main.scm
=======
>>>>>>> master
