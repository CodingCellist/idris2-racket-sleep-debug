#lang racket/base
; required for foreign lib interfacing
(require ffi/unsafe
         ffi/unsafe/define)
; define that we need foreign_sleep.so
(define-ffi-definer define-fsleep (ffi-lib "foreign_sleep"))

; define our foreign sleep function as: void fsleep(int i)
(define-fsleep fsleep (_fun _int -> _void))

(define (child)
  (begin (fsleep 1) (display "Wor\n") (fsleep 2))
  )

(define (main)
  (begin
    (display "Hello\n")
    (thread (lambda () (child)))
    (fsleep 4)
    (display "ld\n")
    (fsleep 5)
   ))

(void (main))

