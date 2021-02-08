#lang racket/base

(define (child)
  (begin (sleep 1) (display "Wor\n") (sleep 2))
  )

(define (main)
  (begin
    (display "Hello\n")
    (thread (lambda () (child)))
    (sleep 4)
    (display "ld\n")
    (sleep 5)
   ))

(void (main))

