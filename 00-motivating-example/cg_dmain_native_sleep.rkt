#lang racket/base
; @generated
(require racket/async-channel)
(require racket/future)
(require racket/math)
(require racket/system)
(require rnrs/bytevectors-6)
(require rnrs/io/ports-6)
(require srfi/19)
(require ffi/unsafe ffi/unsafe/define)
(define-ffi-definer define-libidris2_support (ffi-lib "libidris2_support" ))
(define-libidris2_support idris2_putStr (_fun _string/utf-8 -> _void))
(define-libidris2_support idris2_sleep (_fun _int -> _void))
(let ()
(define (blodwen-os)
  (case (system-type 'os)
    [(unix) "unix"]
    [(osx) "darwin"]
    [(windows) "windows"]
    [else "unknown"]))

(define blodwen-read-args (lambda (desc)
  (case (vector-ref desc 0)
    ((0) '())
    ((1) (cons (vector-ref desc 2)
               (blodwen-read-args (vector-ref desc 3)))))))
(define b+ (lambda (x y bits) (remainder (+ x y) (arithmetic-shift 1 bits))))
(define b- (lambda (x y bits) (remainder (- x y) (arithmetic-shift 1 bits))))
(define b* (lambda (x y bits) (remainder (* x y) (arithmetic-shift 1 bits))))
(define b/ (lambda (x y bits) (remainder (exact-floor (/ x y)) (arithmetic-shift 1 bits))))

(define integer->bits8 (lambda (x) (modulo x (expt 2 8))))
(define integer->bits16 (lambda (x) (modulo x (expt 2 16))))
(define integer->bits32 (lambda (x) (modulo x (expt 2 32))))
(define integer->bits64 (lambda (x) (modulo x (expt 2 64))))

(define bits16->bits8 (lambda (x) (modulo x (expt 2 8))))
(define bits32->bits8 (lambda (x) (modulo x (expt 2 8))))
(define bits32->bits16 (lambda (x) (modulo x (expt 2 16))))
(define bits64->bits8 (lambda (x) (modulo x (expt 2 8))))
(define bits64->bits16 (lambda (x) (modulo x (expt 2 16))))
(define bits64->bits32 (lambda (x) (modulo x (expt 2 32))))

(define blodwen-bits-shl (lambda (x y bits) (remainder (arithmetic-shift x y) (arithmetic-shift 1 bits))))
(define blodwen-shl (lambda (x y) (arithmetic-shift x y)))
(define blodwen-shr (lambda (x y) (arithmetic-shift x (- y))))
(define blodwen-and (lambda (x y) (bitwise-and x y)))
(define blodwen-or (lambda (x y) (bitwise-ior x y)))
(define blodwen-xor (lambda (x y) (bitwise-xor x y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))
(define cast-string-int
  (lambda (x)
    (exact-floor (cast-num (string->number (destroy-prefix x))))))
(define cast-int-char
  (lambda (x)
    (if (and (>= x 0)
             (<= x #x10ffff))
        (integer->char x)
        0)))
(define cast-string-double
  (lambda (x)
    (cast-num (string->number (destroy-prefix x)))))
(define (from-idris-list xs)
  (if (= (vector-ref xs 0) 0)
    '()
    (cons (vector-ref xs 1) (from-idris-list (vector-ref xs 2)))))
(define (to-idris-list-rev acc xs)
  (if (null? xs)
    acc
    (to-idris-list-rev (vector 1 (car xs) acc) (cdr xs))))
(define (string-concat xs) (apply string-append (from-idris-list xs)))
(define (string-unpack s) (to-idris-list-rev (vector 0) (reverse (string->list s))))
(define (string-pack xs) (list->string (from-idris-list xs)))
(define string-cons (lambda (x y) (string-append (string x) y)))
(define get-tag (lambda (x) (vector-ref x 0)))
(define string-reverse (lambda (x)
  (list->string (reverse (string->list x)))))
(define (string-substr off len s)
    (let* ((l (string-length s))
          (b (max 0 off))
          (x (max 0 len))
          (end (min l (+ b x))))
          (substring s b end)))

(define (blodwen-string-iterator-new s)
  0)

(define (blodwen-string-iterator-to-string _ s ofs f)
  (f (substring s ofs (string-length s))))

(define (blodwen-string-iterator-next s ofs)
  (if (>= ofs (string-length s))
      (vector 0)  ; EOF
      (vector 1 (string-ref s ofs) (+ ofs 1))))

(define either-left
  (lambda (x)
    (vector 0 x)))

(define either-right
  (lambda (x)
    (vector 1 x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

(define (blodwen-get-line p)
    (if (port? p)
        (let ((str (read-line p)))
            (if (eof-object? str)
                ""
                str))
        (void)))

(define (blodwen-get-char p)
    (if (port? p)
        (let ((chr (read-char p)))
            (if (eof-object? chr)
                #\nul
                chr))
        (void)))

;; Buffers

(define (blodwen-new-buffer size)
  (make-bytevector size 0))

(define (blodwen-buffer-size buf)
  (bytevector-length buf))

(define (blodwen-buffer-setbyte buf loc val)
  (bytevector-u8-set! buf loc val))

(define (blodwen-buffer-getbyte buf loc)
  (bytevector-u8-ref buf loc))

(define (blodwen-buffer-setbits16 buf loc val)
  (bytevector-u16-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits16 buf loc)
  (bytevector-u16-ref buf loc (native-endianness)))

(define (blodwen-buffer-setbits32 buf loc val)
  (bytevector-u32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits32 buf loc)
  (bytevector-u32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setbits64 buf loc val)
  (bytevector-u64-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getbits64 buf loc)
  (bytevector-u64-ref buf loc (native-endianness)))

(define (blodwen-buffer-setint32 buf loc val)
  (bytevector-s32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint32 buf loc)
  (bytevector-s32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setint buf loc val)
  (bytevector-s64-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint buf loc)
  (bytevector-s64-ref buf loc (native-endianness)))

(define (blodwen-buffer-setdouble buf loc val)
  (bytevector-ieee-double-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getdouble buf loc)
  (bytevector-ieee-double-ref buf loc (native-endianness)))

(define (blodwen-stringbytelen str)
  (bytevector-length (string->utf8 str)))

(define (blodwen-buffer-setstring buf loc val)
  (let* [(strvec (string->utf8 val))
         (len (bytevector-length strvec))]
    (bytevector-copy! strvec 0 buf loc len)))

(define (blodwen-buffer-getstring buf loc len)
  (let [(newvec (make-bytevector len))]
    (bytevector-copy! buf loc newvec 0 len)
    (utf8->string newvec)))

(define (blodwen-buffer-copydata buf start len dest loc)
  (bytevector-copy! buf start dest loc len))

;; Threads

(define (blodwen-thread proc)
  (thread (lambda () (proc (vector 0)))))

(define (blodwen-thread-wait handle)
  (thread-wait handle))

;; Thread mailboxes

(define blodwen-thread-data (make-thread-cell #f))

(define (blodwen-get-thread-data ty)
  (thread-cell-ref blodwen-thread-data))

(define (blodwen-set-thread-data a)
  (thread-cell-set! blodwen-thread-data a))

;; Semaphores

(define (blodwen-make-semaphore init)
  (make-semaphore init))

(define (blodwen-semaphore-post sema)
  (semaphore-post sema))

(define (blodwen-semaphore-wait sema)
  (semaphore-wait sema))

;; Barriers

(struct barrier (count-box num-threads mutex semaphore))

(define (blodwen-make-barrier num-threads)
  (barrier (box 0) num-threads (blodwen-make-mutex) (make-semaphore 0)))

(define (blodwen-barrier-wait barrier)
  (blodwen-mutex-acquire (barrier-mutex barrier))
  (let* [(count-box (barrier-count-box barrier))
         (count-old (unbox count-box))
         (count-new (+ count-old 1))
         (sema (barrier-semaphore barrier))]
    (set-box! count-box count-new)
    (blodwen-mutex-release (barrier-mutex barrier))
    (when (= count-new (barrier-num-threads barrier)) (semaphore-post sema))
    (semaphore-wait sema)
    (semaphore-post sema)
    ))

;; Channels

(define (blodwen-make-channel ty)
  (make-channel))

(define (blodwen-channel-get ty chan)
  (channel-get chan))

(define (blodwen-channel-put ty chan val)
  (channel-put chan val))

;; Mutex

(define (blodwen-make-mutex)
  (make-semaphore 1))

(define (blodwen-mutex-acquire sema)
  (semaphore-wait sema))

(define (blodwen-mutex-release sema)
  (if (semaphore-try-wait? sema)
      (blodwen-error-quit "Exception in mutexRelease: thread does not own mutex")
      (semaphore-post sema)))

;; Condition Variables

(define (blodwen-make-condition)
  (make-async-channel))

(define (blodwen-condition-wait ach mutex)
  ;; Pre-condition: this threads holds `mutex'.
  (let [(sema (make-semaphore 0))]
    (async-channel-put ach sema)
    (blodwen-mutex-release mutex)
    (sync sema)
    (blodwen-mutex-acquire mutex)))

(define (blodwen-condition-wait-timeout ach mutex timeout)
  ;; Pre-condition: this threads holds `mutex'.
  (let [(sema (make-semaphore 0))]
    (async-channel-put ach sema)
    (blodwen-mutex-release mutex)
    (sync/timeout (/ timeout 1000000) sema)
    (blodwen-mutex-acquire mutex)))

(define (blodwen-condition-signal ach)
  (let [(sema (async-channel-try-get ach))]
    (when sema (semaphore-post sema))))

(define (blodwen-condition-broadcast ach)
  (letrec [(loop (lambda ()
                   (let [(sema (async-channel-try-get ach))]
                     (when sema ((semaphore-post sema) (loop))))))]
    loop))


(define (blodwen-make-future work) (future work))
(define (blodwen-await-future ty future) (touch future))

(define (blodwen-sleep s) (sleep s))
(define (blodwen-usleep us) (sleep (* 0.000001 us)))

(define (blodwen-time) (current-seconds))

(define (blodwen-clock-time-utc) (current-time 'time-utc))
(define (blodwen-clock-time-monotonic) (current-time 'time-monotonic))
(define (blodwen-clock-time-duration) (current-time 'time-duration))
(define (blodwen-clock-time-process) (current-time 'time-process))
(define (blodwen-clock-time-thread) (current-time 'time-thread))
(define (blodwen-clock-time-gccpu) 0) ;; unsupported
(define (blodwen-clock-time-gcreal) 0) ;; unsupported
(define (blodwen-is-time? clk) (if (time? clk) 1 0))
(define (blodwen-clock-second time) (time-second time))
(define (blodwen-clock-nanosecond time) (time-nanosecond time))

(define (blodwen-args)
  (define (blodwen-build-args args)
    (if (null? args)
        (vector 0) ; Prelude.List
        (vector 1 (car args) (blodwen-build-args (cdr args)))))
    (blodwen-build-args
      (cons (path->string (find-system-path 'run-file))
            (vector->list (current-command-line-arguments)))))

(define (blodwen-system cmd)
  (if (system cmd)
      0
      1))

;; Randoms
(random-seed (date*-nanosecond (current-date))) ; initialize random seed

(define (blodwen-random-seed s) (random-seed s))
(define blodwen-random
  (case-lambda
    ;; no argument, pick a real value from [0, 1.0)
    [() (random)]
    ;; single argument k, pick an integral value from [0, k)
    [(k) (if (> k 0)
           (random k)
           (raise 'blodwen-random-invalid-range-argument))]))

;; For finalisers

(define (blodwen-register-object obj proc)
   (register-finalizer obj (lambda (ptr) ((proc ptr) 'erased)))
   obj)
(define PreludeC-45IO-prim__putStr (lambda (farg-0 farg-1) (idris2_putStr farg-0) (vector 0 )))
(define PreludeC-45IO-prim__fork (lambda (farg-0 farg-1) (blodwen-thread farg-0)))
(define System-prim__sleep (lambda (farg-0 farg-1) (idris2_sleep farg-0) (vector 0 )))
(define prim__add_Integer (lambda (arg-0 arg-1) (+ arg-0 arg-1)))
(define prim__sub_Integer (lambda (arg-0 arg-1) (- arg-0 arg-1)))
(define prim__mul_Integer (lambda (arg-0 arg-1) (* arg-0 arg-1)))
(define prim__lte_Integer (lambda (arg-0 arg-1) (or (and (<= arg-0 arg-1) 1) 0)))
(define prim__strAppend (lambda (arg-0 arg-1) (string-append arg-0 arg-1)))
(define prim__believe_me (lambda (arg-0 arg-1 arg-2) arg-2))

(define Main-dmain (lambda (ext-0) (let ((act-286 ((PreludeC-45IO-putStrLn
'erased (vector 0 (vector 0 (vector 0 (lambda (b) (lambda (a) (lambda (func)
(lambda (arg-149) (lambda (eta-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased
func arg-149 eta-0)))))) (lambda (a) (lambda (arg-482) (lambda (eta-0)
arg-482))) (lambda (b) (lambda (a) (lambda (arg-483) (lambda (arg-485) (lambda
(eta-0) (let ((act-17 (arg-483 eta-0))) (let ((act-16 (arg-485 eta-0))) (act-17
act-16))))))))) (lambda (b) (lambda (a) (lambda (arg-644) (lambda (arg-645)
(lambda (eta-0) (let ((act-24 (arg-644 eta-0))) ((arg-645 act-24) eta-0)))))))
(lambda (a) (lambda (arg-647) (lambda (eta-0) (let ((act-51 (arg-647 eta-0)))
(act-51 eta-0)))))) (lambda (a) (lambda (arg-7243) arg-7243))) "Hello") ext-0)))
(let ((act-202 (PreludeC-45IO-fork (lambda (eta-0) (Main-child eta-0)) ext-0)))
(let ((act-146 (sleep 4))) (let ((act-118 ((PreludeC-45IO-putStrLn
'erased (vector 0 (vector 0 (vector 0 (lambda (b) (lambda (a) (lambda (func)
(lambda (arg-149) (lambda (eta-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased
func arg-149 eta-0)))))) (lambda (a) (lambda (arg-482) (lambda (eta-0)
arg-482))) (lambda (b) (lambda (a) (lambda (arg-483) (lambda (arg-485) (lambda
(eta-0) (let ((act-17 (arg-483 eta-0))) (let ((act-16 (arg-485 eta-0))) (act-17
act-16))))))))) (lambda (b) (lambda (a) (lambda (arg-644) (lambda (arg-645)
(lambda (eta-0) (let ((act-24 (arg-644 eta-0))) ((arg-645 act-24) eta-0)))))))
(lambda (a) (lambda (arg-647) (lambda (eta-0) (let ((act-51 (arg-647 eta-0)))
(act-51 eta-0)))))) (lambda (a) (lambda (arg-7243) arg-7243))) "ld") ext-0)))
(sleep 5)))))))

(define Main-child (lambda (ext-0) (let ((act-24 (sleep 1))) (let ((act-25
((PreludeC-45IO-putStrLn 'erased (vector 0 (vector 0 (vector 0 (lambda (b)
(lambda (a) (lambda (func) (lambda (arg-149) (lambda (eta-0)
(PreludeC-45IO-map_Functor_IO 'erased 'erased func arg-149 eta-0)))))) (lambda
(a) (lambda (arg-482) (lambda (eta-0) arg-482))) (lambda (b) (lambda (a) (lambda
(arg-483) (lambda (arg-485) (lambda (eta-0) (let ((act-17 (arg-483 eta-0))) (let
((act-16 (arg-485 eta-0))) (act-17 act-16))))))))) (lambda (b) (lambda (a)
(lambda (arg-644) (lambda (arg-645) (lambda (eta-0) (let ((act-25 (arg-644
eta-0))) ((arg-645 act-25) eta-0))))))) (lambda (a) (lambda (arg-647) (lambda
(eta-0) (let ((act-51 (arg-647 eta-0))) (act-51 eta-0)))))) (lambda (a) (lambda
(arg-7243) arg-7243))) "Wor") ext-0))) (sleep 2)))))

(define PreludeC-45Basics-intToBool (lambda (arg-0) (let ((sc0 arg-0)) (cond ((equal? sc0 0) 1)(else 0)))))
(define PreludeC-45Basics-id (lambda (arg-0 arg-1) arg-1))
(define Builtin-believe_me (lambda (arg-0 arg-1 ext-0) ext-0))
(define PreludeC-45Types-case--prim__integerToNat-648 (lambda (arg-0 arg-1) (let ((sc0 arg-1)) (cond ((equal? sc0 0) (Builtin-believe_me 'erased 'erased arg-0)) (else 0)))))
(define PreludeC-45Types-prim__integerToNat (lambda (arg-0) (PreludeC-45Types-case--prim__integerToNat-648 arg-0 (let ((sc0 (or (and (<= 0 arg-0) 1) 0))) (cond ((equal? sc0 0) 1)(else 0))))))
(define PreludeC-45Interfaces-C-62C-62C-61 (lambda (arg-0 arg-1 arg-2 arg-3) (let ((sc0 arg-3)) (let ((e-2 (vector-ref sc0 2))) (lambda (arg-4) (lambda (arg-5) ((((e-2 'erased) 'erased) arg-4) arg-5)))))))
(define PrimIO-case--unsafePerformIO-532 (lambda (arg-0 arg-1 arg-2 arg-3) (PrimIO-unsafeDestroyWorld 'erased 'erased arg-3)))
(define PrimIO-case--caseC-32blockC-32inC-32io_bind-453 (lambda (arg-0 arg-1 arg-2 arg-3 arg-4 arg-5 arg-6 arg-7) (arg-7 arg-6)))
(define PrimIO-case--io_bind-431 (lambda (arg-0 arg-1 arg-2 arg-3 arg-4 arg-5) (PrimIO-case--caseC-32blockC-32inC-32io_bind-453 'erased 'erased 'erased 'erased 'erased arg-5 'erased (arg-3 arg-5))))
(define PrimIO-unsafePerformIO (lambda (arg-0 arg-1) (PrimIO-unsafeCreateWorld 'erased (lambda (w) (PrimIO-case--unsafePerformIO-532 'erased arg-1 'erased (arg-1 w))))))
(define PrimIO-unsafeDestroyWorld (lambda (arg-0 arg-1 arg-2) arg-2))
(define PrimIO-unsafeCreateWorld (lambda (arg-0 arg-1) (arg-1 #f)))
(define PrimIO-toPrim (lambda (arg-0 arg-1) arg-1))
(define PrimIO-io_pure (lambda (arg-0 arg-1 ext-0) arg-1))
(define PrimIO-io_bind (lambda (arg-0 arg-1 arg-2 arg-3 ext-0) (PrimIO-case--io_bind-431 'erased 'erased 'erased arg-3 'erased (arg-2 ext-0))))
(define PrimIO-fromPrim (lambda (arg-0 arg-1) arg-1))
(define PreludeC-45IO-pure_Applicative_IO (lambda (arg-0 arg-1 ext-0) arg-1))
(define PreludeC-45IO-map_Functor_IO (lambda (arg-0 arg-1 arg-2 arg-3 ext-0) (let ((act-3 (arg-3 ext-0))) (arg-2 act-3))))
(define PreludeC-45IO-liftIO_HasIO_C-36io (lambda (arg-0 arg-1 arg-2 arg-3) (let ((sc0 arg-2)) (let ((e-2 (vector-ref sc0 2))) ((e-2 'erased) arg-3)))))
(define PreludeC-45IO-liftIO1_HasLinearIO_IO (lambda (arg-0 arg-1) arg-1))
(define PreludeC-45IO-join_Monad_IO (lambda (arg-0 arg-1 ext-0) (let ((act-2 (arg-1 ext-0))) (act-2 ext-0))))
(define PreludeC-45IO-__Impl_Monad_IO (lambda () (vector 0 (vector 0 (lambda (b) (lambda (a) (lambda (func) (lambda (arg-149) (lambda (eta-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased func arg-149 eta-0)))))) (lambda (a) (lambda (arg-482) (lambda (eta-0) arg-482))) (lambda (b) (lambda (a) (lambda (arg-483) (lambda (arg-485) (lambda (eta-0) (let ((act-17 (arg-483 eta-0))) (let ((act-16 (arg-485 eta-0))) (act-17 act-16))))))))) (lambda (b) (lambda (a) (lambda (arg-644) (lambda (arg-645) (lambda (eta-0) (let ((act-24 (arg-644 eta-0))) ((arg-645 act-24) eta-0))))))) (lambda (a) (lambda (arg-647) (lambda (eta-0) (let ((act-29 (arg-647 eta-0))) (act-29 eta-0))))))))
(define PreludeC-45IO-__Impl_HasLinearIO_IO (lambda () (vector 0 (vector 0 (vector 0 (lambda (b) (lambda (a) (lambda (func) (lambda (arg-149) (lambda (eta-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased func arg-149 eta-0)))))) (lambda (a) (lambda (arg-482) (lambda (eta-0) arg-482))) (lambda (b) (lambda (a) (lambda (arg-483) (lambda (arg-485) (lambda (eta-0) (let ((act-17 (arg-483 eta-0))) (let ((act-16 (arg-485 eta-0))) (act-17 act-16))))))))) (lambda (b) (lambda (a) (lambda (arg-644) (lambda (arg-645) (lambda (eta-0) (let ((act-24 (arg-644 eta-0))) ((arg-645 act-24) eta-0))))))) (lambda (a) (lambda (arg-647) (lambda (eta-0) (let ((act-51 (arg-647 eta-0))) (act-51 eta-0)))))) (lambda (a) (lambda (arg-7272) arg-7272)))))
(define PreludeC-45IO-__Impl_HasIO_C-36io (lambda (arg-0 arg-1) (vector 0 (let ((sc0 arg-1)) (let ((e-1 (vector-ref sc0 1))) e-1)) (lambda (a) (lambda (arg-7243) (let ((sc0 arg-1)) (let ((e-2 (vector-ref sc0 2))) ((e-2 'erased) arg-7243))))))))
(define PreludeC-45IO-__Impl_Functor_IO (lambda (ext-4 ext-1 ext-2 ext-3 ext-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased ext-2 ext-3 ext-0)))
(define PreludeC-45IO-__Impl_Applicative_IO (lambda () (vector 0 (lambda (b) (lambda (a) (lambda (func) (lambda (arg-149) (lambda (eta-0) (PreludeC-45IO-map_Functor_IO 'erased 'erased func arg-149 eta-0)))))) (lambda (a) (lambda (arg-482) (lambda (eta-0) arg-482))) (lambda (b) (lambda (a) (lambda (arg-483) (lambda (arg-485) (lambda (eta-0) (let ((act-17 (arg-483 eta-0))) (let ((act-16 (arg-485 eta-0))) (act-17 act-16)))))))))))
(define PreludeC-45IO-__HasLinearIO_C-40MonadC-32ioC-41 (lambda (arg-0 arg-1) (let ((sc0 arg-1)) (let ((e-1 (vector-ref sc0 1))) e-1))))
(define PreludeC-45IO-C-62C-62C-61_Monad_IO (lambda (arg-0 arg-1 arg-2 arg-3 ext-0) (let ((act-1 (arg-2 ext-0))) ((arg-3 act-1) ext-0))))
(define PreludeC-45IO-C-60C-42C-62_Applicative_IO (lambda (arg-0 arg-1 arg-2 arg-3 ext-0) (let ((act-6 (arg-2 ext-0))) (let ((act-5 (arg-3 ext-0))) (act-6 act-5)))))
(define PreludeC-45IO-putStrLn (lambda (arg-0 arg-1 arg-2) (PreludeC-45IO-putStr 'erased arg-1 (string-append arg-2 "\u000a"))))
(define PreludeC-45IO-putStr (lambda (arg-0 arg-1 arg-2) (let ((sc0 arg-1)) (let ((e-2 (vector-ref sc0 2))) ((e-2 'erased) (lambda (eta-0) (PreludeC-45IO-prim__putStr arg-2 eta-0)))))))
(define PreludeC-45IO-primIO (lambda (arg-0 arg-1 arg-2 arg-3) (let ((sc0 arg-2)) (let ((e-2 (vector-ref sc0 2))) ((e-2 'erased) arg-3)))))
(define PreludeC-45IO-liftIO1 (lambda (arg-0 arg-1 arg-2) (let ((sc0 arg-2)) (let ((e-2 (vector-ref sc0 2))) (lambda (arg-3) ((e-2 'erased) arg-3))))))
(define PreludeC-45IO-liftIO (lambda (arg-0 arg-1 arg-2) (let ((sc0 arg-2)) (let ((e-2 (vector-ref sc0 2))) (lambda (arg-3) ((e-2 'erased) arg-3))))))
(define PreludeC-45IO-fork (lambda (arg-0 ext-0) (PreludeC-45IO-prim__fork arg-0 ext-0)))
(define System-sleep (lambda (arg-0 arg-1 arg-2) (let ((sc0 arg-1)) (let ((e-2 (vector-ref sc0 2))) ((e-2 'erased) (lambda (eta-0) (System-prim__sleep arg-2 eta-0)))))))
(void (PrimIO-unsafePerformIO 'erased (lambda (eta-0) (Main-dmain eta-0))))
) (collect-garbage)
