#lang rosette
(require "./bounded.rkt")
(require "./utils.rkt")
(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)



 (define-bounded (vector_add x y) 
(if (< (length x ) 1 ) (list-empty ) (list-prepend (+ (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vector_add (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) )) 
 
 (define-bounded (vector_sub x y) 
(if (< (length x ) 1 ) (list-empty ) (list-prepend (- (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (vector_sub (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) )) 
 
 (define-bounded (elem_mul x y) 
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* (list-ref-noerr x 0 ) (list-ref-noerr y 0 ) ) (elem_mul (list-tail-noerr x 1 ) (list-tail-noerr y 1 )) ) )) 
 
 (define-bounded (scalar_mul a x) 
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (scalar_mul a (list-tail-noerr x 1 )) ) )) 
 
 (define-bounded (scalar_add a x) 
(if (< (length x ) 1 ) (list-empty ) (list-prepend (* a (list-ref-noerr x 0 ) ) (scalar_add a (list-tail-noerr x 1 )) ) )) 

(define-grammar (test_ps_gram base active opacity test_rv)
 [rv (choose (=> (&& (equal? (length base ) (length active ) )
                     (> (length base ) 0 ) )
                 (equal? test_rv
                         ((b) ((b) (a) (a)) ((b) (a) (a))) ) ))]
    [c (choose 0 1)]
    [arith (choose - +)]
    [a (choose ((arith) (c) opacity) opacity active base)]
    [b (choose vector_add vector_sub scalar_add scalar_mul)]
) 

(define-grammar (test_inv0_gram agg.result ref.tmp i base active opacity)
 [rv (choose
    (=> (&& (equal? (length base ) (length active ) ) (> (length base ) 0 ) )
        (&& ((op) i (a) )
            ((op2) i (length active ) )
            (equal? agg.result
                ((b) ((b) (a) (a))
                    ((b) (a) (a))) ) ) ) )]

    [a (choose 0 1 2 3 opacity (- 1 opacity) (list-take-noerr active i) (list-take-noerr base i))]
    [b (choose vector_add vector_sub scalar_add scalar_mul)]
    [op (choose >= > = < <=)]
    [op2 (choose >= > = < <=)]
) 

;(define (test_inv0 agg.result ref.tmp i base active opacity)
;  (choose
;   (=>
;    (&& (equal? (length base) (length active)) (> (length base) 0))
;    (&&
;     (>= i 0)
;     (<= i (length active))
;     (equal?
;      agg.result
;      (vector_add
;       (scalar_mul opacity (list-take-noerr active i))
;       (scalar_mul (- 1 opacity) (list-take-noerr base i))))))))

(define (test_ps base active opacity test_rv) (test_ps_gram base active opacity test_rv #:depth 10))
(define (test_inv0 agg.result ref.tmp i base active opacity) (test_inv0_gram agg.result ref.tmp i base active opacity #:depth 10))

(define-symbolic active_BOUNDEDSET-0 integer?)
(define-symbolic active_BOUNDEDSET-1 integer?)
(define-symbolic active_BOUNDEDSET-len integer?)
(define active (take (list active_BOUNDEDSET-0 active_BOUNDEDSET-1) active_BOUNDEDSET-len))
(define-symbolic agg.result_BOUNDEDSET-0 integer?)
(define-symbolic agg.result_BOUNDEDSET-1 integer?)
(define-symbolic agg.result_BOUNDEDSET-len integer?)
(define agg.result (take (list agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1) agg.result_BOUNDEDSET-len))
(define-symbolic base_BOUNDEDSET-0 integer?)
(define-symbolic base_BOUNDEDSET-1 integer?)
(define-symbolic base_BOUNDEDSET-len integer?)
(define base (take (list base_BOUNDEDSET-0 base_BOUNDEDSET-1) base_BOUNDEDSET-len))
(define-symbolic i integer?)
(define-symbolic opacity integer?)
(define-symbolic ref.tmp integer?)
(define-symbolic test_rv_BOUNDEDSET-0 integer?)
(define-symbolic test_rv_BOUNDEDSET-1 integer?)
(define-symbolic test_rv_BOUNDEDSET-len integer?)
(define test_rv (take (list test_rv_BOUNDEDSET-0 test_rv_BOUNDEDSET-1) test_rv_BOUNDEDSET-len))
(current-bitwidth 6)
(define (assertions)
 (assert (&& (test_inv0 (list-empty ) 0 0 base active opacity) (=> (&& (< i (length base ) ) (test_inv0 agg.result ref.tmp i base active opacity) ) (test_inv0 (list-append agg.result (+ (* opacity (list-ref-noerr active i ) ) (* (- 1 opacity ) (list-ref-noerr base i ) ) ) ) (+ (* opacity (list-ref-noerr active i ) ) (* (- 1 opacity ) (list-ref-noerr base i ) ) ) (+ i 1 ) base active opacity) ) (=> (or (&& (! true ) (! (< i (length base ) ) ) (test_inv0 agg.result ref.tmp i base active opacity) ) (&& (! (< i (length base ) ) ) (test_inv0 agg.result ref.tmp i base active opacity) ) ) (test_ps base active opacity agg.result) ) )))

(define sol
 (synthesize
 #:forall (list active_BOUNDEDSET-0 active_BOUNDEDSET-1 active_BOUNDEDSET-len agg.result_BOUNDEDSET-0 agg.result_BOUNDEDSET-1 agg.result_BOUNDEDSET-len base_BOUNDEDSET-0 base_BOUNDEDSET-1 base_BOUNDEDSET-len i opacity ref.tmp test_rv_BOUNDEDSET-0 test_rv_BOUNDEDSET-1 test_rv_BOUNDEDSET-len)
 #:guarantee (assertions)))
 (sat? sol)
 (print-forms sol)
