#lang typed/racket
;; written by ryanc, typed by ianj
(provide
 gvector?
 (rename-out [gvector* gvector])
 make-gvector
 gvector-ref
 gvector-set!
 gvector-add!
 gvector-remove!
 gvector-remove-last!
 gvector-count
 gvector->vector
 gvector->list
 gvector=?
 (rename-out [in-gvector* in-gvector])
 for/gvector
 for*/gvector
 GVectorof)
(require (for-syntax racket/base
                     unstable/wrapc
                     syntax/for-body))

(define-type (GVectorof A) (gvector A))
(: make-gvector : (All (A) (-> A [#:capacity Integer] (GVectorof A))))
(define (make-gvector default #:capacity [capacity 10])
  (gvector (make-vector capacity default) default 0))

(: gvector* : (All (A) (-> A A * (GVectorof A))))
(define (gvector* i0 . init-elements)
  (define gv (make-gvector i0))
  (apply gvector-add! gv init-elements)
  gv)

(: check-index : (-> Symbol Integer Index Boolean Void))
(define (check-index who index n set-to-add?)
  (unless (< index n)
    (error who "index out of range ~a~a: ~s"
           (let ([max-index (if set-to-add? (- n 2) (- n 1))])
             (cond [(< max-index 0) "(empty)"]
                   [else (format "[0,~s]" max-index)]))
           (if set-to-add?
               (format " or ~s to add" (- n 1))
               "")
           index)))

(: check-nonempty : (-> Symbol Real Void : #:+ (Positive-Real @ 1) #:- (Positive-Real @ 1)))
(define (check-nonempty who n)
  (unless (> n 0)
    (error who "empty")))

(: bad-index-error : (-> Symbol Integer (-> Nothing)))
(define ((bad-index-error who index))
  (raise-mismatch-error who "index out of range" index))

(: gvector-add! : (All (A) (-> (GVectorof A) A * Void)))
(define (gvector-add! gv . items)
  (let ([n : Index ((inst gvector-n A) gv)]
        [v : (Vectorof A) ((inst gvector-vec A) gv)]
        [item-count : Index (length items)])
    (cond [(<= (+ n item-count) (vector-length v))
           (for ([index (in-naturals n)]
                 [item (in-list items)])
             ((inst vector-set! A) v index item))
           ((inst set-gvector-n! A) gv (cast (+ n item-count) Index))]
          [else
           (let* ([nn (let loop : Index ([nn : Index n])
                        (if (<= (+ n item-count 1) nn)
                            nn
                            (loop (cast (* 2 nn) Index))))]
                  [nv (make-vector nn (gvector-default gv))])
             ((inst vector-copy! A) nv 0 v)
             (for ([index (in-naturals n)] [item (in-list items)])
               (vector-set! nv index item))
             ((inst set-gvector-vec! A) gv nv)
             ((inst set-gvector-n! A) gv (cast (+ n item-count) Index)))])))

(define SHRINK-MIN 10)

;; SLOW!
(: gvector-remove! : (All (A) (-> (GVectorof A) Integer Void)))
(define (gvector-remove! gv index)
  (let ([n (gvector-n gv)]
        [v (gvector-vec gv)])
    (check-index 'gvector-remove! index n #f)
    (cond [(<= SHRINK-MIN (* 3 n) (vector-length v))
           (let ([nv (make-vector (floor (/ (vector-length v) 2)) (gvector-default gv))])
             (vector-copy! nv 0 v 0 index)
             (vector-copy! nv index v (add1 index) n)
             (set-gvector-n! gv (cast (sub1 n) Index))
             (set-gvector-vec! gv nv))]
          [else
           (set-gvector-n! gv (cast (sub1 n) Index))
           (vector-copy! v index v (add1 index) n)
           (vector-set! v (sub1 n) (gvector-default gv))])))

(: gvector-remove-last! : (All (A) (-> (GVectorof A) A)))
(define (gvector-remove-last! gv)
  (let ([n (gvector-n gv)]
        [v (gvector-vec gv)])
    (check-nonempty 'gvector-remove-last! n)
    (define last-val (vector-ref v (sub1 n)))
    (set-gvector-n! gv (cast (sub1 n) Index))
    (vector-set! v (sub1 n) (gvector-default gv))
    last-val))

(: gvector-count : (All (A) (-> (GVectorof A) Index)))
(define (gvector-count gv)
  (gvector-n gv))

(: gvector-ref : (All (A) (->* ((GVectorof A) Integer) [(-> Nothing)] A)))
(define (gvector-ref gv index
                     [default (bad-index-error 'gvector-ref index)])
  (if (< index (gvector-n gv))
      (vector-ref (gvector-vec gv) index)
      (if (procedure? default)
          (default)
          default)))

(: gvector=? : (All (A B) (-> (GVectorof A) (GVectorof B) Boolean)))
(define (gvector=? g0 g1)
  (match-define (gvector v0 _ n0) g0)
  (match-define (gvector v1 _ n1) g1)
  (and (= n0 n1)
       (for/and ([v0 (in-vector v0)]
                 [v1 (in-vector v1)]
                 [i (in-range n0)])
         (equal? v0 v1))))

;; gvector-set! with index = |gv| is interpreted as gvector-add!
(: gvector-set! : (All (A) (-> (GVectorof A) Integer A Void)))
(define (gvector-set! gv index item)
  (let ([n (gvector-n gv)])
    (check-index 'gvector-set! index (cast (add1 n) Index) #t)
    (if (= index n)
        (gvector-add! gv item)
        (vector-set! (gvector-vec gv) index item))))

;; creates a snapshot vector
(: gvector->vector : (All (A) (-> (GVectorof A) (Vectorof A))))
(define (gvector->vector gv)
  (vector-copy (gvector-vec gv) 0 (gvector-n gv)))

(: gvector->list : (All (A) (-> (GVectorof A) (Listof A))))
(define (gvector->list gv)
  (vector->list (gvector->vector gv)))

;; Iteration methods

;; A gvector position is represented as an exact-nonnegative-integer.

(: gvector-iterate-first : (All (A) (-> (GVectorof A) (Option Index))))
(define (gvector-iterate-first gv)
  (and (positive? (gvector-n gv)) 0))

(: gvector-iterate-next : (All (A) (-> (GVectorof A) Index (Option Index))))
(define (gvector-iterate-next gv iter)
  (check-index 'gvector-iterate-next iter (gvector-n gv) #f)
  (define n (gvector-n gv))
  (define i* (add1 iter))
  (and (< i* n) i*))

(: gvector-iterate-key : (All (A) (-> (GVectorof A) Index Index)))
(define (gvector-iterate-key gv iter)
  (check-index 'gvector-iterate-key iter (gvector-n gv) #f)
  iter)

(: gvector-iterate-value : (All (A) (-> (GVectorof A) Index A)))
(define (gvector-iterate-value gv iter)
  (check-index 'gvector-iterate-value iter (gvector-n gv) #f)
  (gvector-ref gv iter))

(: in-gvector : (All (A) (-> (GVectorof A) (Sequenceof A))))
(define (in-gvector gv)
  (define v (gvector-vec gv))
  (define n (gvector-n gv))
  ((inst make-do-sequence Index A)
   (λ ()
      (values (λ ([i : Index]) (vector-ref v i))
              (λ ([i : Index]) (cast (add1 i) Index))
              0
              (λ ([i : Index]) (< i n)) #f #f))))

(define-sequence-syntax in-gvector*
  (lambda () #'in-gvector)
  (lambda (stx)
    (syntax-case stx ()
      [[(var) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var)
            (:do-in ([(gv) gv-expr-c])
                    (void) ;; outer-check; handled by contract
                    ([index 0] [vec (gvector-vec gv)] [n (gvector-n gv)]) ;; loop bindings
                    (< index n) ;; pos-guard
                    ([(var) (vector-ref vec index)]) ;; inner bindings
                    #t ;; pre-guard
                    #t ;; post-guard
                    ((add1 index) (gvector-vec gv) (gvector-n gv)))]))]
      [[(var ...) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var ...) (in-gvector gv-expr-c)]))]
      [_ #f])))

(define-syntax (for/gvector stx)
  (syntax-case stx ()
    [(_ default (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector default)])
           (for/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
              (lambda args (apply gvector-add! gv args) (values))))
           gv)))]))

(define-syntax (for*/gvector stx)
  (syntax-case stx ()
    [(_ default (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector default)])
           (for*/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
              (lambda args (apply gvector-add! gv args) (values))))
           gv)))]))

(struct (A) gvector ([vec : (Vectorof A)]
                     [default : A]
                     [n : Index]) #:mutable)

