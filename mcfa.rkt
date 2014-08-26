#lang typed/racket
(require "gvector.rkt")
(define-type Counter (case-> (-> Exact-Nonnegative-Integer)
                             (-> Exact-Nonnegative-Integer Exact-Nonnegative-Integer)))
(: counter : (-> Counter))
(define (counter)
  (: c : (Boxof Exact-Nonnegative-Integer))
  (define c (box 0))
  (case-lambda [() (unbox c)]
               [(n)
                (define res (unbox c))
                (set-box! c (+ n res))
                res]))

;; Surface
(struct ref ([x : Symbol]) #:transparent)
(struct app ([fn : Expr] [args : (Listof Expr)]) #:transparent)
(struct lam ([xs : (Listof Symbol)] [body : Expr]) #:transparent)
(define-type Expr (U ref app lam))

;; IR
(define-type Name (HashTable Contour Index))
(: mk-name : (-> Name))
(define (mk-name) ((inst make-hash Contour Index)))
(struct expr ([fv : (Setof Name)]))
(struct ref* expr ([x : Name]))
(struct app* expr ([ℓ : Label] [κa : Name]
                   [fn : Expr*] [fna : Name]
                   [args : (Vectorof Expr*)]
                   [argas : (Vectorof Name)]))
(struct lam* expr ([xs : (Vectorof Name)] [body : Expr*]))
(define-type Expr* (U ref* app* lam*))
(define-type CExpr (-> Kont Contour Void))
;; Closures, continuations and frames are callable to do their task.

(struct *unmapped ()) (define unmapped (*unmapped))

(struct clam ([xs : (Vectorof Name)]
              [body : CExpr]
              [fv : (Setof Name)])) ;; sealed for pointer equality only
(struct clos ([clam : clam] [ρ : Contour]) #:transparent)
(define-type Value (U clos Index))

(define m 1)
(define-type Label Index)
;(define-type Contour #f) ;; m = 0
(define-type Contour (U #f Label)) ;; m = 1
;(define-type Contour (Vectorof #f Label)) ;; m > 1
(define-type AbsVal Exact-Nonnegative-Integer)

(: mt : (-> Value Contour Void))
(define mt (λ (v t) (add-final! v)))
(struct kcons ([φ : Frame] [t : Contour] [κ : Kont]) #:transparent)
(struct kev ([arga : Name] [next : CExpr]))
(define-type Frame (U kev))
(define-type Kont (U kcons (-> Value Contour Void) Index))

(struct co ([κ : Kont] [v : Value] [t : Contour]) #:transparent)
(struct ap ([body : CExpr] [κ : Kont] [t : Contour]) #:transparent)
(define-type State (U co ap))

(define unit? (zero? m))
(: t₀ : Contour)
(: tick : (-> Label Contour Contour))
(define-values (t₀ tick)
  (cond
   [(eq? 0 m) (values #f (λ (ℓ t) t))]
   [(eq? 1 m) (values #f (λ (ℓ t) ℓ))]
   [else
    (error 'tick "Fix type for Contour")
    #;
    (values (make-vector m #f)
                 (λ (ℓ t)
                    (define t* (make-vector m ℓ))
                    (for ([ℓ* (in-vector t)]
                          [i (in-range 1 m)])
                      (vector-set! t* i ℓ*))
                    t*))]))

(: default-value : Value)
(define default-value
  (clos (clam (vector) (λ (κ t) (error 'default)) (seteq)) t₀))

(: nothing : AbsVal)
(define nothing 0)
(: registrar : (HashTable Value AbsVal))
(define registrar (make-hash))
(: registrar2 : (HashTable Kont AbsVal))
(define registrar2 (make-hash))
(: backtrans : (GVectorof Value))
(define backtrans ((inst make-gvector Value) default-value))
(: backtrans2 : (GVectorof Kont))
(define backtrans2 ((inst make-gvector Kont) mt))
(: start : (-> Index Void))
(define (start size)
  (set! registrar ((inst make-hash Value AbsVal)))
  (set! backtrans ((inst make-gvector Value) default-value #:capacity size))
  (set! registrar2 ((inst make-hash Kont AbsVal)))
  (set! backtrans2 ((inst make-gvector Kont) mt #:capacity size)))
(: singleton : (-> Value AbsVal))
(define (singleton v)
  (or (hash-ref registrar v #f)
      (let ([n (arithmetic-shift 1 (hash-count registrar))])
        (hash-set! registrar v n)
        (gvector-add! backtrans v)
        n)))
(: singleton2 : (-> Kont AbsVal))
(define (singleton2 v)
  (or (hash-ref registrar2 v #f)
      (let ([n (arithmetic-shift 1 (hash-count registrar2))])
        (hash-set! registrar2 v n)
        (gvector-add! backtrans2 v)
        n)))
(: ⊔/Δ? : (-> AbsVal AbsVal (Values AbsVal Boolean)))
(define (⊔/Δ? S S*)
  (define new (bitwise-ior S S*))
  (if (= S new)
      (values S #f)
      (values new #t)))
(: step : (-> AbsVal (Values Value AbsVal)))
(define (step i)
  (define bit (sub1 (integer-length i)))
  (values (gvector-ref backtrans bit)
          (bitwise-xor i (arithmetic-shift 1 bit))))
(: step2 : (-> AbsVal (Values Kont AbsVal)))
(define (step2 i)
  (define bit (sub1 (integer-length i)))
  (values (gvector-ref backtrans2 bit)
          (bitwise-xor i (arithmetic-shift 1 bit))))
(: *in-absval : (-> AbsVal (Sequenceof Value)))
(define (*in-absval e)
  (if (= 0 e)
      empty-sequence
      ((inst make-do-sequence AbsVal Value)
       (λ ()
          (values (λ ([i : AbsVal]) (gvector-ref backtrans (sub1 (integer-length i))))
                  (λ (i)
                     (bitwise-xor i
                                  (arithmetic-shift 1 (sub1 (integer-length i)))))
                  e
                  (λ ([i : AbsVal]) (< 0 i)) #f #f)))))
(: *in-absval2 : (-> AbsVal (Sequenceof Kont)))
(define (*in-absval2 e)
  (if (= 0 e)
      empty-sequence
      ((inst make-do-sequence AbsVal Kont)
       (λ ()
          (values (λ ([i : AbsVal]) (gvector-ref backtrans2 (sub1 (integer-length i))))
                  (λ (i)
                     (bitwise-xor i
                                  (arithmetic-shift 1 (sub1 (integer-length i)))))
                  e
                  (λ ([i : AbsVal]) (< 0 i)) #f #f)))))
(: ⊔1/Δ? : (-> AbsVal Value (Values AbsVal Boolean)))
(define (⊔1/Δ? S v) (⊔/Δ? S (singleton v)))
(: k⊔1/Δ? : (-> AbsVal Kont (Values AbsVal Boolean)))
(define (k⊔1/Δ? S κ) (⊔/Δ? S (singleton2 κ)))
(define-sequence-syntax in-absval
  (λ () #'*in-absval)
  (λ (stx)
     (syntax-case stx ()
       [[(v) (_ abs)]
        #'[(v)
           (:do-in ([(a) abs])
                   (void)
                   ([i a])
                   (< 0 i)
                   ([(v i*) (step i)])
                   #t #t (i*))]])))
(define-sequence-syntax in-absval2
  (λ () #'*in-absval2)
  (λ (stx)
     (syntax-case stx ()
       [[(v) (_ abs)]
        #'[(v)
           (:do-in ([(a) abs])
                   (void)
                   ([i a])
                   (< 0 i)
                   ([(v i*) (step2 i)])
                   #t #t (i*))]])))

(define-type Store (GVectorof AbsVal))
(: σ : Store)
(define σ (make-gvector nothing))
(: kσ : Store)
(define kσ (make-gvector nothing))
(: addr : (-> Name Contour Index))
(define (addr h t)
  (or (hash-ref h t #f)
      (let ([n (gvector-count σ)])
        (hash-set! h t n)
        (gvector-add! σ nothing)
        n)))
(: kaddr : (-> Name Contour Index))
(define (kaddr h t)
  (or (hash-ref h t #f)
      (let ([n (gvector-count kσ)])
        (hash-set! h t n)
        (gvector-add! kσ nothing)
        n)))
(: σt : Counter)
(define σt (counter))
(: Δ? : Boolean)
(define Δ? #f)
(: S : (HashTable State Exact-Nonnegative-Integer))
(define S (make-hash))
(: F : (Boxof (Listof State)))
(define F (box '()))
(define-type Finals (HashTable Value #t))
(: Final : Finals)
(define Final (make-hash))
(: add-final! : (-> Value Void))
(define (add-final! c) (hash-set! Final c #t))

(: store-ref : (-> Store Index AbsVal))
(define (store-ref s idx) (gvector-ref s idx))
(: store-add! : (-> Index Value Void))
(define (store-add! idx v)
    (define cur (gvector-ref σ idx))
    (define-values (new Δ?*)
      (if (exact-integer? v)
          (⊔/Δ? cur (store-ref σ v))
          (⊔1/Δ? cur v)))
    (when Δ?*
      (set! Δ? #t)
      (gvector-set! σ idx new)))
(: kstore-add! : (-> Index Kont Void))
(define (kstore-add! idx v)
    (define cur (gvector-ref kσ idx))
    (define-values (new Δ?*)
      (if (exact-integer? v)
          (⊔/Δ? cur (store-ref kσ v))
          (k⊔1/Δ? cur v)))
    (when Δ?*
      (set! Δ? #t)
      (gvector-set! kσ idx new)))
(: store-join! : (-> Store Index AbsVal Void))
(define (store-join! s idx vs)
  (define cur (gvector-ref s idx))
  (define-values (new Δ?*) (⊔/Δ? cur vs))
  (when Δ?*
    (set! Δ? #t)
    (gvector-set! s idx new)))

(: add-state! : (-> State Void))
(define (add-state! c)
  (define σt* (σt))
  (define σt** (if Δ? (add1 σt*) σt*))
  (cond
   [(= (hash-ref S c (λ () -1)) σt**)
    (void)]
   [else
    (hash-set! S c σt**)
    (set-box! F (cons c (unbox F)))]))

(: bind : (-> (Vectorof Name) (Vectorof Name) Contour Contour Value Label Void))
(define (bind xs argas t* t fnv ℓ)
  (unless (= (vector-length xs) (vector-length argas))
    (log-info (format "Arity mismatch when calling ~a on ~a:~a" fnv ℓ argas)))
  (for ([x (in-vector xs)]
        [arga (in-vector argas)])
    ;; Bypass store-ref since we know that it will catch up by the ap processing
    (store-join! σ (addr x t*) (store-ref σ (addr arga t)))))

(: do-clos : (-> Value Label (Vectorof Name) Kont Contour Void))
(define do-clos
  (if unit?
      (match-lambda**
       [((and fnv (clos (clam xs body _) ρ)) ℓ argas κ t)
        (bind xs argas t t fnv ℓ)
        (add-state! (ap body κ t))])
      (match-lambda**
       [((and fnv (clos (clam xs body fv) ρ)) ℓ argas κ t)
        (define t* (tick ℓ t))
        (for ([x (in-set fv)])
          (store-join! σ (addr x t*) (store-ref σ (addr x ρ))))
        (bind xs argas t* t fnv ℓ)
        (add-state! (ap body κ t*))])))

(: do-φ : (-> Frame Kont Value Contour Void))
(define (do-φ φ κ v t)
  (match φ
    [(kev arga next)
     (store-add! (addr arga t) v)
     (next κ t)]))
(: do-κ : (-> Kont Value Contour Void))
(define (do-κ κ v t)
  (match κ
    [(kcons φ t κ) (do-φ φ κ v t)]
    [_ (mt v t)]))

(: step-state : (-> State Void))
(define (step-state c)
  (match c
    [(co κ v t)
     (match κ
       [(? exact-integer? i)
        (for ([κ (in-absval2 (store-ref kσ i))])
          (do-κ κ v t))]
       [κ (do-κ κ v t)])]
    [(ap body κ t) (body κ t)]))

(: aval : (-> Expr (Values Finals Store)))
(define (aval e)
  (define-values (e* n) (numbering e))
  (start (cast n Index))
  ;; var/location ↦ contour ↦ absval
  (set! σ ((inst make-gvector AbsVal) nothing #:capacity n))
  (set! kσ ((inst make-gvector AbsVal) nothing #:capacity n))
  (set! σt (counter))
  (set! Final ((inst make-hash Value #t)))
  (set-box! F '())

  (set! S ((inst make-hash State Exact-Nonnegative-Integer)))
  ((compile e*) mt t₀)
  (: run (-> Void))
  (define (run)
    (define F* (unbox F))
    (cond [(pair? F*)
           (set-box! F '())
           (set! Δ? #f)
           (for ([c (in-list F*)]) (step-state c))
           (when Δ? (σt 1))
           (run)]))
  (run)
  (values Final σ))

(: compile : (-> Expr* CExpr))
(define (compile e)
  (match e
    [(ref* fv x) (λ (κ t) (add-state! (co κ (addr x t) t)))]
    [(app* fv ℓ κa fn fna args argas)
     (define n (vector-length args))
     (define args* ((inst build-vector Expr*) n (λ ([i : Index]) (vector-ref args (- n i 1)))))
     (define argas* ((inst build-vector Name) n (λ ([i : Index]) (vector-ref argas (- n i 1)))))
     (: last : CExpr)
     (define last
       (λ (κ t)
          (define κidx (kaddr κa t))
          (kstore-add! κidx κ)
          (for ([v (in-absval (store-ref σ (addr fna t)))])
            (do-clos v ℓ argas κidx t))))
     (: fnc : CExpr)
     (define fnc
       (for/fold ([next : CExpr last])
            ([arg (in-vector args*)]
             [arga (in-vector argas*)])
          (define a* (compile arg))
          (define φ (kev arga next))
          (λ (κ t) (a* (kcons φ t κ) t))))
     (define fnφ (kev fna fnc))
     (define fn* (compile fn))
     (λ (κ t)
        (fn* (kcons fnφ t κ) t))]
    [(lam* fv xs body)
     (define clamv (clam xs (compile body) fv))
     (λ (κ t)
        (add-state! (co κ (clos clamv t) t)))]))

;; Surface -> IR
(: default-expr* : Expr*)
(define default-expr* (ref* (seteq) (mk-name)))
(: numbering : (-> Expr (Values Expr* Exact-Nonnegative-Integer)))
(define (numbering e)
  (define n! (counter))
  (define-type Renaming (HashTable Symbol Name))
  (: rename : (-> Renaming Symbol (Values Renaming Name)))
  (define (rename ρ x)
    (: x* : Name)
    (define x* (mk-name))
    (n! 1)
    (values (hash-set ρ x x*) x*))
  (: rename* : (-> Renaming (Listof Symbol) (Values Renaming (Vectorof Name))))
  (define (rename* ρ xs)
    (: xs* : (Vectorof Name))
    (define xs* (make-vector (length xs) (mk-name)))
    (: ρ* : Renaming)
    (define ρ*
      (for/fold ([ρ : Renaming ρ])
          ([x (in-list xs)]
           [i (in-naturals)])
        (define-values (ρ* x*) (rename ρ x))
        ((inst vector-set! Name) xs* i x*)
        ρ*))
    (values ρ* xs*))
  (: loop : (-> Expr Renaming Expr*))
  (define (loop e ρ)
    (: loop* : (-> Expr Expr*))
    (define (loop* e) (loop e ρ))
    (match e
      [(ref x)
       (define x* (hash-ref ρ x))
       (ref* (seteq x*) x*)]
      [(app fn args)
       (define n (length args))
       (define ℓ (cast (n! (+ 2 n)) Index))
       (define fn* (loop* fn))
       (: args* : (Vectorof Expr*))
       (define args* (make-vector n default-expr*))
       (for ([a (in-list args)] [i (in-naturals)]) (vector-set! args* i (loop* a)))
       (: argas : (Vectorof Name))
       (define argas (build-vector n (λ _ (mk-name))))
       (define fv (for/fold ([S : (Setof Name) (expr-fv fn*)])
                      ([a (in-vector args*)])
                    (set-union S (expr-fv a))))
       (app* fv ℓ (mk-name) fn* (mk-name) args* argas)]
      [(lam xs body)
       (define-values (ρ* xs*) (rename* ρ xs))
       (: xs** : (Setof Name))
       (define xs** (for/fold ([r : (Setof Name) (seteq)])
                        ([x* (in-vector xs*)])
                      (set-add r x*)))
       (define body* (loop body ρ*))
       (lam* (set-subtract (expr-fv body*) xs**) xs* body*)]))
  (values (loop e #hash()) (n!)))


;; File -> surface
(: file->surface : (-> String Expr))
(define (file->surface file)
  (sexp->surface (with-input-from-file file read)))

(: sexp->surface : (-> Any Expr))
(define (sexp->surface sexp)
  (match sexp
    [(? symbol? x) (ref x)]
    [`(,(or 'lambda 'λ) (,(? symbol? x)) ,body) (lam (list x) (sexp->surface body))]
    [`(,e . ,(? list? es)) (app (sexp->surface e) (map sexp->surface es))]
    [_ (error 'barf)]))

(time (call-with-values (λ () (aval (file->surface "mini-church.sch"))) list))
