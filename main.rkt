#lang plait

(module+ test
  (print-only-errors #t))

(define-type Def
  (def [d : (Listof Fun)] [e : Exp]))

(define-type Fun
  (fun [f : Symbol] [xs : (Listof Symbol)] [e : Exp]))



(define-type Exp
  (numE [n : Number])
  (varE [x : Symbol])
  (ifzE [b : Exp] [l : Exp] [r : Exp])
  (letE [x : Symbol] [e1 : Exp] [e2 : Exp])
  (fE [x : Symbol] [le : (Listof Exp)])
  (opE [e1 : Exp] [x : Symbol] [e2 : Exp] ))



(define (check-dn-fun l s)
  (if (empty? l)
      #t
      (let ([x (fun-f (first l))])
        (if (member x s)
            #f
            (check-dn-fun (rest l) (cons x s))))))


(define (parse [s : S-Exp]) : Def
  (cond
    [(s-exp-match? `{define {ANY ...} for ANY} s)
     (let ([funct (map (lambda (x) (parse-Fun x)) (s-exp->list ( second (s-exp->list s))))])
       (if (check-dn-fun funct '())
           (def  funct (parse-Exp (fourth (s-exp->list s))))
           (error 'parse "Duplicate function names")))]
    [else (error 'parse "Wrong define structure")]))


(define (parse-Exp [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s)
     (numE (s-exp->number s))]
    [(s-exp-match? `{ifz ANY then ANY else ANY} s)
     (ifzE (parse-Exp (second (s-exp->list s)))
          (parse-Exp (fourth (s-exp->list s)))
          (parse-Exp (list-ref (s-exp->list s) 5)))]
    [(s-exp-match? `SYMBOL s)
     (varE (s-exp->symbol s))]
    [(s-exp-match? `{let SYMBOL be ANY in ANY} s)
     (letE (s-exp->symbol (second (s-exp->list s)))
           (parse-Exp (fourth (s-exp->list s)))
           (parse-Exp (list-ref (s-exp->list s) 5)))]
    [(s-exp-match? `{SYMBOL {ANY ...}} s)
     (fE (s-exp->symbol (first (s-exp->list s)))
         (map (lambda (x) (parse-Exp x)) (s-exp->list (second (s-exp->list s)))))]
    [(s-exp-match? `{ANY SYMBOL ANY} s)
     (opE (parse-Exp (first (s-exp->list s)))
                 (parse-Op (s-exp->symbol (second (s-exp->list s))))
                 (parse-Exp (third (s-exp->list s))))]
    [else (error 'parse-Exp "Wrong expression structure")]))

(define (map-func-args f l)
  (if (empty? l)
      '()
      (let ([x (f (first l))]
            [lp (map-func-args f (rest l))])
        (if (member x lp)
            (error 'parse "Duplicate function arguments")
            (cons x lp)))))

(define (parse-Fun [s : S-Exp]) : Fun
  (if (s-exp-match? `{fun SYMBOL {SYMBOL ...} = ANY} s)
      (fun (s-exp->symbol (second (s-exp->list s)))
           (map-func-args (lambda (x) (s-exp->symbol x)) (s-exp->list (third (s-exp->list s))))
           (parse-Exp (list-ref (s-exp->list s) 4)))
      (error 'parse-Fun "Wrong function structure")))


(define prim-ops '(+ - * <=))

(define (parse-Op [op : Symbol]) : Symbol
  (if (member op prim-ops)
      op 
      (error 'parse "unknown operator")))


;Eval 
;============================================================================================================

(define-type-alias Value Number)

(define-type Val
  (numV [n : Number])
  (primopV [f : (Val Val -> Val)])
  (fundefV [xs : (Listof Symbol)] [body : Exp])
  )

;; environments

(define-type Binding
  (bind [name : Symbol]
        [val : Val]))

(define-type-alias Env (Listof Binding))

(define-type Env-list
  (en [fun : Env]
       [prim : Env]
       [body : Env]))


(define mt-env empty)


(define (extend-env [env : Env] [x : Symbol] [t : Val]) : Env
  (cons (bind x t) env))


(define (extend-env-l-help [env-new : Env-list] [env-old : Env-list] [xs : (Listof Symbol)] [ts : (Listof Exp)]) : Env-list
  (if (empty? xs)
      env-new
      (extend-env-l-help (en (en-fun env-new) (en-prim env-new) (cons (bind (first xs) (eval (first ts) env-old)) (en-body env-new))) env-old (rest xs) (rest ts))))


(define (extend-env-l [env : Env-list] [xs : (Listof Symbol)] [ts : (Listof Exp)]) : Env-list
  (if (= (length xs) (length ts))
      (extend-env-l-help (en (en-fun env) (en-prim env) mt-env) env xs ts)
      (error 'extend-env-l "(Listof Symbol) != (Listof Val)")))


(define (lookup-env [n : Symbol] [env : Env] ) : Val
  (type-case (Listof Binding) env
    [empty (error 'lookup "unbound variable")]
    [(cons b rst-env) (cond
                        [(eq? n (bind-name b))
                         (bind-val b)]
                        [else (lookup-env n rst-env)])]))


;; primitive operations

(define (op-num-num->value [f : (Number Number -> Number)]) : Val
  (primopV
   (λ (v1 v2)
     (type-case Val v1
       [(numV n1)       
        (type-case Val v2
          [(numV n2)
           (numV (f n1 n2))]
          [else
           (error 'eval "type error")])]
       [else
        (error 'eval "type error")]))))


(define (m<= x y)
  (if (<= x y)
      0
      1))

(define init-env 
  (foldr (λ (b env) (extend-env env (fst b) (snd b)))
         mt-env 
         (list (pair '+ (op-num-num->value +))
               (pair '- (op-num-num->value -))
               (pair '* (op-num-num->value *))
               (pair '<= (op-num-num->value m<=)))))



(define (eval [e : Exp] [env : Env-list]) : Val
  (type-case Exp e
    [(numE n) (numV n)]
    [(ifzE b l r)
     (type-case Val (eval b env)
       [(numV v)
        (if (= v 0) (eval l env) (eval r env))]
       [else
        (error 'eval "type error")])]
    [(varE x)
     (lookup-env x (en-body env))]
    [(letE x e1 e2)
     (let ([v1 (eval e1 env)])
       (eval e2 (en (en-fun env) (en-prim env) (extend-env (en-body env) x v1))))]
    [(fE f el) (eval-f f el env)]
    [(opE e1 s e2) (eval-op e1 s e2 env)]
    ))

(define (eval-op [e1 : Exp] [s : Symbol] [e2 : Exp] [env : Env-list])
  (type-case Val (lookup-env s (en-prim env))
    [(primopV f) (f (eval e1 env) (eval e2 env))]
    [else (error 'eval-op "Can't use as primary operator")]))


(define (eval-f [f : Symbol] [el : (Listof Exp)] [env : Env-list]) : Val
  (type-case Val (lookup-env f (en-fun env))
    [(fundefV xs body) (eval body (extend-env-l env xs el))]
    [else (error 'eval-f "Can't evaluate as function")]))

  


(define (eval-fun [f : (Listof Fun)] [env : Env]) : Env
  (if (empty? f)
      env
      (type-case Fun (first f)
        [(fun s xs e1) (eval-fun (rest f) (extend-env env s (fundefV xs e1)))])))


(define (eval-def [e : Def] [env : Env]) : Val 
  (type-case Def e
    [(def d e1) (eval e1 (en (eval-fun d mt-env) init-env mt-env))])) 
  


(define (run [s : S-Exp]) : Value
  (type-case Val (eval-def (parse s) init-env)
    [(numV n) n]
    [else (error 'run "Value was not a number")]))




