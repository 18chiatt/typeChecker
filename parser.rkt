#lang plait
(print-only-errors #t)
(define-type Expr
  (num [n : Number])
  (id [x : Symbol])
  (bool [b : Boolean])
  (bin-num-op [op : (Number Number -> Number)] [lhs : Expr] [rhs : Expr])
  (iszero [e : Expr])
  (bif [test : Expr] [then : Expr] [else : Expr])
  (with [bound-x : Symbol] [bound-body : Expr] [body : Expr])
  (fun [arg-x : Symbol]
       [arg-type : Type]
       [body : Expr]
       [body-type : Type])
  (app [fun : Expr] [arg : Expr])
  (nempty)
  (ncons [first : Expr] [rest : Expr])
  (nfirst [e : Expr])
  (nrest [e : Expr])
  (isnempty [e : Expr]))

(define-type Type
  (t-num)
  (t-bool)
  (t-nlist)
  (t-fun [arg : Type] [result : Type]))
(define-type Gamma
  (mtEnv)
  (notMtEnv [id : Symbol] [theType : Type] [rest : Gamma]))





(define (getArg sexp n) (list-ref (s-exp->list sexp) n))
(define (parseNth sexp n) (parse (getArg sexp n)))
(define (getSymbol expr) (s-exp->symbol (list-ref (s-exp->list expr) 0)))
(define (getBoundExpr expr ) (list-ref (s-exp->list expr) 1))

(define (getFunArgType expr) (parseType (getArg expr 2)))
(define (parseType expr)
  (cond
    [(s-exp-match? `number expr) (t-num)]
    [(s-exp-match? `boolean expr) (t-bool)]
    [(s-exp-match? `nlist expr) (t-nlist)]
    [(s-exp-match? `(ANY -> ANY) expr) (t-fun (parseType (getArg expr 0)) (parseType (getArg expr 2)))]
    [else 
            (error 'parse (string-append "Unable to identify type" (to-string expr)))]))


(define (plus x y) (+ x y))
(define (minus x y) (- x y))
(define (mult x y) (* x y))

(define (parse expr)
  (cond
    [(s-exp-match? `NUMBER expr ) (num (s-exp->number expr))]
    [(s-exp-match? `true expr) (bool #t)]
    [(s-exp-match? `false expr) (bool #f)]
    [(s-exp-match? `empty expr) (nempty)]
    [(s-exp-match? `(+ ANY ANY) expr) (bin-num-op plus (parse (getArg expr 1) ) (parse (getArg expr 2)) )  ]
    [(s-exp-match? `(* ANY ANY) expr) (bin-num-op mult (parse (getArg expr 1) ) (parse (getArg expr 2)) ) ]
    [(s-exp-match? `(- ANY ANY) expr) (bin-num-op minus (parse (getArg expr 1) ) (parse (getArg expr 2)) ) ]
    [(s-exp-match? `(zero? ANY) expr) (iszero (parseNth expr 1))]
    [(s-exp-match? `(if ANY ANY ANY) expr) (bif (parseNth expr 1) (parseNth expr 2) (parseNth expr 3))]
    [(s-exp-match? `(with (SYMBOL ANY) ANY) expr) (with (getSymbol (getArg expr 1))  (parse (getBoundExpr (getArg expr 1)))  (parseNth expr 2) )]
    [(s-exp-match? `SYMBOL expr) (id (s-exp->symbol expr))]
    [(s-exp-match? `(fun (ANY : ANY ) : ANY ANY) expr) (fun (getSymbol (getArg expr 1)) (getFunArgType (getArg expr 1)) (parseNth expr 4) (parseType (getArg expr 3)))]    
    [(s-exp-match? `(cons ANY ANY) expr) (ncons (parseNth expr 1) (parseNth expr 2))]
    [(s-exp-match? `(empty? ANY) expr) (isnempty (parseNth expr 1))]
    [(s-exp-match? `(first ANY ) expr) (nfirst (parseNth expr 1))]
    [(s-exp-match? `(rest ANY) expr) (nrest (parseNth expr 1))]
    [(s-exp-match? `(ANY ANY) expr) (app (parseNth expr 0) (parseNth expr 1))]
    
    [else 
                 (error 'parse (string-append (to-string expr) "Not in our language"))]))





(define (lookup env symbol)
  (type-case Gamma env
    [(mtEnv) (error 'typeCheck (string-append "Unable to find type of " (to-string symbol) ))]
    [(notMtEnv id type rest) (cond
                               [(equal? id symbol) type]
                               [else (lookup rest symbol)])]))
(define (extend env symbol type)
  (notMtEnv symbol type env))

(define (typeAssert expr env expected)
  (cond
    [(equal? expected (type-of expr env))void ]
    [else  (error 'type (string-append "Expected " (string-append (to-string expected ) (string-append " but got " (to-string (type-of expr env) ))))) ]))

(define (getArgType fun env)
  (type-case Type (type-of fun env)
    [(t-fun argType resultType) argType]
    [else (error 'type "attempted to apply non-function")]))

(define (getResultType fun env)
    (type-case Type (type-of fun env)
    [(t-fun argType resultType) resultType]
    [else (error 'type "attempted to apply non-function")]))



(type-of : (Expr Gamma -> Type))


(define (type-of expr env)
  (type-case Expr expr
    [(num n) (t-num) ]
    [(id x) (lookup env x)]
    [(bool b) (t-bool)]
    [(bin-num-op op lhs rhs) (begin (typeAssert lhs env (t-num)) (typeAssert rhs env (t-num)) (t-num)) ]
    [(iszero e) (begin (typeAssert e env (t-num)) (t-bool))]
    [(bif test then elseB) (begin (typeAssert test env (t-bool)) (typeAssert then env (type-of elseB env))  (type-of elseB env)) ]
    [(with symb binding body) (type-of body (extend env symb (type-of binding env)))]
    [(fun argSym argType bodyExpr bodyType) (begin (typeAssert bodyExpr (extend env argSym argType) bodyType) (t-fun argType bodyType)) ]
    [(app fun arg) (begin (typeAssert arg env (getArgType fun env)) (getResultType fun env))]
    [(nempty)(t-nlist) ]
    [(ncons curr rest) (begin (typeAssert curr env (t-num)) (typeAssert rest env (t-nlist)) (t-nlist))]
    [(nfirst expr) (begin (typeAssert expr env (t-nlist)) (t-num) )]
    [(nrest expr) (begin (typeAssert expr env (t-nlist)) (t-nlist))]
    [(isnempty expr) (begin (typeAssert expr env (t-nlist)) (t-bool))]))

(define (full expr) (type-of (parse expr) (mtEnv)))

(test/exn (full `(fun (x : number) : number (zero? x))) "")
(test/exn (full `(cons 3 (cons false empty))) "Expected")
(test/exn (full `(fun (x : nlist) : nlist (empty? x))) "")
(test/exn (full `(full `(fun (x : (number -> number)) : (number -> number) (x 3))  )) "")
(test/exn (full `(fun (x : ( number -> number )) : number (x x))) "")
(test/exn (full `(if (zero? 3) 4 empty)) "")
(test/exn (full `(if 3 4 5)) "")
(test/exn (full `(if empty 4 5)) "")
(test/exn (full `(with (id : boolean) (if true id 3))) "")
(test/exn (full `(cons 3 (cons true empty))) "")
(test/exn (full `(cons 3 true)) "")
(test/exn (full `(zero? (rest empty))) "")
(test/exn (full `(* true true)) "")
(test/exn (full `gla) "")
(test/exn (full `(3 5)) "")
(test/exn (full `(if false (fun (x : number) : number x) 5)) "")
(test/exn (full `(if (zero? (with (x 5) x)) (fun (x : number) : number x) (fun (x : boolean) : number (+ x 1)))) "")
(test/exn (full `(if (zero? (with (x true) x)) (fun (x : number) : number x) (fun (x : number) : number (+ x 1)))) "")
(test/exn (full `(if (zero? (with (x 5) x)) (fun (x : boolean) : number x) (fun (x : number) : number (+ x 1)))) "")
(test/exn (full `(if (zero? (with (x 5) x)) (fun (x : number) : number x) 3)) "")
(test/exn (full `(if ((fun (x : nlist ) : boolean x) empty) 3 5)) "")
(test/exn (full `(if ((fun (x : nlist ) : number (rest x)) empty) 3 5)) "")
(test/exn (full `(if ((fun (x : nlist ) : nlist (first x)) empty) 3 5)) "")
(test/exn (full `(+ 3 true)) "")
(test/exn (full `(cons false empty)) "")
(test/exn (full `(if empty 3 5)) "")
(test/exn (full `(3 (fun (x : number): number x))) "")
(test/exn (full `((fun (x : boolean) : boolean x) 3)) "")
(test/exn (full `(with (x 6) ((fun (x : boolean) : boolean x) x))) "")
;(test/exn (full `()) "")


(test (full `3) (t-num))
(test (full`(+ 3 3)) (t-num )   )
(test (full`(* 3 3) )(t-num )   )
(test (full`(zero? 3) )( t-bool)   )
(test (full`((fun (x : number) : boolean (zero? x)) 3)) (t-bool )   )
(test (full`((fun (x : (number -> number)) : number (x 3)) (fun (x : number) : number (+ x 1))  )) (t-num )   )
(test (full` (with (bad  empty) bad) ) (t-nlist )   )

(test (full `(fun (x : (number -> number)) : (number -> number) x)  ) (t-fun (t-fun (t-num) (t-num)) (t-fun (t-num) (t-num)))) ;function from a function from number to number to a different function from num -> num
(test (full `(fun (x : ( number -> number )) : number (x 3))  ) (t-fun (t-fun (t-num) (t-num)) (t-num)))

(test (full `(first empty)) (t-num))

(test (full `(cons 3 empty))   (t-nlist))
(test (full `(rest empty))   (t-nlist))
(test (full `(empty? empty))   (t-bool))
(test (full `(with (x 3) (+ x x)))   (t-num))
(test (full `((fun (x : number) : number (+ 1 x)) 1) )  (t-num)) 
(test (full `(if (zero? 3) 4 5))   (t-num))



(test (full `(cons 3 empty))   (t-nlist))
(test (full `(rest empty))   (t-nlist))
(test (full `(rest (cons 3 empty)))   (t-nlist))
(test (full `empty)   (t-nlist))
(test (full `( (fun (x : nlist) : number (first x)) empty ))   (t-num))
(test (full `( with (g empty) g))   (t-nlist))
(test (full `( with (g (fun (x : number) : number (+ x x))) (g 3) ))   (t-num))
(test (full `(zero? ( (fun (x : number) : number x) 3)))   (t-bool))
(test (full `(if false 68 10))   (t-num))
(test (full `(empty? empty))   (t-bool))
(test (full `(fun (x : boolean) : number 3) )   (t-fun (t-bool) (t-num)))
(test (full `((fun (x : boolean) : number 6) true))   (t-num))
(test (full `(fun (x : nlist) : boolean (empty? x)))   (t-fun (t-nlist) (t-bool)))
(test (full `(if ((fun (x : nlist ) : boolean true) empty) 3 5) )   (t-num))
(test (full `(if (zero? (with (x 5) x)) (fun (x : number) : number x) (fun (x : number) : number (+ x 1))))   (t-fun (t-num) (t-num)))
(test (full `(if (empty? (rest empty)) 3 ((fun (x : number) : number x) 3)))   (t-num))
(test (full `(if ((fun (z : number) : boolean (zero? z)) 3) true false))   (t-bool))
(test (full `empty)   (t-nlist))
(test (full `(cons ((fun (x : boolean) : number (if x 3 56)) false) empty))   (t-nlist))
(test (full `(with (x true) (if x (fun (x : number) : boolean (zero? x)) (fun (x : number) : boolean (zero? (+ x 1))))))   (t-fun (t-num) (t-bool)))

;(test (full `())   ())









