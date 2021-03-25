#lang plait

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
    [else (begin
            (display expr)
            (error 'parse "Unable to identify type"))]))


(define (plus x y) (+ x y))
(define (minus x y) (- x y))
(define (mult x y) (* x y))

(define (parse expr)
  (cond
    [(s-exp-match? `NUMBER expr ) (num (s-exp->number expr))]
    [(s-exp-match? `true expr) (bool #t)]
    [(s-exp-match? `false expr) (bool #f)]
    [(s-exp-match? `null expr) (nempty)]
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
    
    [else (begin (display expr)
                 (error 'parse "Not in our language"))]))

(parse `(+ 1 2))
(parse `(with (x 3) (+ 1 2)))
(parse `false)
(parse `(fun (x : number) : boolean (+ x x)))

(parse `( (fun ( x : number) : number (+ x x) )  (+ 3 5) ))

(define (lookup env symbol)
  (type-case Gamma env
    [(mtEnv) (error 'typeCheck "Unable to find type of thing")]
    [(notMtEnv id type rest) (cond
                               [(equal? id symbol) type]
                               [else (lookup rest symbol)])]))
(define (extend env symbol type)
  (notMtEnv symbol type env))

(define (typeAssert expr env expected)
  (cond
    [(equal? expected (type-of expr env))void ]
    [else (begin (display "Expected ") (display expected) (display " got ") (display (type-of expr env) )(error 'type "Unexpected type!") )]))

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

(full `1)
(test/exn (full `(fun (x : number) : number (zero? x))) "Unexp")
(test/exn (full `(cons 3 (cons false null))) "Unexp")


(full `(first null))
(full `(rest null))







