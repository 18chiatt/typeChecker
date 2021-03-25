#lang plait

(define-type Expr
  (numE [n : Number])
  (plusE [lhs : Expr] [rhs : Expr])
  (equalE [lhs : Expr] [rhs : Expr])
  (notE [arg : Expr]))

(define-type Type
  (numT)
  (boolT))

; to implement
; - typecheck

(define (check expr type)
  (cond
    [(equal? type (typecheck expr)) void ]
    [else (error 'type "unexpected type, expected happy, got sad")]))

(define (typecheck expr)
  (type-case Expr expr
    [(numE n) (numT)]
    [(plusE lhs rhs) (begin
                       (check lhs (numT))
                       (check rhs (numT))
                       (numT))]
    [(equalE lhs rhs) (begin
                        (check rhs (numT))
                        (check lhs (numT))
                        (boolT))]
    [(notE arg) (begin
                  (check arg (boolT))
                  (boolT))]))

(typecheck (equalE (numE 10) (numE 10)))

