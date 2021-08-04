#lang pl

;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Part A - Augmenting the syntax for the SOL Language with Boolean expressions and call-static/call-dynamic ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;; ---------------------------------------------------- Section 1 - SOL BNF

#|

<SOL> :: = { <NumList> }
        |  { scalar-mult <num> <SOL> }
        |  { intersect <SOL> <SOL>}
        |  { union <SOL> <SOL> }
        |  <id>
        |  { with {<id> <SOL>  <id> <SOL>} <SOL> } ;; this should be a syntactic sugar
        |  { fun { <id> <id> } <SOL> } ;; a function must have exactly two formal parameters
        |  { call-static <SOL> <SOL> <SOL> } ;; extends closure environment
        |  { call-dynamic <SOL> <SOL> <SOL> } ;; extends current environment
        |  True
        |  False
        | { if <SOL> then <SOL> else <SOL> }
        | { equal? <SOL> <SOL> }

<NumList> :: =  λ | <num> <NumList> ;; where λ stands for the empty word, i.e., { } is the empty set

;; where <num> is any expression identified by Racket as a Number
;; and <id> is any expression such that Racket identifies '<id> as a symbol
 
|#


;; ----------------------------------------------------- The abstract syntax tree SOL
(define-type SET = (Listof Number))
(define-type SOL
  [Set  SET]
  [Smult Number SOL]
  [Inter SOL SOL]
  [Union SOL SOL]
  [Id    Symbol]
  ;;    [With  Symbol Symbol SOL SOL SOL] -- not to be used, syntactic sugar for ...
  [Fun   Symbol Symbol SOL]
  [CallS SOL SOL SOL]
  [CallD SOL SOL SOL]
  [Bool Boolean]
  [If SOL SOL SOL]
  [Equal SOL SOL])


;; ---------------------------------------------------- Operations on SETs
;; ---------------------------------------------------- ismember?
(: ismember? : Number SET  -> Boolean)
(define (ismember? n l)
  (cond [(null? l) #f]
        [(= n (first l)) #t]
        [else (ismember? n (rest l))]))

;; ---------------------------------------------------- Tests- ismember?
(test (ismember? 1 '(3 4 5)) => #f)
(test (ismember? 1 '()) => #f)
(test (ismember? 1 '(1)) => #t)
(test (ismember? 12 '(1 2)) => #f)
(test (ismember? 4 '(1 2 3 5 6)) => #f)
(test (ismember? 0 '(0)) => #t)
(test (ismember? 1 '(11)) => #f)
(test (not (ismember? 1 '(3 4 5))))
(test (not (ismember? 1 '( 3 2 3 5 6))))
(test (ismember? 1 '(3 4 5 1 3 4)))
(test (ismember? 1 '(1)))

;; ---------------------------------------------------- remove-duplicates
(: remove-duplicates : SET  -> SET)
(define (remove-duplicates l)
  (cond [(or (null? l) (null? (rest l))) l]
        [(ismember? (first l) (rest l)) (remove-duplicates (rest l))]
        [else (cons (first l) (remove-duplicates (rest l)))]))

;; ---------------------------------------------------- Tests- remove-duplicates
(test (remove-duplicates '(3 4 5 1 3 4)) => '(5 1 3 4))
(test (remove-duplicates '(1)) => '(1))
(test (remove-duplicates '()) => '())
(test (remove-duplicates '(1 2 2 2)) => '(1 2))
(test (remove-duplicates '(2 -2 2 -2 2 -2 2)) => '(-2 2))
(test (remove-duplicates '(-11)) => '(-11))
(test (remove-duplicates '(1 2 3 2 1 2 3 2 1 2 3 2 1 2 3)) => '(1 2 3))
(test (remove-duplicates '(1 11 111 1111 11111)) => '(1 11 111 1111 11111))
(test (remove-duplicates '(0)) => '(0))
(test (remove-duplicates '(00)) => '(00))
(test (remove-duplicates '(1 7 -8 6 4 8 2 7)) => '(1 -8 6 4 8 2 7))
(test (remove-duplicates '(1 4 5 3 3)) => '(1 4 5 3))

;; ---------------------------------------------------- create-sorted-set
(: create-sorted-set : SET -> SET)
(define (create-sorted-set l)
  (remove-duplicates (sort l <)))

;; ---------------------------------------------------- Tests- create-sorted-set
(test (create-sorted-set '(3 4 5)) => '(3 4 5))
(test (create-sorted-set '( 3 2 3 5 6)) => '(2 3 5 6))
(test (create-sorted-set '()) => '())
(test (create-sorted-set '( 3 2 3 3 3 3 3 5 6)) => '(2 3 5 6))
(test (create-sorted-set '(1)) => '(1))
(test (create-sorted-set '( 3 2 1)) => '(1 2 3))
(test (create-sorted-set '()) => '())
(test (create-sorted-set '( 3 2 3 2 1 1)) => '(1 2 3))
(test (create-sorted-set '(1 -1 1 1 1 1 -1 11 2 2 2 2 22 3 3 33 -333 333)) => '(-333 -1 1 2 3 11 22 33 333))

;; ---------------------------------------------------- set-union
(: set-union : SET SET -> SET)
(define (set-union A B)
  (create-sorted-set (append A B)))

;; ---------------------------------------------------- Tests- set-union
(test (set-union '(3 4 5) '(3 4 5)) => '(3 4 5))
(test (set-union '(3 4 5) '()) => '(3 4 5))
(test (set-union '(3 4 5) '(1)) => '(1 3 4 5))
(test (set-union '(3 4 5) '(3 4 5 6)) => '(3 4 5 6))
(test (set-union '(3 4 5) '(1)) => '(1 3 4 5))
(test (set-union '(3 4 -5) '(11)) => '(-5 3 4 11))
(test (set-union '() '()) => '())
(test (set-union '(3) '(2)) => '(2 3))
(test (set-union '(3 4 5) '(0 1)) => '(0 1 3 4 5))
(test (set-union '(-3 -4 -5) '(1 0)) => '(-5 -4 -3 0 1))

;; ---------------------------------------------------- set-intersection
(: set-intersection : SET SET -> SET)
(define (set-intersection A B)
  (: mem-filter : Number -> Boolean)
  (define (mem-filter n)
    (ismember? n A))
  (filter mem-filter (create-sorted-set B)))

;; ---------------------------------------------------- Tests- set-intersection
(test (set-intersection '(3 4 5) '(3 4 5)) => '(3 4 5))
(test (set-intersection '(3 -4 5) '(3)) => '(3))
(test (set-intersection '(3 4 -5) '(1)) => '())
(test (set-intersection '(3 4 5) '(3 4)) => '(3 4))
(test (set-intersection '() '()) => '())
(test (set-intersection '(1 2 3 4 5 6 8) '(2 4 6 8 10)) => '(2 4 6 8))
(test (set-intersection '(1 2 3 4 5 6 7 8 9 0) '()) => '())
(test (set-intersection '(1 3 4 5 11) '(1 11)) => '(1 11))
(test (set-intersection '(3 -4 5) '(-4 5)) => '(-4 5))
(test (set-intersection '(3 4 5) '(2)) => '())
(test (set-intersection '(-3 -4 -5) '(-1)) => '())


;; ---------------------------------------------------- Section 2 - Parser
(: parse-sexpr : Sexpr -> SOL)
;; parse-sexpr function convert s-expressions into SOLs.
;; input: S-expression
;; output: SOL
;; operates: That function convert sexpr type to SOL type, to "help" the other function- parse.
;; The function checks by "match" function the input, and works by the logic of the SOL.
;; If there is not a good syntax- return Error.
;; My function will work with Sexpr only.
;; There is not some difficulties to solve that question
;; I solved it after 1.5 hours.
(define (parse-sexpr sexpr)
  (match sexpr
    [(list (number: ns) ...) (Set (create-sorted-set ns))] ;; sort and remove-duplicates
    ['True (Bool true)]
    ['False (Bool false)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name1) named1 (symbol: name2) named2) body)
        (CallS (Fun name1 name2 (parse-sexpr body)) (parse-sexpr named1) (parse-sexpr named2))] ;;; There is no With constructor. I used CallS + Fun.
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: name1) (symbol: name2)) body)
        (if (equal? name1 name2)
            (error 'parse-sexpr "`fun' has a duplicate param name in ~s" sexpr) ;; cannot use the same param name twice
            (Fun name1 name2 (parse-sexpr body)))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(list 'scalar-mult (number: sc) rhs) (Smult sc (parse-sexpr rhs))]
    [(list 'intersect lhs rhs) (Inter (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'union lhs rhs) (Union (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'call-static fun arg1 arg2) (CallS (parse-sexpr fun) (parse-sexpr arg1) (parse-sexpr arg2))]
    [(list 'call-dynamic fun arg1 arg2) (CallD (parse-sexpr fun) (parse-sexpr arg1) (parse-sexpr arg2))]
    [(list 'if cond 'then true-cond 'else false-cond) (If (parse-sexpr cond) (parse-sexpr true-cond) (parse-sexpr false-cond))]
    [(list 'equal? check1 check2) (Equal (parse-sexpr check1) (parse-sexpr check2))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))


;; ---------------------------------------------------- Tests- parse-sexpr
(test (parse-sexpr '(1 2)) => (Set '(1 2)))
(test (parse-sexpr '()) => (Set '()))
(test (parse-sexpr '(1 -1 0)) => (Set '(-1 0 1)))
(test (parse-sexpr '(1 1 1)) => (Set '(1)))
(test (parse-sexpr '(1 11 111)) => (Set '(1 11 111)))
(test (parse-sexpr '(-1 -2)) => (Set '(-2 -1)))
(test (parse-sexpr '(union (1 2 3) (1 2 7))) => (Union (Set '(1 2 3)) (Set '(1 2 7))))
(test (parse-sexpr '(union (1 3) (1 2 3))) => (Union (Set '(1 3)) (Set '(1 2 3))))
(test (parse-sexpr '(union (1 2 3) (1 2 3))) => (Union (Set '(1 2 3)) (Set '(1 2 3))))
(test (parse-sexpr '(union (1 2 3) (0 7))) => (Union (Set '(1 2 3)) (Set '(0 7))))
(test (parse-sexpr '(union (-1) (1 -2 7))) => (Union (Set '(-1)) (Set '(-2 1 7))))
(test (parse-sexpr '(union (000) (0))) => (Union (Set '(0)) (Set '(0))))
(test (parse-sexpr '(intersect (1 2 3 4 5 6 7 8 9 0) (0))) => (Inter (Set '(0 1 2 3 4 5 6 7 8 9)) (Set '(0))))
(test (parse-sexpr '(intersect (0 00 000 1 2 3 4) (1 2 3 4))) => (Inter (Set '(0 1 2 3 4)) (Set '(1 2 3 4))))
(test (parse-sexpr '(intersect (0 0 0 12 13 0 0 14 0 0) (12 13 14 12 13 14 15 15 1 5 15 ))) => (Inter (Set '(0 12 13 14)) (Set '(1 5 12 13 14 15))))
(test (parse-sexpr '(intersect (1 2 3 ) (1 2 3))) => (Inter (Set '(1 2 3)) (Set '(1 2 3))))
(test (parse-sexpr '(intersect (1 2 3) ())) => (Inter (Set '(1 2 3)) (Set '())))
(test (parse-sexpr 'A) => (Id 'A))
(test (parse-sexpr 'B) => (Id 'B))
(test (parse-sexpr '(scalar-mult 1 (1 2 3))) => (Smult 1 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult 0 (1 2 3))) => (Smult 0 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult -1 (1 2 3))) => (Smult -1 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult 10 (1 2 3))) => (Smult 10 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult 1 ())) => (Smult 1 (Set '())))
(test (parse-sexpr '(scalar-mult 0 (1))) => (Smult 0 (Set '(1))))
(test (parse-sexpr '(scalar-mult 11 (1 2 3))) => (Smult 11 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult 100 (1 2 3))) => (Smult 100 (Set '(1 2 3))))
(test (parse-sexpr '(scalar-mult 1 (-1))) => (Smult 1 (Set '(-1))))
(test (parse-sexpr 'True) => (Bool #t))
(test (parse-sexpr 'False) => (Bool #f))
(test (parse-sexpr '(with d d d)) =error> "parse-sexpr: bad `with' syntax in (with d d d)")
(test (parse-sexpr '1)
      =error> "parse-sexpr: bad syntax in 1")

(test (parse-sexpr '123)
      =error> "parse-sexpr: bad syntax in 123")

(test (parse-sexpr '-1)
      =error> "parse-sexpr: bad syntax in -1")

(test (parse-sexpr 4)
      =error> "parse-sexpr: bad syntax in 4")

(test (parse-sexpr '(a b c))
      =error> "parse-sexpr: bad syntax in (a b c)")

(test (parse-sexpr '(a 1 4 b c))
      =error> "parse-sexpr: bad syntax in (a 1 4 b c)")

(test (parse-sexpr '(want))
      =error> "parse-sexpr: bad syntax in (want)")





(: parse : String -> SOL)
;; parses a string containing a SOL expression to a SOL AST
;; input: String that represents SOL
;; output: SOL
;; operates: That function convert String type that represents a SOL to SOL type.
;; The function will work with correct String only.
;; The function get the String, make it to be a sexpr by "string->sexpr" function, and use parse-sexpr on it.
;; The solved time is included in ths "parse-sexpr" time. 1.5 hours for all..
(define (parse str)
  (parse-sexpr (string->sexpr str)))

  
;; ---------------------------------------------------- Tests- parse
 
(test (parse "{1 2 3  4 1 4  4 2 3 4 1 2 3}") => (Set '(1 2 3 4)))
(test (parse "{union {1 2 3} {4 2 3}}") => (Union (Set '(1 2 3)) (Set '(2 3 4))))
(test (parse "{fun {x x} x}") =error> "parse-sexpr: `fun' has a duplicate param name in (fun (x x) x)")
(test (parse "{intersect {1 2 3} {4 2 3}}") => (Inter (Set '(1 2 3)) (Set '(2 3 4))))
(test (parse "{with {S {intersect {1 2 3} {4 2 3}} c {}}
                 {call-static {fun {x y} {union x S}}
                              {scalar-mult 3 S}
                              {4 5 7 6 9 8 8 8}}}") 
      =>
      (CallS (Fun 'S
                  'c
                  (CallS (Fun 'x 'y (Union (Id 'x) (Id 'S))) 
                         (Smult 3 (Id 'S)) 
                         (Set '(4 5 6 7 8 9))))
             (Inter (Set '(1 2 3)) (Set '(2 3 4)))
             (Set '())))


(test (parse "{with {S {intersect {1 2 3} {4 2 3}} S1 {union {1 2 3} {4 2 3}}}
                          {fun {x} S}}")
      =error> "parse-sexpr: bad `fun' syntax in (fun (x) S)") ;; functions require two formal parameters
(test (parse "True") => (Bool true))
(test (parse "{if {equal? {1 2 3} {1 2}} then {1 2 3} else {1 2}}") =>
      (If (Equal (Set '(1 2 3)) (Set '(1 2))) (Set '(1 2 3)) (Set '(1 2))))

(test (parse "{with {S {intersect {1 2 3} {4 2 3}} c {}}
                 {call-dynamic {fun {x y} {union x S}}
                               {if {equal? S {scalar-mult 3 S}}
                                   then S
                                   else {4 5 7 6 9 8 8 8}}
                               {}}}")
      => (CallS (Fun 'S 'c
                     (CallD (Fun 'x 'y (Union (Id 'x) (Id 'S)))
                            (If (Equal (Id 'S) (Smult 3 (Id 'S)))
                                (Id 'S)
                                (Set '(4 5 6 7 8 9)))
                            (Set '())))
                (Inter (Set '(1 2 3)) (Set '(2 3 4)))
                (Set '())))


;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Part B - Adapting the implementation of eval for the SOL language with boolean expressions and call-static/call-dynamic ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;; ---------------------------------------------------- Section 3 - Formal evaluation rules

#|
------------------------------------------------------
Evaluation rules:

    eval({ N1 N2 ... Nl })      = sort( create-set({ N1 N2 ... Nl })) ;; where create-set removes all duplications from
                                                                         the sequence (list) and sort is a sorting procedure

    eval({scalar-mult K E})     = { K*N1 K*N2 ... K*Nl }              ;; where eval(E)={ N1 N2 ... Nl }
    eval({intersect E1 E2})     = sort( create-set(set-intersection (eval(E1) , eval(E2)))
    eval({union E1 E2})         = sort( create-set(set-union (eval(E1) , eval(E2)))
    eval({fun {x1 x2} E},env)   = <{fun {x1 x2} E}, env> ;; eval of fun returns the function as is. (make it FunV and use the env..)
    eval({call-static E-op E1 E2},env)
                                = eval(Ef, extend(x2,eval(E2,env), extend(x1, eval(E1,env), f-env)) ;; I decided to use f-env because its the static call,
                                                                                                       and I want to use the env in which its defined.
                                                      if eval(E-op,env) = <{fun {x1 x2} Ef}, envf>
                                = error!              otherwise

    eval({call-dynamic E-op E1 E2},env)
                                = eval(Ef, extend(x2,eval(E2,env), extend(x1, eval(E1,env), env)) ;; I decided to use env because its the dynamic call,
                                                                                                     and I want to enable evaluating the function in which its called.
                                                      if eval(E-op,env) = <{fun {x1 x2} Ef}, envf>
                                = error!              otherwise

    eval(True,env)              = true
    eval(False,env)             = false
    eval({if E1 then E2 else E3},env)
                                = eval(E3, env)       if eval(E1,env) = false
                                = eval(E2, env)     otherwise

    eval({equal? E1 E2},env)    = true                if eval(E1,env) is equal in content to eval(E2,env)
                                = false               otherwise
    eval({call E1 E2},env1)
                                = eval(Ef,extend(x,eval(E2, env1),env2))
                                                      if eval(E1,env1) = <{fun {x} Ef}, env2>
                                = error!          otherwise

|#

;; ---------------------------------------------------- Section 4 - Types for environments, values, and a lookup function

(define-type ENV
  [EmptyEnv]
  [Extend Symbol VAL ENV])

(define-type VAL
  [SetV SET]
  [FunV Symbol Symbol SOL ENV]
  [BoolV Boolean]) ;; I want to enable boolean term

(: lookup : Symbol ENV -> VAL)
(define (lookup name env)
  (cases env
    [(EmptyEnv) (error 'lookup "no binding for ~s" name)]
    [(Extend id val rest-env)
     (if (eq? id name) val (lookup name rest-env))]))

;; ---------------------------------------------------- Tests- lookup
(test (lookup 'x (Extend 'x (SetV '(1 2)) (EmptyEnv))) => (SetV '(1 2)))
(test (lookup 'x (Extend 'x (BoolV true) (EmptyEnv))) => (BoolV true))
(test (lookup 'y (Extend 'x (SetV '(1 2)) (EmptyEnv)))
      =error> "lookup: no binding for y")

;; Auxiliary procedures for eval

(: SetV->set : VAL -> SET)
;; SetV->set function gets a set that represents as VAL, and make it to be set.
;; Input: VAL
;; Output: SET
(define (SetV->set v)
  (cases v
    [(SetV S) S]
    [else (error 'SetV->set "expects a set, got: ~s" v)]))


(: smult-set : Number VAL -> VAL)
;; smult-set function makes a scalar multiply to the whole set.
;; Input: Number (Scalar) and VAL
;; Output: VAL
;; By the SetV constructor i maked the list to be VAL
;; and I used SetV->set on "s" set to go over it with "map" and mult-op.
;; The function "fill in" takes me a 1 hour.
(define (smult-set n s)
  (: mult-op : Number -> Number)
  (define (mult-op k)
    (* k n))
  (SetV (map mult-op (SetV->set s))))



(: set-op : (SET SET -> SET) VAL VAL -> VAL)
;; set-op function gets a binary SET operator, and uses it within a SetV wrapper
;; The function takes 2 SetV, change it to sets, use the operator on it- and return the answer to be SetV.
;; I decided to make this signature of the function with "(SET SET -> SET) VAL VAL -> VAL" because:
;; (SET SET -> SET) its the operator- union/intersect..
;; VAL VAL its the 2 SetV's that I working on.
;; and the return value is a VAL too..
;; The answer takes me a 1 hour.
(define (set-op op val1 val2)
  (SetV (op (SetV->set val1) (SetV->set val2))))



;; ---------------------------------------------------- Section 5 - the eval procedure 
(: eval : SOL ENV -> VAL)
;; evaluates SOL expressions by reducing them to set values
;; That function makes the convertion from an SOL and ENV to the VAL values
;; input: SOL ENV
;; output: VAL
;; operates: That function evaluated the SOL to his value.
;; The function will work with correct input only.
;; The function get the input and makes check by "cases" function-
;; to check the pattern and the validation of the variant.
;; The difficult- to decide the call-type, static/dynamic.
;; and the env that appropirates 
;; It tooks me 2.5 hours to solve that question..
(define (eval expr env)
  (cases expr
    [(Set S) (SetV (create-sorted-set S))]
    [(Smult n set) (smult-set n (eval set env))]
    [(Inter l r) (set-op set-intersection (eval l env) (eval r env))]
    [(Union l r) (set-op set-union (eval l env) (eval r env))]
    [(Id name) (lookup name env)]
    [(Fun bound-id1 bound-id2 bound-body)
     (FunV bound-id1 bound-id2 bound-body env)]
    [(CallS fun-expr arg-expr1 arg-expr2)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-id1 bound-id2 bound-body f-env)
          (eval bound-body (Extend bound-id2 (eval arg-expr2 env)
                                   (Extend bound-id1 (eval arg-expr1 env)
                                           f-env)))] ;; static-call with the environment that got with the function
         [else (error 'eval "`call-static' expects a function, got: ~s" fval)]))]
    [(CallD fun-expr arg-expr1 arg-expr2)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-id1 bound-id2 bound-body f-env)
          (eval bound-body (Extend bound-id2 (eval arg-expr2 env)
                                   (Extend bound-id1 (eval arg-expr1 env)
                                           env)))] ;; dynamic-call with the "that" environment
         [else (error 'eval "`call-dynamic' expects a function, got: ~s" fval)]))]
    [(Bool b) (BoolV b)]
    [(If cond true-cond false-cond)
     (let ([cval (eval cond env)])
       (cases cval
         [(BoolV b) (if (eq? b true) (eval true-cond env) (eval false-cond env))]
         [else (eval true-cond env)]))]
    [(Equal l r) (if (equal? (eval l env) (eval r env)) (BoolV #t) (BoolV #f))]))


;; ---------------------------------------------------- Tests- eval
(test (eval (Set '(-1 2 3)) (EmptyEnv)) => (SetV '(-1 2 3)))
(test (eval (Set '())(EmptyEnv)) => (SetV '()))
(test (eval (Set '(1 2 3))(EmptyEnv)) => (SetV '(1 2 3)))
(test (eval (Set '(-1 -2 -3))(EmptyEnv)) => (SetV '(-3 -2 -1)))
(test (eval (Set '(0 -0 0))(EmptyEnv)) => (SetV '(0)))
(test (eval (Smult 5 (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(-5 10 15)))
(test (eval (Smult 0 (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(0 0 0)))
(test (eval (Smult -1 (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(1 -2 -3)))
(test (eval (Smult 10 (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(-10 20 30)))
(test (eval (Smult 1 (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(-1 2 3)))
(test (eval (Inter (Set '(-1 2 3)) (Set '(-1 2 3)))(EmptyEnv)) => (SetV '(-1 2 3)))
(test (eval (Inter (Set '(-1 2 3)) (Set '()))(EmptyEnv)) => (SetV '()))
(test (eval (Inter (Set '(-1 2 3)) (Set '(0)))(EmptyEnv)) => (SetV '()))
(test (eval (Inter (Set '(-1 2 3)) (Set '(-1)))(EmptyEnv)) => (SetV '(-1)))
(test (eval (Inter (Set '(3 33 333)) (Set '(33 3)))(EmptyEnv)) => (SetV '(3 33)))
(test (eval (Inter (Set '(-1 -2 -3)) (Set '(-1 2 -3)))(EmptyEnv)) => (SetV '(-3 -1)))
(test (eval (Union (Set '(3 33 333)) (Set '(33 3)))(EmptyEnv)) => (SetV '(3 33 333)))
(test (eval (Union (Set '(3 33 333)) (Set '(0 00 000)))(EmptyEnv)) => (SetV '(0 3 33 333)))
(test (eval (Union (Set '(7)) (Set '(12 3)))(EmptyEnv)) => (SetV '(3 7 12)))
(test (eval (Union (Set '(0)) (Set '(15 16)))(EmptyEnv)) => (SetV '(0 15 16)))
(test (eval (Union (Set '(12)) (Set '(33 3)))(EmptyEnv)) => (SetV '(3 12 33)))
(test (eval (Union (Set '(4 8 0)) (Set '(33 3)))(EmptyEnv)) => (SetV '(0 3 4 8 33)))
(test (eval (CallD (Set '(4 8 0)) (Set '(33 3)) (Set '(1))) (EmptyEnv))
      =error> "eval: `call-dynamic' expects a function, got: #(struct:SetV (0 4 8)")
(test (eval (If (Equal (Set '(1 2 3)) (Set '(1 2 3))) (Set '(1 2 3)) (Set '(1))) (EmptyEnv)) => (SetV '(1 2 3)))




;; ---------------------------------------------------- Section 6 - Creating a non-empty global environment 

(: createGlobalEnv : -> ENV)
;; createGlobalEnv function, makes an Empty Environment that can be extended.
;; The function dont get any input, and makes an environment that get as output.
;; The dufficulty in this function is to understand the "Extend" logic.
;; The function uses "Extend" to the "EmptyEnv" by the constructors, and makes cons, first and second terms.
;; cons- creating a pair,
;; first- returning the first element in a pair
;; second- returning the second element in a pair
;; It tooks me an 2 hours to complete the function.
(define (createGlobalEnv)
  (Extend 'second
          (FunV 'x 'y
                (CallS (Id 'x) (Fun 'f 's (Id 's)) (Set '()))
                (EmptyEnv))
          (Extend 'first
                  (FunV 'x 'y
                        (CallS (Id 'x) (Fun 'f 's (Id 'f)) (Set '()))
                        (EmptyEnv))
                  (Extend 'cons
                          (FunV 'x 'y (Fun 'select 'select2
                                           (CallD (Id 'select) (Id 'x) (Id 'y)))
                                (EmptyEnv))
                          (EmptyEnv)))))



;; ---------------------------------------------------- Section 7 - Interface: The run procedure

(: run : String -> (U SET VAL Boolean))
;; evaluate a SOL program contained in a string
;; run function get String as input, making it to be VAL "result" be "let" function,
;; (with eval and parse + createGlobalEnv as environment) 
;; and its output is VAL/SET/Boolean.
;; Its took me an hour to fill in all the function.
(define (run str)
  (let ([result (eval (parse str) (createGlobalEnv))])
    (cases result
      [(SetV S) S]
      [(BoolV B) B]
      [else (error 'run "eval returned invalid argument: ~s" result)])))





(test (run "{1 2 3  4 1 4  4 2 3 4 1 2 3}") => '(1 2 3 4))
(test (run "{union {1 2 3} {4 2 3}}") => '(1 2 3 4))
(test (run "{intersect {1 2 3} {4 2 3}}") => '( 2 3))
(test (run "{with {S {intersect {1 2 3} {4 2 3}}
                   S1 {}}
                 {call-static {fun {x y} {union x S}}
                              {scalar-mult 3 S}
                              {4 5 7 6 9 8 8 8}}}")
      => '(2 3 6 9))


(test (run "{with {S {intersect {1 2 3} {4 2 3}}
                   S1 {}}
               {call-static {fun {x y} {union x y}}
                              {scalar-mult 3 S}
                              {4 5 7 6 9 8 8 8}}}")
      => '(4 5 6 7 8 9))

(test (run "{with {p {call-static cons {1 2 3} {4 2 3}}
                    S1 {}}
              {with {S {intersect {call-static first p {}}
                                  {call-static second p {}}}
                     S1 {}}
                 {call-static {fun {x y} {union x S}}
                              {scalar-mult 3 S}
                              {4 5 7 6 9 8 8 8}}}}")
      =>  '(2 3 6 9))
(test (run "{with {p {call-dynamic cons {1 2 3} {4 2 3}}
                   S1 {}}
              {with {S {intersect {call-dynamic first p {}}
                                  {call-dynamic second p {}}}
                     S1 {}}
                 {call-dynamic {fun {x y} {union x S}}
                              {scalar-mult 3 S}
                              {4 5 7 6 9 8 8 8}}}}")
      =>  '(2 3 6 9))
(test (run "True") => #t)
(test (run "False") => #f)
(test (run "{if {equal? {1 2 3} {1 2}} then {1 2 3} else {1 2}}") => '(1 2))
(test (run "{equal? {union {1 2 3} {4 2 3}} {1 2 3 4}}") => #t)
(test (run "{if {1 2 3} then {1 2 3} else {1 2}}") => '(1 2 3))
(test (run "{if {3} then {1 33} else {44}}") => '(1 33))
(test (run "{if {3} then {1 33} else {44}}") => '(1 33))
(test (run "{call-dynamic cons {1 2 3} {4 2 3}}")
      =error> "run: eval returned invalid argument: ")
(test (run "{union {equal? {4} {4}} {4 2 3}}")
      =error> "SetV->set: expects a set, got: #(struct:BoolV #t)")
(test (run "{fun {x x} x}")
      =error> "parse-sexpr: `fun' has a duplicate param name in (fun (x x) x)")
(test (run "{call-static {1} {2 2} {}}")
      =error> "eval: `call-static' expects a function, got: #(struct:SetV (1))")






;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Part C - Open questions: ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#|


1.
Question:
What are the types that we have now (after you are done) in the SOL language?


Answer:
The types that we have now in the SOL language, are:
Set
Smult
Inter
Union
Id
Fun
CallS
CallD
Bool
If
Equal



2.
Question:
Explain where in the solution of section 2 (when parsing with expressions) you called a function
dynamically/statically – what was the importance of your choices?


Answer:
In section 2, when I parsing "with" expressions, I called a function statically.
I used (CallS (Fun.. )) because of the reason that i dont want to enable changing identifiers in run time,
meaning- to use the identifiers as they were when its defined, and not as they were when its use.
The "with" expression allowing us to declare an identifier that we need to use later..
When i parsing "call-static", obviously i used CallS, that using static-call..
Same goes for "call-dynamically"- CallD, that using dynamic-call.
The importance of my choise is:
To not allow changing/overriding identifier that defined before, if its not the reason.
And to enable it- when you need dynamic call.



3.
Question:
Explain where in the solution of section 6 you used call-dynamic and where you used
call-static – what was the importance of your choices?


Answer:
In section 6, I used call-static at all the 3 times, because of the reason that i dont want to make an situation
that the 'second get the value of the 'first, or the 'first get the value of the 'cons, because of unwanted update of the identifiers
(in case that the identifiers are with the same name).
The 'cons call, can be both static and dynamic call, because its the inner scope. but more accurate to make it static.
I explained the importance of the choices.. to not enable the unwanted updates of identifiers..



4. 
Question:
Would there be any difference if we used call-dynamic in some places in the following test? Explain your answer.


Answer:
No, there is no any different if we used call-dynamic in some places in this test.
The reason, is-
There is no duplicates of identifiers, so both of calls will work.
The only identifier that is duplicate is S1, but we dont use it.




|#