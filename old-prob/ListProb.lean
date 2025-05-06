namespace ListProb

inductive Typpi
  | nat : Typpi
  | bool : Typpi

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => List Nat
    | .bool => Bool


inductive Expr : Typpi -> Type
  | const : Nat -> Expr .nat
  | bool : Bool -> Expr .bool
  | add : Expr .nat -> Expr .nat -> Expr .nat
  | sub : Expr .nat -> Expr  .nat -> Expr .nat
  | ifThenElse : Expr .bool -> Expr x -> Expr x -> Expr x
  | and : Expr .bool -> Expr .bool -> Expr .bool
  | or : Expr .bool -> Expr .bool -> Expr .bool
  | not : Expr .bool -> Expr .bool
  | coinFlip : Expr .nat
  | roll : Nat -> Expr .nat
  | probEq : Nat -> Expr .nat -> Expr .nat
  | probGt : Nat -> Expr .nat -> Expr .nat
  | probGe : Nat -> Expr .nat -> Expr .nat
  | prob : (Nat -> Bool) -> Expr .nat -> Expr .nat


-- limitation: cant pass .nat to roll because we don't know how to convert .nat to Nat
-- coin flip should contain booleans for reasonable semantics. Usually you don't want to add coin flips
-- booleans seem kind of useless, because you cant compare anything with random numbers
-- prob only works with lambda expressions written in the lean programming language
def eval (exp : Expr x) : x.de :=
  match exp with
    | Expr.const n => [n]
    | Expr.bool n => n
    | Expr.add n m =>
        let xs := eval n
        let ys := eval m
        List.join (List.map (fun x => List.map (fun y => x + y) (ys)) (xs))
    | Expr.sub n m =>
        let xs := eval n
        let ys := eval m
        List.join (List.map (fun x => List.map (fun y => x - y) (ys)) (xs))
    | Expr.ifThenElse c e1 e2 =>
        if eval c then eval e1 else eval e2
    | Expr.and n m =>
        eval n && eval m
    | Expr.or n m =>
        eval n || eval m
    | Expr.not n => !(eval n)
    | Expr.coinFlip => [0, 1]
    | Expr.roll n => List.map (fun x => x + 1) (List.range n)
    | Expr.probEq n xs =>
        [((List.length (List.filter (fun x => x == n) (eval xs)) * 100) / List.length (eval xs))]
    | Expr.probGt n xs =>
        [((List.length (List.filter (fun x => x > n) (eval xs)) * 100) / List.length (eval xs))]
    | Expr.probGe n xs =>
        [((List.length (List.filter (fun x => x >= n) (eval xs)) * 100) / List.length (eval xs))]
    | Expr.prob f xs =>
        [((List.length (List.filter f (eval xs)) * 100) / List.length (eval xs))]




#eval eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3)))
#eval eval (Expr.add (Expr.roll 3) (Expr.roll 3))
#eval eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))

def tests := [
  eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) == [33],
  eval (Expr.add (Expr.roll 3) (Expr.roll 3)) == [2, 3, 4, 3, 4, 5, 4, 5, 6],
  eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3))) == [33]
]
