inductive Typpi
  | nat : Typpi
  | bool : Typpi

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => Nat
    | .bool => Bool

inductive Expr : Typpi -> Type
  | const : Nat -> Expr .nat
  | bool : Bool -> Expr .bool
  | add : Expr .nat -> Expr .nat -> Expr  .nat
  | sub : Expr .nat -> Expr  .nat -> Expr .nat
  | ifThenElse : Expr .bool -> Expr x -> Expr x -> Expr x
  | and : Expr .bool -> Expr .bool -> Expr .bool
  | or : Expr .bool -> Expr .bool -> Expr .bool
  | not : Expr .bool -> Expr .bool
  | coinFlip : Expr .bool
deriving Repr

#eval Expr.const 10

def coinFlip : IO Bool := do
  let x <- IO.rand 0 1
  pure (x == 0)

def eval (exp : Expr x) : IO x.de :=
  match exp with
    | Expr.const n => pure n
    | Expr.bool n => if n then pure true else pure false
    | Expr.add n m => do
        let x <- eval n
        let y <- eval m
        pure (x + y)
    | Expr.sub n m => do
        let x <- eval n
        let y <- eval m
        pure (x - y)
    | Expr.ifThenElse c e1 e2 => do
        let x <- eval c
        if x then eval e1 else eval e2
    | Expr.and n m =>  do
        let x <- eval n
        let y <- eval m
        pure (x && y)
    | Expr.or n m => do
        let x <- eval n
        let y <- eval m
        pure (x || y)
    | Expr.not n => do
        let x <- eval n
        if x then pure false else pure true
    | Expr.coinFlip => coinFlip

#eval eval (Expr.ifThenElse (Expr.coinFlip) (Expr.const 2) (Expr.const 3))

def main : IO Unit := do
  let x <- eval Expr.coinFlip
  IO.println s!"coin flip: {x}"
