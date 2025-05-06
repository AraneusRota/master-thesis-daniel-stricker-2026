namespace DivideOption

inductive Typpi
  | nat : Typpi
  | bool : Typpi

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => Nat
    | .bool => Bool

inductive Expr : Typpi -> Type
  | greaterThan : Expr .nat -> Expr .nat -> Expr .bool  --Now we are able to compare random numbers with each other
  | const : Nat -> Expr .nat
  | bool : Bool -> Expr .bool
  | add : Expr .nat -> Expr .nat -> Expr .nat
  | ifThenElse : Expr .bool -> Expr x -> Expr x -> Expr x
  | and : Expr .bool -> Expr .bool -> Expr .bool
  | or : Expr .bool -> Expr .bool -> Expr .bool
  | not : Expr .bool -> Expr .bool
  | coinFlip : Expr .bool
  | div : Expr .nat -> Expr .nat -> Expr .nat
deriving Repr

def IO.pure' : x → IO x := pure
def IO.bind' : IO x → (x → IO y) → IO y := bind

def IOO := fun x => IO (Option x)

instance : Pure IOO where
  pure x := IO.pure' (some x)

instance : Bind IOO where
  bind x f := ((do
      let x ← x
      let z ← match x with
      | .some x => f x
      | .none => IO.pure' none)
    : IO (Option _))


def coinFlippi : IOO Bool := ((do
    let x <- IO.rand 0 1
    pure (x == 0))
  : IO (Option Bool))

def eval (exp : Expr x) : IOO x.de :=
  match exp with
    | Expr.greaterThan l r => do
        let l <- eval l
        let r <- eval r
        pure (l > r)
    | Expr.const n => pure n
    | Expr.bool n => if n then pure true else pure false
    | Expr.add n m => do
        let x <- eval n
        let y <- eval m
        pure (x + y)
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
    | Expr.coinFlip => coinFlippi
    | Expr.div n m => do
        let x <- eval n
        let y <- eval m
        if y == 0 then IO.pure' none else pure (x / y)


def doTests : IO Unit := do
  let t1 <- eval (Expr.add (Expr.const 3) (Expr.div (Expr.const 5) (Expr.const 0)))
  let t2 <- eval (Expr.ifThenElse (Expr.greaterThan (Expr.const 2) (Expr.const 3)) (Expr.bool true) (Expr.bool false))
  let t3 <- eval (Expr.ifThenElse (Expr.coinFlip) (Expr.const 2) (Expr.const 3))
  let tests := [t1 == none, t2 == some false, t3 == some 3]
  IO.println s!"DivideOption: {(tests.filter id).length}/{tests.length}"
