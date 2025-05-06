import Mathlib.Control.Random

namespace StateMRandomness

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
  | ifThenElse : Expr .bool -> Expr x -> Expr x -> Expr x
  | and : Expr .bool -> Expr .bool -> Expr .bool
  | or : Expr .bool -> Expr .bool -> Expr .bool
  | not : Expr .bool -> Expr .bool
  | roll : Nat -> Expr .nat
  | prob : (Nat -> Bool) -> Expr .nat -> Expr .nat
--deriving Repr

def diceRoll (d : Nat) : IO Nat :=
  IO.rand 1 d

def diceRolli (gen: StdGen) (d : Nat) : (Nat × StdGen) :=
  randNat gen 1 d

def sampleSize := 1000

def prob (pred: Nat -> Bool) (l : Typpi.nat.de) : Typpi.nat.de :=
  let listi := l
  let fil := List.filter pred listi
  let probab := ((List.length fil) * 100) / (List.length listi)
  [probab]

def statefulliRolli (n : Nat) : StateM StdGen Nat := do
  let (number, generator) := diceRolli (<- get) n
  set generator
  pure number



def eval (exp : Expr x) : StateM StdGen x.de :=
  match exp with
    | Expr.const n => pure (List.map (fun _ => n) (List.range sampleSize))
    | Expr.bool n => if n then pure true else pure false
    | Expr.add n m => do
        let x <- eval n
        let y <- eval m
        pure (List.zipWith (fun l r => l + r) x y)
    | Expr.ifThenElse c e1 e2 => do
        let x <- eval c
        if x then eval e1 else eval e2
    | Expr.and n m => do
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
    | Expr.roll n =>
        Monad.sequence ((List.range sampleSize).map (fun _ => statefulliRolli n))
    | Expr.prob f xs => do
        pure (prob f (<- eval xs))


--#eval eval (Expr.add (Expr.roll 3) (Expr.roll 3))
def hello := eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))
#eval hello |>.run (mkStdGen 200)
#eval eval (Expr.add (Expr.roll 3) (Expr.roll 3)) |>.run (mkStdGen 200)

def doTests := [(do
  let (r, _) <- (hello |>.run (mkStdGen 200))
  pure (r == [33])).run]
