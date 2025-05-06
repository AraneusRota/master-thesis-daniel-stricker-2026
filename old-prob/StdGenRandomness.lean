import Mathlib.Control.Random

namespace StdGenRandomness

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


def diceRolli (gen: StdGen) (d : Nat) : (Nat × StdGen) :=
  randNat gen 1 d

def sampleSize := 1000

def prob (pred: Nat -> Bool) (l : (Typpi.nat.de × StdGen)) : (Typpi.nat.de × StdGen) :=
  let (listi, gen) := l
  let fil := List.filter pred listi
  let probab := ((List.length fil) * 100) / (List.length listi)
  ([probab], gen)

def eval (gen : StdGen) (exp : Expr x) : (x.de × StdGen) :=
  match exp with
    | Expr.const n => (List.map (fun _ => n) (List.range sampleSize), gen)
    | Expr.bool n => if n then (true, gen) else (false, gen)
    | Expr.add n m =>
        let (x, xGen) := eval gen n
        let (y, yGen) := eval xGen m
        ((List.zipWith (fun l r => l + r) x y), yGen)
    | Expr.ifThenElse c e1 e2 =>
        let (x, xGen) := eval gen c
        if x then eval xGen e1 else eval xGen e2
    | Expr.and n m =>
        let (x, xGen) := eval gen n
        let (y, yGen) := eval xGen m
        (x && y, yGen)
    | Expr.or n m =>
        let (x, xGen) := eval gen n
        let (y, yGen) := eval xGen m
        (x || y, yGen)
    | Expr.not n =>
        let (x, xGen) := eval gen n
        if x then (false, xGen) else (true, xGen)
    | Expr.roll n =>
        (List.range sampleSize).foldl
          (fun (listAccu, generator) _ =>
            let (roll, newGen) := diceRolli generator n
            (roll::listAccu, newGen))
          (([], gen))
    | Expr.prob f xs => prob f (eval gen xs)


#eval eval (mkStdGen 200) (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))
#eval diceRolli (mkStdGen 200) 5
#eval eval (mkStdGen 200) (Expr.add (Expr.roll 3) (Expr.roll 3))

def tests :=
  let (r, _) := eval (mkStdGen 200) (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))
  [r == [33]]
