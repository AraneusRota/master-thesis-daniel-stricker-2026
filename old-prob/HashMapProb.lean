import Lean.Data.HashMap

namespace HashMapProb

inductive Typpi
  | nat : Typpi
  | bool : Typpi

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => Lean.HashMap Nat Nat
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
  | probEq : Nat -> Expr .nat -> Expr .nat
  | probGt : Nat -> Expr .nat -> Expr .nat
  | probGe : Nat -> Expr .nat -> Expr .nat
  | prob : (Nat -> Bool) -> Expr .nat -> Expr .nat


def prob (pred: Nat -> Bool) (m: Typpi.nat.de) : Typpi.nat.de :=
  let allFreqSum := Lean.HashMap.fold (fun accu _ freq => accu + freq) 0 m
  let filteredFreqSum := Lean.HashMap.fold (fun acc outcome fr => if pred outcome then acc + fr else acc) 0 m
  let probability := (filteredFreqSum * 100) / allFreqSum
  Lean.HashMap.insert Lean.mkHashMap probability 1

-- limitation: cant pass .nat to roll because we don't know how to convert .nat to Nat
-- booleans seem kind of useless, because you cant compare anything with random numbers
-- sub is analogous to add
-- prob only works with lambda expressions written in the lean programming language
def eval (exp : Expr x) : x.de :=
  match exp with
    | Expr.const n => Lean.HashMap.insert (Lean.mkHashMap) n 1
    | Expr.bool n => n
    | Expr.add n m =>
        let xs := eval n
        let ys := eval m
        Lean.HashMap.fold
          (fun outerMapped outerOutcome outerFreq =>
            Lean.HashMap.fold
              (fun innerMapped innerOutcome innerFreq =>
                let sumOutcome := outerOutcome + innerOutcome
                let mulFreq := outerFreq * innerFreq

                let (modHashMap, maybeCurrentFreq) := Lean.HashMap.insertIfNew innerMapped sumOutcome mulFreq
                match maybeCurrentFreq with
                  | some currentFreq => Lean.HashMap.insert innerMapped sumOutcome (currentFreq + mulFreq)
                  | none => modHashMap
              )
              outerMapped
              ys)
          Lean.mkHashMap
          xs
    | Expr.ifThenElse c e1 e2 =>
        if eval c then eval e1 else eval e2
    | Expr.and n m =>
        eval n && eval m
    | Expr.or n m =>
        eval n || eval m
    | Expr.not n => !(eval n)
    | Expr.roll n => List.foldl (fun acc x => Lean.HashMap.insert acc (x + 1) 1) Lean.mkHashMap (List.range n)
    | Expr.probEq n xs => prob (fun x => x == n) (eval xs)
    | Expr.probGt n xs => prob (fun x => x > n) (eval xs)
    | Expr.probGe n xs => prob (fun x => x >= n) (eval xs)
    | Expr.prob f xs => prob f (eval xs)


instance [Repr α] [Repr β] [BEq α] [Hashable α]: Repr (Lean.HashMap α β) where
  reprPrec := fun m n => Repr.reprPrec (Lean.HashMap.toList m) n

def egg := eval (Expr.add (Expr.roll 3) (Expr.roll 3))
#eval egg

#eval eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3)))
#eval eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))

def test1 :=
  let v : Lean.HashMap Nat Nat := (eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))))
  v.find! 33 == 1

def test2 :=
  let v := eval (Expr.add (Expr.roll 3) (Expr.roll 3))
  ([(6, 1), (5, 2), (4, 3), (3, 2), (2, 1)].map (fun (l, r) => v.find! l == r)).all id

def tests := [
  test1,
  (eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))).find! 33 == 1,
  test2
]
