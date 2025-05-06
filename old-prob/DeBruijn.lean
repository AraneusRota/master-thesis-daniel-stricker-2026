import Lean.Data.HashMap

namespace DeBruijn

inductive Typpi
  | nat : Typpi
  | bool : Typpi
  | array (α: Typpi) : Typpi
deriving DecidableEq, BEq

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => List Nat
    | .bool => Bool
    | .array α => List α.de

--abbrev Typpi.de (typpi : Typpi) : Type :=
--  match typpi with
--    | .nat => [Nat]
--    | .bool => Bool

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
  | letin : {t : Typpi} -> Expr t -> Expr β -> Expr β
  | var : Nat -> Expr α
  | newArr : Expr (.array t)
  | insert : Expr (.array t) -> Expr t -> Expr (.array t)
  | set : Expr (.array t) -> Nat -> Expr t -> Expr (.array t)
  | get : Expr (.array t) -> Nat -> Expr t
  | range : Nat -> Expr (.array .nat)
  | map : Expr (.array t) -> (t.de -> s.de) -> Expr (.array s)
-- deriving Repr

def hello := fun hell : Nat => 5

--#eval Expr.const 10

def coinFlip : IO Bool := do
  let x <- IO.rand 0 1
  pure (x == 0)

def diceRoll (d : Nat) : IO Nat :=
  IO.rand 1 d

def typeof (_ : α) : Type := α

-- def fi (fifi: Nat) (fififi: Nat) : Option Nat := (5 + fifi)

-- limitation: cant pass .nat to roll because we don't know how to convert .nat to Nat
-- coin flip should contain booleans for reasonable semantics. Usually you don't want to add coin flips
-- booleans seem kind of useless, because you cant compare anything with random numbers
-- prob only works with lambda expressions written in the lean programming language
def eval (exp : Expr x) (env: List ((α : Typpi) × α.de)) : Option x.de :=
  match exp with
    | Expr.const n => [n]
    | Expr.bool n => n
    | Expr.map arrExpr f => do
        let arr <- eval arrExpr env
        arr.map f
    | Expr.range n =>
      some ((List.range n).map ([·]))
    -- | Expr.emptyArr t => some []
    | Expr.newArr => some []
    -- | Expr.set arrExpr n valExpr => do
    --       let arr <- eval arrExpr env
    --       let val <- eval valExpr env
    --       arr.set n val
    | Expr.insert arrExpr valExpr => do
        let arr <- eval arrExpr env
        let val <- eval valExpr env
        arr.append [val]
    | Expr.get arrExpr n => do
          let arr <- eval arrExpr env
          arr.get? n
    | Expr.set arrExpr n valExpr => do
          let arr <- eval arrExpr env
          let val <- eval valExpr env
          arr.set n val
    | Expr.letin (t := typpi) varExpr e =>
        do
          let varValue <- eval varExpr env
          let varEnv := ⟨typpi, varValue⟩ :: env
          let eValue <- eval e varEnv
          pure eValue
    | Expr.var varIndex =>
        match env.get? varIndex with
          | some ⟨typpi, v⟩ =>
            if cast : typpi = x then cast ▸ v else none
          | none => none
    | Expr.add n m => do
          let xs <- eval n env
          let ys <- eval m env
          List.join (List.map (fun x => List.map (fun y => x + y) (ys)) (xs))
    | Expr.sub n m => do
          let xs <- eval n env
          let ys <- eval m env
          List.join (List.map (fun x => List.map (fun y => x - y) (ys)) (xs))
    | Expr.ifThenElse c e1 e2 => do
          let cVal <- eval c env
          let e1Val <- eval e1 env
          let e2Val <- eval e2 env
          if cVal then e1Val else e2Val
    | Expr.and n m => do
          let nVal <- eval n env
          let mVal <- eval m env
          nVal && mVal
    | Expr.or n m => do
          let nVal <- eval n env
          let mVal <- eval m env
          nVal || mVal
    | Expr.not n => do
          let nVal <- eval n env
          !nVal
    | Expr.coinFlip => [0, 1]
    | Expr.roll n => List.map (fun x => x + 1) (List.range n)
    | Expr.probEq n xs => do
          let xsVal <- eval xs env
          [((List.length (List.filter (fun x => x == n) xsVal) * 100) / List.length xsVal)]
    | Expr.probGt n xs => do
          let xsVal <- eval xs env
          [((List.length (List.filter (fun x => x > n) xsVal) * 100) / List.length xsVal)]
    | Expr.probGe n xs => do
          let xsVal <- eval xs env
          [((List.length (List.filter (fun x => x >= n) xsVal) * 100) / List.length xsVal)]
    | Expr.prob f xs => do
          let xsVal <- eval xs env
          [((List.length (List.filter f xsVal) * 100) / List.length xsVal)]

def two := Expr.const 2
def arr := (Expr.insert (Expr.newArr) (Expr.const 1))
#eval eval (Expr.insert arr two) []
-- #eval eval (Expr.letin "a" (.array .nat) (Expr.newArr .nat) (Expr.get (Expr.var "a") 0)) []
-- #eval eval (((Expr.insert (Expr.const 0) (Expr.newArr .nat))) : Expr (.array .nat)) []

#eval eval (Expr.insert (Expr.newArr) arr) []

#eval eval (((Expr.map (Expr.range 5) (·.map (· + 7)))) : Expr (.array .nat)) []

def boolArr := (Expr.insert (Expr.newArr) (Expr.bool false))
#eval eval (((Expr.map boolArr (if · then [0] else [1]))) : Expr (.array .nat)) []

#eval eval (Expr.letin (Expr.bool true) (Expr.and (Expr.bool true) (Expr.var 0))) []

#eval eval (Expr.letin (Expr.bool true) (Expr.add (Expr.const 3) (Expr.var 0))) []

def vEq4 := Expr.probEq (4) (Expr.add (Expr.var 0) (Expr.roll 3))
#eval eval (Expr.letin (Expr.roll 3) vEq4) []
#eval eval (Expr.letin (Expr.roll 3) (Expr.letin (Expr.roll 4) vEq4)) []
#eval eval (Expr.letin (Expr.roll 4) (Expr.letin (Expr.roll 3) vEq4)) []

-- Was showing shadowing but De Bruijn doesn't support shadowing
-- #eval eval (Expr.letin "x" (Expr.const 6) (Expr.letin "x" (Expr.const 5) (Expr.var (α := .nat) "x"))) []

def q := (Expr.letin (Expr.const 6) (Expr.letin (Expr.const 5) (Expr.var (α := .nat) 0)))
#eval eval (Expr.letin (Expr.const 4) (Expr.add q (Expr.var 0))) []

def letti : Expr .nat := (Expr.letin (Expr.roll 2) (Expr.add (Expr.var 0) (Expr.var 1)))
def vEq42 := Expr.probEq (4) (Expr.add (Expr.var 0) letti)
#eval eval (Expr.letin (Expr.roll 3) vEq42) []

#eval eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) []

def tests := [
      (eval (Expr.insert (Expr.newArr) arr) []) == (some [[[1]]]),
      (eval (((Expr.map (Expr.range 5) (·.map (· + 7)))) : Expr (.array .nat)) []) == some [[7], [8], [9], [10], [11]],
      (eval (((Expr.map boolArr (if · then [0] else [1]))) : Expr (.array .nat)) []) == some [[1]],
      (eval (Expr.letin (Expr.bool true) (Expr.and (Expr.bool true) (Expr.var 0))) []) == some true,
      eval (Expr.letin (Expr.roll 4) (Expr.letin (Expr.roll 3) vEq4)) [] == some [33],
      eval (Expr.letin (Expr.const 4) (Expr.add q (Expr.var 0))) [] == some [9],
      eval (Expr.letin (Expr.roll 3) vEq42) [] == some [16],
      eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) [] == some [33],
]

-- #eval eval (Expr.add (Expr.roll 3) (Expr.roll 3))
-- #eval eval (Expr.prob (fun x => x == 4) (Expr.add (Expr.roll 3) (Expr.roll 3)))

def fibbi (n : Nat) : Nat :=
  if n < 2 then n else fibbi (n - 1) + fibbi (n - 2)

def main : IO Unit := do
  IO.println "hello"
