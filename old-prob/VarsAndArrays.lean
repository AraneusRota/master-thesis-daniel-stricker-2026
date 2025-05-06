import Lean.Data.HashMap

namespace VarsAndArrays

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
  | letin : {t : Typpi} -> String -> Expr t -> Expr β -> Expr β
  | var : String -> Expr α
  | newArr : Expr (.array t)
  | insert : Expr (.array t) -> Expr t -> Expr (.array t)
  | set : Expr (.array t) -> Nat -> Expr t -> Expr (.array t)
  | get : Expr (.array t) -> Nat -> Expr t
  | range : Nat -> Expr (.array .nat)
  | map : Expr (.array t) -> (t.de -> s.de) -> Expr (.array s)

def typeof (_ : α) : Type := α

def eval (exp : Expr x) (env: Lean.HashMap String ((α : Typpi) × α.de)) : Option x.de :=
  match exp with
    | Expr.const n => [n]
    | Expr.bool n => n
    | Expr.map arrExpr f => do
        let arr <- eval arrExpr env
        arr.map f
    | Expr.range n =>
      some ((List.range n).map ([·]))
    | Expr.newArr => some []
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
    | Expr.letin (t := typpi) varName varExpr e =>
        do
          let varValue <- eval varExpr env
          let varEnv := env.insert varName ⟨typpi, varValue⟩
          let eValue <- eval e varEnv
          pure eValue
    | Expr.var varName =>
        match env.find? varName with
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
#eval eval (Expr.insert arr two) Lean.mkHashMap

#eval eval (Expr.insert (Expr.newArr) arr) Lean.mkHashMap

#eval eval (((Expr.map (Expr.range 5) (·.map (· + 7)))) : Expr (.array .nat)) Lean.mkHashMap

def boolArr := (Expr.insert (Expr.newArr) (Expr.bool false))
#eval eval (((Expr.map boolArr (if · then [0] else [1]))) : Expr (.array .nat)) Lean.mkHashMap

#eval eval (Expr.letin "v" (Expr.bool true) (Expr.and (Expr.bool false) (Expr.var "v"))) Lean.mkHashMap

def vEq4 := Expr.probEq (4) (Expr.add (Expr.var "v") (Expr.roll 3))
#eval eval (Expr.letin "v" (Expr.roll 3) vEq4) Lean.mkHashMap



#eval eval (Expr.letin "x" (Expr.const 6) (Expr.letin "x" (Expr.const 5) (Expr.var (α := .nat) "x"))) Lean.mkHashMap

def q := (Expr.letin "x" (Expr.const 6) (Expr.letin "x" (Expr.const 5) (Expr.var (α := .nat) "x")))
#eval eval (Expr.letin "x" (Expr.const 4) (Expr.add q (Expr.var "x"))) Lean.mkHashMap

def letti : Expr .nat := (Expr.letin "w" (Expr.roll 2) (Expr.add (Expr.var "w") (Expr.var "v")))
def vEq42 := Expr.probEq (4) (Expr.add (Expr.var "v") letti)
#eval eval (Expr.letin "v" (Expr.roll 3) vEq42) Lean.mkHashMap

#eval eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) Lean.mkHashMap

def tests := [
      eval (Expr.insert arr two) Lean.mkHashMap == some [[1], [2]],
      eval (Expr.insert (Expr.newArr) arr) Lean.mkHashMap == some [[[1]]],
      eval (((Expr.map (Expr.range 5) (·.map (· + 7)))) : Expr (.array .nat)) Lean.mkHashMap == some [[7], [8], [9], [10], [11]],
      eval (((Expr.map boolArr (if · then [0] else [1]))) : Expr (.array .nat)) Lean.mkHashMap == some [[1]],
      eval (Expr.letin "v" (Expr.bool true) (Expr.and (Expr.bool false) (Expr.var "v"))) Lean.mkHashMap == some false,
      eval (Expr.letin "v" (Expr.roll 3) vEq4) Lean.mkHashMap == some [33],
      eval (Expr.letin "x" (Expr.const 6) (Expr.letin "x" (Expr.const 5) (Expr.var (α := .nat) "x"))) Lean.mkHashMap == some [5],
      eval (Expr.letin "x" (Expr.const 4) (Expr.add q (Expr.var "x"))) Lean.mkHashMap == some [9],
      eval (Expr.letin "v" (Expr.roll 3) vEq42) Lean.mkHashMap == some [16],
      eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) Lean.mkHashMap == some [33]
]
