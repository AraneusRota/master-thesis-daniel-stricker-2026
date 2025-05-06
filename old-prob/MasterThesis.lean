import Lean.Data.HashMap

namespace MasterThesis

inductive Typpi
  | real : Typpi
  | bool : Typpi
deriving DecidableEq, BEq

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .real => Float
    | .bool => Bool


inductive Expr : Typpi -> Type
  | lit : Float -> Expr .real
  | var : String -> Expr a
  | letin : {t : Typpi} -> String -> Expr t -> Expr a -> Expr a
  | neg : Expr .real -> Expr .real
  | exp : Expr .real -> Expr .real
  | log : Expr .real -> Expr .real
  | not : Expr .bool -> Expr .bool
  | add : Expr .real -> Expr .real -> Expr .real
  | less : Expr .real -> Expr .real -> Expr .bool
  | ifThenElse : Expr .bool -> Expr a -> Expr a -> Expr a

def typeof (_ : α) : Type := α

def eval (expr : Expr x) (env: Lean.HashMap String ((α : Typpi) × α.de)) : Option x.de :=
  match expr with
    | Expr.lit n => [n]
    | Expr.var varName =>
        match env.find? varName with
          | some ⟨typpi, v⟩ =>
            if cast : typpi = x then cast ▸ v else none
          | none => none
    | Expr.letin (t := typpi) varName varExpr e =>
        do
          let varValue <- eval varExpr env
          let varEnv := env.insert varName ⟨typpi, varValue⟩
          let eValue <- eval e varEnv
          pure eValue
    | Expr.neg => _
    | Expr.exp => _
    | Expr.log => _
    | Expr.not n => do
        let nVal <- eval n env
        !nVal
    | Expr.add n m => do
          let xs <- eval n env
          let ys <- eval m env
          List.join (List.map (fun x => List.map (fun y => x + y) (ys)) (xs))
    | Expr.less => _
    | Expr.ifThenElse c e1 e2 => do
          let cVal <- eval c env
          let e1Val <- eval e1 env
          let e2Val <- eval e2 env
          if cVal then e1Val else e2Val
