import Lean.Data.HashMap

namespace DeBruijnDependent



inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
| nil : HList β []
| cons : β i → HList β is → HList β (i :: is)

#eval [1, 2, 3].map (· + 1)


infix:67 " :: " => HList.cons

notation "[" "]" => HList.nil

inductive Member : α → List α → Type
| head : Member a (a::as)
| tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
| a::as, .head => a
| a::as, .tail h => as.get h


open Member

inductive Typpi
  | nat : Typpi
  | bool : Typpi
deriving DecidableEq, BEq

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => List Nat
    | .bool => Bool

#reduce [.nat, .bool, .nat].map Typpi.de


inductive Expr : Typpi -> List Typpi -> Type
  | const : {xs : List Typpi} -> Nat -> Expr .nat xs
  | bool : Bool -> Expr .bool xs
  | add : Expr .nat xs -> Expr .nat xs -> Expr .nat xs
  | sub : Expr .nat xs -> Expr  .nat xs -> Expr .nat xs
  | ifThenElse : Expr .bool xs -> Expr x xs -> Expr x xs -> Expr x xs
  | and : Expr .bool xs -> Expr .bool xs -> Expr .bool xs
  | or : Expr .bool xs -> Expr .bool xs -> Expr .bool xs
  | not : Expr .bool xs -> Expr .bool xs
  | coinFlip : Expr .nat xs
  | roll : Nat -> Expr .nat xs
  | probEq : Nat -> Expr .nat xs -> Expr .nat xs
  | probGt : Nat -> Expr .nat xs -> Expr .nat xs
  | probGe : Nat -> Expr .nat xs -> Expr .nat xs
  | prob : (Nat -> Bool) -> Expr .nat xs -> Expr .nat xs
  | letin : {t : Typpi} -> Expr t xs -> Expr β (t::xs) -> Expr β xs
  | var : Member x xs -> Expr x xs

def typeof (_ : α) : Type := α

-- type system works
def typeSystemWorks : Expr .nat [] :=
      Expr.letin (Expr.const 1)
            (Expr.letin (Expr.const 3)
                  (Expr.letin (Expr.const 2)
                        (Expr.add (Expr.const 4) (Expr.var (tail (tail head))))))

def eval (exp : Expr x xs) (env: HList Typpi.de xs) : x.de :=
  match exp with
    | Expr.const n => [n]
    | Expr.bool n => n
    | Expr.letin varExpr e =>
          let varValue := eval varExpr env
          let varEnv := HList.cons varValue env
          eval e varEnv
    | Expr.var mem =>
        HList.get env mem
    | Expr.add n m =>
          let xs := eval n env
          let ys := eval m env
          List.join (List.map (fun x => List.map (fun y => x + y) (ys)) (xs))
    | Expr.sub n m =>
          let xs := eval n env
          let ys := eval m env
          List.join (List.map (fun x => List.map (fun y => x - y) (ys)) (xs))
    | Expr.ifThenElse c e1 e2 =>
          let cVal := eval c env
          let e1Val := eval e1 env
          let e2Val := eval e2 env
          if cVal then e1Val else e2Val
    | Expr.and n m =>
          let nVal := eval n env
          let mVal := eval m env
          nVal && mVal
    | Expr.or n m =>
          let nVal := eval n env
          let mVal := eval m env
          nVal || mVal
    | Expr.not n =>
          let nVal := eval n env
          !nVal
    | Expr.coinFlip => [0, 1]
    | Expr.roll n => List.map (fun x => x + 1) (List.range n)
    | Expr.probEq n xs =>
          let xsVal := eval xs env
          [((List.length (List.filter (fun x => x == n) xsVal) * 100) / List.length xsVal)]
    | Expr.probGt n xs =>
          let xsVal := eval xs env
          [((List.length (List.filter (fun x => x > n) xsVal) * 100) / List.length xsVal)]
    | Expr.probGe n xs =>
          let xsVal := eval xs env
          [((List.length (List.filter (fun x => x >= n) xsVal) * 100) / List.length xsVal)]
    | Expr.prob f xs =>
          let xsVal := eval xs env
          [((List.length (List.filter f xsVal) * 100) / List.length xsVal)]

#eval eval (Expr.letin (Expr.bool true) ((Expr.and (Expr.bool true) (Expr.var head)))) []

def vEq4 : Expr .nat (.nat :: __) := Expr.probEq (4) (Expr.add (Expr.var head) (Expr.roll 3))
#eval eval (Expr.letin (Expr.roll 3) vEq4) []
#eval eval (Expr.letin (Expr.roll 3) (Expr.letin (Expr.roll 4) vEq4)) []
#eval eval (Expr.letin (Expr.roll 4) (Expr.letin (Expr.roll 3) vEq4)) []

-- Was showing shadowing but De Bruijn doesn't support shadowing
-- #eval eval (Expr.letin "x" (Expr.const 6) (Expr.letin "x" (Expr.const 5) (Expr.var (α := .nat) "x"))) []

def q : Expr .nat __ := (Expr.letin (Expr.const 6) (Expr.letin (Expr.const 5) (Expr.var head)))
#eval eval (Expr.letin (Expr.const 4) (Expr.add q (Expr.var head))) []

def letti : Expr .nat (.nat :: __) := (Expr.letin (Expr.roll 2) (Expr.add (Expr.var head) (Expr.var (tail head))))
def vEq42 : Expr .nat (.nat :: __) := Expr.probEq (4) (Expr.add (Expr.var head) letti)
#eval eval (Expr.letin (Expr.roll 3) vEq42) []

#eval eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) []

def tests := [
      eval (Expr.letin (Expr.bool true) ((Expr.and (Expr.bool true) (Expr.var head)))) [] == true,
      eval (Expr.letin (Expr.roll 4) (Expr.letin (Expr.roll 3) vEq4)) [] == [33],
      eval (Expr.letin (Expr.const 4) (Expr.add q (Expr.var head))) [] == [9],
      eval (Expr.letin (Expr.roll 3) vEq42) [] == [16],
      eval (Expr.probEq (4) (Expr.add (Expr.roll 3) (Expr.roll 3))) [] == [33],
]
