import Mathlib.Control.Random

namespace PiEstimator

structure Point where
  x : Float
  y : Float
deriving Repr

def randPoint: IO Point := do
  let accuracy := 1000000000
  let rand := IO.rand 0 (accuracy * 2)
  let xUnscaled <- rand
  let yUnscaled <- rand
  let scale := fun (n: Nat) => (n.toFloat / accuracy.toFloat) - 1
  let x := scale xUnscaled
  let y := scale yUnscaled
  pure {x, y}

partial def range (n: Nat) (acc: List Nat): List Nat := match n with
  | 0 => acc
  | _ => range (n - 1) ((n - 1) :: acc)

def pi (n : Nat) : IO Float := do
  let points <- Monad.sequence (List.map (fun _ => randPoint) (List.range n))
  let radii :=
    List.map (fun point => (point.x * point.x) + (point.y * point.y)) points
  let inCircle :=
    List.filter (fun radius => radius <= 1) radii
  pure (inCircle.length.toFloat / n.toFloat * 4)

#eval pi 9500


def doTests : IO Bool := do
  let t <- pi 9500
  pure (t > 3.09 && t < 3.19)

inductive Expr
  | const : Nat -> Expr
  | add : Expr -> Expr -> Expr
deriving Repr
#eval Expr.const 10
open Expr
def eval (exp : Expr) : Nat :=
  match exp with
    | const n => n
    | add n m => eval n + eval m

#eval eval (Expr.const 10)
def fibbi (n : Nat) : Nat :=
  if n < 2 then n else fibbi (n - 1) + fibbi (n - 2)

def main : IO Unit :=
  let x := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  for number in x do
    IO.println s!"{fibbi number}"
