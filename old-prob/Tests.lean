import Mathlib.Control.Random
import «Daimpl2024Prob.lean».Approximate
import «Daimpl2024Prob.lean».DeBruijn
import «Daimpl2024Prob.lean».DivideOption
import «Daimpl2024Prob.lean».Fib
import «Daimpl2024Prob.lean».HashMapProb
import «Daimpl2024Prob.lean».ListProb
import «Daimpl2024Prob.lean».PiEstimator
import «Daimpl2024Prob.lean».StateMRandomness
import «Daimpl2024Prob.lean».StdGenRandomness
import «Daimpl2024Prob.lean».VarsAndArrays
import «Daimpl2024Prob.lean».DeBruijnDependent

def f (x: (IO (List Nat) × List Nat)) : IO Bool := do
  let (l, r) := x
  let l <- l
  pure (l == r)

def main : IO Unit := do
  IO.setRandSeed 5

  IO.println ""
  IO.println ""
  IO.println ""
  IO.println ""
  IO.println ""
  IO.println ""
  IO.println "Test results:"
  IO.println ""

  let n := Approximate.tests.length
  let l := Monad.sequence (Approximate.tests.map f)
  let success <- do
    let l <- l
    let e := l.filter id
    pure e.length
  IO.println s!"Approximate: {success}/{n}"

  let printResult := fun (name: String) (l : List Bool) =>
    IO.println s!"{name}: {(l.filter id).length}/{l.length}"

  printResult "DeBruijn" DeBruijn.tests

  DivideOption.doTests

  printResult "Fib" Fib.tests
  printResult "HashMapProb" HashMapProb.tests
  printResult "ListProb" ListProb.tests

  do
    let t <- PiEstimator.doTests
    printResult "PiEstimator" [t]

  printResult "StateMRandomness" StateMRandomness.doTests
  printResult "StdGenRandomness" StdGenRandomness.tests
  printResult "VarsAndArrays" VarsAndArrays.tests
  printResult "DeBruijnDependent" DeBruijnDependent.tests


#eval main
