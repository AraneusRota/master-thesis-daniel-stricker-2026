namespace Fib

def fibbi (n : Nat) : Nat :=
  if n < 2 then n else fibbi (n - 1) + fibbi (n - 2)

def fib'' : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib'' (n + 1) + fib'' (n)


def fibNotSoSimple (n: Nat): Nat :=
  if h : n = 0 then
    0
  else if h' : n = 1 then
    1
  else
    have : 0 < n := by
      cases n with
        | zero => contradiction
        | succ n' => simp_arith

    have : 0 < 2 := by simp_arith
    have : n - 2 < n := by
      apply Nat.sub_lt <;> assumption

    fibNotSoSimple (n - 1) + fibNotSoSimple (n - 2)

def fib (n: Nat): Nat :=
  let rec fib' := fun n a b =>
    if n < 0 then
      0
    else if n = 0 then
      a
    else
      fib' (n - 1) b (a + b)
  fib' n 0 1

#eval fib 17
#eval fibNotSoSimple 17
#eval fibbi 17

def tests := [
  fib 17 == 1597,
  fibNotSoSimple 17 == 1597,
  fibbi 17 == 1597
]
