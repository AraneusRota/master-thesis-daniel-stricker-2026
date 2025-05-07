-- Intrinsically Typed Sessions with Callbacks (Functional Pearl)

-- 2.0 usual implementation --

inductive Type'
  | int : Type'
  | bool : Type'
deriving DecidableEq, BEq, Repr
open Type'

inductive Session
  | send : Type' -> Session -> Session
  | recv : Type' -> Session -> Session
  | ends : Session
open Session

#check (·  + 1)

def binaryp := recv int $ recv int $ recv int ends 
def unaryp := recv int $ send int ends


def dual
    | send t s => recv t $ dual s
    | recv t s => send t $ dual s
    | ends => ends

#eval dual unaryp


-- 2.1 Commands with Callbacks
