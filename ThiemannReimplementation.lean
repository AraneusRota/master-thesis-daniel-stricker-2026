-- Intrinsically Typed Sessions with Callbacks (Functional Pearl)

-- 2.0 usual implementation --

inductive Type'
  | int : Type'
  | bool : Type'
deriving DecidableEq, BEq, Repr
open Type'

inductive Session
  | _! : Type' -> Session -> Session
  | _? : Type' -> Session -> Session
  | _end : Session
open Session

#check (·  + 1)

def binaryp := _? int $ _? int $ _? int _end 
def unaryp := _? int $ _! int _end


def dual
    | _! t s => _? t $ dual s
    | _? t s => _! t $ dual s
    | _end => _end

#eval dual unaryp


-- 2.1 Commands with Callbacks

abbrev Type'.de
    | int => Int
    | bool => Bool
#check bool.de
 
inductive Cmd (State : Type) : Session -> Type
    | close : Cmd State _end
    | send : 
        (State -> State × de Payload) -> 
            Cmd State ContinuationSession -> 
                Cmd State (_! Payload ContinuationSession)
    | recv : 
        (de Payload -> State -> State) -> 
            Cmd State ContinuationSession -> 
                Cmd State (_? Payload ContinuationSession)
open Cmd
    
-- def negateServer : Cmd Int (_? int _end) := 
    -- recv (fun payload state => payload) close
    
def negateServer := 
    recv (fun (operand : int.de) _ => operand) <| 
        send (fun state => (state, -state)) close

def additionServer := 
    recv (fun (l : int.de) _ => l) <|
        recv (fun r l => l + r) <|
            send (fun sum => (sum, sum)) close