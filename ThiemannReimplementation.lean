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
            Cmd State ContSession -> 
                Cmd State (_! Payload ContSession)
    | recv : 
        (de Payload -> State -> State) -> 
            Cmd State ContSession -> 
                Cmd State (_? Payload ContSession)
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

            
-- 2.2 Interpretation

-- Lean channels or IO channels to implement
structure ChannelApi where
    Channel : Type
    primAccept : IO Channel
    primClose : Channel -> IO Unit
    primSend : State -> Channel -> IO Unit
    primRecv : Channel -> IO State    
-- def chApiImpl : ChannelApi := ⟨...⟩  

def exec (chApi : ChannelApi) : 
     Cmd State ContSession -> State -> chApi.Channel -> IO State
        | close, state, ch =>  
            do
                chApi.primClose ch
                pure state
        | send getFromState k, state, ch =>
            do 
                let (state', payload) := getFromState state
                chApi.primSend payload ch
                exec chApi k state' ch
        | recv putInState k, state, ch =>
            do
                let payload <- chApi.primRecv ch 
                let state' := putInState payload state
                exec chApi k state' ch
                 

def runServer
    {State : Type} 
    {session : Session} 
    (chApi : ChannelApi) 
    (cmd : Cmd State session) 
    (state : State) :=
        chApi.primAccept >>= exec chApi cmd state
        
