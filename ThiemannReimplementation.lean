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
  | end' : Session
  | internalChoice : (Fin k -> Session) -> Session
  | externalChoice : (Fin k -> Session) -> Session
open Session

#check (·  + 1)

def binaryp := _? int $ _? int $ _! int end'
def unaryp := _? int $ _! int end'
def arithp (i : Fin 2) := match i with
    | 0 => binaryp
    | 1 => unaryp

-- def ari := _


def dual
    | _! t s => _? t $ dual s
    | _? t s => _! t $ dual s
    | end' => end'
    | internalChoice sessionSelector => externalChoice (fun label => dual $ sessionSelector label)
    | externalChoice sessionSelector => internalChoice (fun label => dual $ sessionSelector label)

#check dual unaryp

abbrev Type'.de
    | int => Int
    | bool => Bool
#check bool.de

inductive Cmd (State : Type) : Session -> Type
    | close : Cmd State end'
    | send :
        (State -> State × de Payload) ->
            Cmd State ContSession ->
                Cmd State (_! Payload ContSession)
    | recv :
        (de Payload -> State -> State) ->
            Cmd State ContSession ->
                Cmd State (_? Payload ContSession)
    | select :
        (label : Fin k) ->
            Cmd State (SessionSelector label) ->
                Cmd State (internalChoice SessionSelector)
    | choice :
        ((label : Fin k) -> Cmd State (SessionSelector label)) ->
            Cmd State (externalChoice SessionSelector)
    | dynamicSelect :
          (getLabel : State -> State × Fin k) ->
                  ((label : Fin k) -> Cmd State (SessionSelector label)) ->
                      Cmd State (internalChoice SessionSelector)
open Cmd


-- def negateServer : Cmd Int (_? int end') :=
    -- recv (fun payload state => payload) close

def negateServer :=
    recv (fun (operand : int.de) _ => operand) <|
        send (fun state => (state, -state)) close

def additionServer :=
    recv (fun (l : int.de) _ => l) <|
        recv (fun r l => l + r) <|
            send (fun sum => (sum, sum)) close

-- Had to change arithp to (externalChoice arithp). Error in paper? Smart constructor that smart?
def selectArityServer : Cmd Int (externalChoice arithp) :=
    choice (fun label =>
                match label with
                    | Fin.mk 0 _ => additionServer
                    | Fin.mk 1 _ => negateServer)





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
        | select label cmd, state, ch =>
            do
                chApi.primSend label ch
                exec chApi cmd state ch
        | choice contCmdSelector, state, ch =>
            do
                let label <- chApi.primRecv ch
                let cmd := contCmdSelector label
                exec chApi cmd state ch
        | dynamicSelect getLabel getCmd, state, ch =>
            do
                let (state', label) := getLabel state
                let cmd := getCmd label
                exec chApi cmd state' ch


def boolToF2 (b : Bool) : Fin 2 := match b with
    | false => 0
    | true => 1

def stateIdentity {α : Type} (state : α) :=
    (state, state)



-- dual guarantees correct and easy typing for communication
def dynamicArityClient : Cmd Int (dual (externalChoice arithp)) :=
    dynamicSelect
        (fun aritySelector => ⟨aritySelector, boolToF2 (aritySelector <= 0)⟩ )
        (fun label => match label with
            | 0 =>
                send
                    stateIdentity
                    (send
                        stateIdentity
                        (recv (fun payload _ => payload) close))
            | 1 =>
                send
                    stateIdentity
                    (recv (fun payload _ => payload) close)

        )

def runServer
    {State : Type}
    {session : Session}
    (chApi : ChannelApi)
    (cmd : Cmd State session)
    (state : State) :=
        chApi.primAccept >>= exec chApi cmd state
