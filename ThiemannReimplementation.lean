-- Intrinsically Typed Sessions with Callbacks (Functional Pearl)

-- 2.0 usual implementation --

inductive Type'
  | int : Type'
  | bool : Type'
deriving DecidableEq, BEq, Repr
open Type'

-- inductive Session (n : Nat) where
-- difference n after or before colon
inductive Session : (n : Nat) -> Type where
  | _! : Type' -> Session n -> Session n
  | _? : Type' -> Session n -> Session n
  | end' : Session n
  | internalChoice : (Fin k -> Session n) -> Session n
  | externalChoice : (Fin k -> Session n) -> Session n
  | μ  : Session (n + 1) -> Session n
  | _' : Fin n -> Session n
open Session

inductive HListS : List (Type') → Type
  | nil  : HListS []
  | cons : (α : Type')  → HListS αs → HListS (α::αs)

def x : HListS [int, int, bool] := sorry


#check (·  + 1)

-- def binaryp := _? int $ _? int $ _! int end'
def unaryp (s : Session n) : Session n := _? int $ _! int s
-- def selectRecurseOrEnd (i : Fin 2) := match i with
    -- | 0 => unaryp $ _' (Fin.mk 0)
    -- | 1 => end'

def manyUnaryp : Session 0 :=
    μ (externalChoice ( fun (i : Fin 2) => match i with
        | 0 => unaryp $ _' 0
        | 1 => end'
    ))



-- def arithp' (i : Fin 2) := match i with
    -- | 0 => binaryp
    -- | 1 => unaryp
-- def arithp := externalChoice arithp'

-- def ari := _


def dual (session : Session n) : Session n := match session with
    | _! t s  => _? t $ dual s
    | _? t s => _! t $ dual s
    | end' => end'
    | internalChoice sessionSelector => externalChoice (fun label => dual $ sessionSelector label)
    | externalChoice sessionSelector => internalChoice (fun label => dual $ sessionSelector label)
    | μ body => μ $ dual body
    | _' i => _' i
def test : Session 0 := dual $ unaryp end'

abbrev Type'.de
    | int => Int
    | bool => Bool
#check bool.de

inductive Cmd (State : Type) : (n : Nat) -> Session n -> Type
    | close : Cmd State n end'
    | send :
        (State -> State × de Payload) ->
            Cmd State n ContSession ->
                Cmd State n (_! Payload ContSession)
    | recv :
        (de Payload -> State -> State) ->
            Cmd State n ContSession ->
                Cmd State n (_? Payload ContSession)
    | select :
        (label : Fin k) ->
            Cmd State n (SessionSelector label) ->
                Cmd State n (internalChoice SessionSelector)
    | choice :
        ((label : Fin k) -> Cmd State n (SessionSelector label)) ->
            Cmd State n (externalChoice SessionSelector)
    | dynamicSelect :
          (getLabel : State -> State × Fin k) ->
                  ((label : Fin k) -> Cmd State n (SessionSelector label)) ->
                      Cmd State n (internalChoice SessionSelector)
    | loop : Cmd State (n + 1) Body -> Cmd State n (μ Body)
    | continue' : (i : Fin n) -> Cmd State n (_' i)
    | unroll :
        Cmd State (n + 1) ContSession ->
            Cmd State n (μ ContSession) ->
                Cmd State n (μ ContSession)
open Cmd

def finToNat (i : Fin n) : Nat := i

def abEq (A B : Type) (a : A) (ab : A = B): B :=
              cast ab a





-- def push'
--         (stack : CmdStack size State)
--         (cmd : Cmd State size Continuation)
--         : CmdStack (size + 1) State :=
--     fun (i : Fin (size + 1)) =>
--         if h: i = 0 then
--             by subst i; exact

            -- have h' : opposite i = (size + 1) := by simp
            -- let toNFromN {size : Nat} :=
                -- fun n => Fin.toNat (n:=size) $ ⟨n, _⟩
            -- have h' : size = i.rev.toNat := by rw [toNFromN]
            -- have h' : size = i.rev.toNat := by apply
            -- have h' : size = i.rev.toNat := by
                -- rw [h]
                -- simp [Fin.rev, Fin.toNat]
            -- let con : Session size := ...

            -- have h' : size = i.rev.toNat := by
            --     rw [h]
            --     simp [Fin.rev, Fin.toNat]
            -- have h1 : i.rev.toNat = size := by
            --                 rw [h]
            --                 simp [Fin.rev, Fin.toNat]
            -- have h'' : Session size = Session i.rev.toNat :=
            --     congrArg Session h'
            -- have h2 : Session i.rev.toNat = Session size :=
            --     congrArg Session h1
            -- -- have h''' : Continuation = (cast h'' Continuation) := by
            --     -- simp [h2]

            -- -- have h'''' : Cmd State size Continuation = Cmd State i.rev.toNat (cast h'' Continuation) := by
            --     -- rw [←congrArg (Cmd State i.rev.toNat)]
            -- have zero : @Fin.val (size + 1) i = 0 := by
            --     simp [h]

            -- have hSize : size + 1 - (↑i + 1) = size := by
            --     simp [zero]

            -- have p : Cmd State size Continuation = Cmd State i.rev.toNat (cast h'' Continuation) := by
            --     simp
            --     rw [hSize]



            -- let x : Session i.rev.toNat := cast h' Continuation
            -- have Continuation : Session size
            -- let cont := h'' ▸ Continuation
            -- let cmd' := p ▸ cmd
        --     ⟨Continuation, cmd⟩
        -- else
        --     sorry

-- def push'
  -- (cms : CmdStack n A)
  -- (cmd : Cmd A n S) : CmdStack (n + 1) A :=
  -- fun i =>
    -- if h : i = 0 then
      -- -- index 0: we insert the new command
      -- have h' : opposite i = n := by sorry
      -- ⟨S, cmd⟩
    -- else
      -- -- i ≠ 0: reduce i to i.pred and delegate to previous stack
      -- let j : Fin n := ⟨i.val - 1, Nat.sub_lt (Fin.pos i) (Nat.zero_lt_succ _)⟩
      -- cms j

-- def push'
  -- (cms : CmdStack size A)
  -- (cmd : Cmd A size S) : CmdStack (size + 1) A
-- | ⟨0, _⟩      => ⟨S, cmd⟩
-- | ⟨k+1, h⟩    => cms ⟨k, Nat.lt_of_succ_lt_succ h⟩

-- def push'
        -- (stack : CmdStack size State)
        -- (cmd : Cmd State (size) Continuation)
        -- : CmdStack (size + 1) State :=
    -- fun (i : Fin (size + 1)) {ithSession : Session (opposite i)} =>
        -- sorry
        -- if h: i < size then
            -- -- let h :=
            -- let i' : Fin size := i.castLT h
            -- let h' := i = i'
            -- stack i' (ithSession:=ithSession)
        -- else
            -- cmd

def CmdStack (size : Nat) (State : Type) := (i : Fin size) ->
    Σ session, Cmd State (size - (i.toNat + 1)) session

def push
        (stack : CmdStack size State)
        (cmd : Cmd State size Continuation)
        : CmdStack (size + 1) State
    | ⟨0, _⟩ =>
        ⟨Continuation, cmd⟩
    | ⟨i + 1, _⟩ =>
        -- stack i
        -- let i' : Fin size := ⟨i, _⟩
        have i_is_in_smaller_fin : i < size := by omega
        let oldStackEntry : Σ session, Cmd State (size - (i + 1)) session := stack ⟨i, i_is_in_smaller_fin⟩

        have size_simplification : (size - (i + 1)) = (size + 1 - (i + 1 + 1)) := by omega
        -- by simp [Fin.toNat] ; exact h ▸ s
        size_simplification ▸ oldStackEntry

def pop1 (stack : CmdStack (newSize + 1) State) : CmdStack newSize State
    | ⟨i, _⟩ =>
        have h : i < newSize + 1 := by omega
        let fin : Fin (newSize + 1) := ⟨i, h⟩
        let s : Σ session, Cmd State ((newSize + 1) - (i + 1)) session := stack fin
        by simp; exact s

def pop
        (stack : CmdStack (size + 1) State)
        (i : Fin (size + 1))
        : CmdStack (i.rev.toNat + 1) State :=
    sorry


def addupCommand (cmd : Cmd Int n s) : Cmd Int n (unaryp s) :=
    recv (fun payload state => payload + state) $
        send (fun state => (state, state)) $
            cmd
def runningSumCommand : Cmd Int 0 manyUnaryp :=
    loop $
        choice fun (i : Fin 2) => match i with
            | 0 => addupCommand (continue' 0)
            | 1 => close

def runningSumClient : Cmd Int 0 (dual manyUnaryp) :=
    unroll (
        select 0 $
        send (fun x => (x, 17)) $
        recv (fun payload _ => payload) $
        continue' 0) $
    unroll (
        select 0 $
        send (fun x => (x, 4)) $
        recv (fun payload _ => payload) $
        continue' 0) $
    loop (select 1 close)



-- def negateServer : Cmd Int (_? int end') :=
    -- recv (fun payload state => payload) close

-- def negateServer :=
    -- recv (fun (operand : int.de) _ => operand) <|
        -- send (fun state => (state, -state)) close
--
-- def additionServer :=
    -- recv (fun (l : int.de) _ => l) <|
        -- recv (fun r l => l + r) <|
            -- send (fun sum => (sum, sum)) close

-- -- Had to change arithp to (externalChoice arithp). Error in paper? Smart constructor that smart?
-- def selectArityServer : Cmd Int (externalChoice arithp) :=
    -- choice (fun label =>
                -- match label with
                    -- | Fin.mk 0 _ => additionServer
                    -- | Fin.mk 1 _ => negateServer)

def CmdCont (State : Type) : Type :=
    Σ n, CmdStack (n + 1) State × State


-- Lean channels or IO channels to implement
structure ChannelApi where
    Channel : Type
    primAccept : IO Channel
    primClose : Channel -> IO Unit
    primSend : State -> Channel -> IO Unit
    primRecv : Channel -> IO State
-- def chApiImpl : ChannelApi := ⟨...⟩

def exec (chApi : ChannelApi) :
     Cmd State n ContSession -> CmdStack n State -> State -> chApi.Channel -> IO (CmdCont State ⊕ State)
        | close, stack, state, ch =>
            do
                chApi.primClose ch
                pure (Sum.inr state)
        | send getFromState k, stack, state, ch =>
            do
                let (state', payload) := getFromState state
                chApi.primSend payload ch
                exec chApi k stack state' ch
        | recv putInState k, stack, state, ch =>
            do
                let payload <- chApi.primRecv ch
                let state' := putInState payload state
                exec chApi k stack state' ch
        | select label cmd, stack, state, ch =>
            do
                chApi.primSend label ch
                exec chApi cmd stack state ch
        | choice contCmdSelector, stack, state, ch =>
            do
                let label <- chApi.primRecv ch
                let cmd := contCmdSelector label
                exec chApi cmd stack state ch
        | dynamicSelect getLabel getCmd, stack, state, ch =>
            do
                let (state', label) := getLabel state
                let cmd := getCmd label
                exec chApi cmd stack state' ch
        | loop cmd, stack, state, ch =>
            let stack' := push stack $ loop cmd
            exec chApi cmd stack' state ch
        | unroll bodyCmd nextCmd, stack, state, ch =>
            let stack' := push stack nextCmd
            exec chApi bodyCmd stack' state ch
        | continue' i, stack, state, ch =>
            match n with
                | 0 => exec chApi close stack state ch -- should not be possible. How to enforce?
                | _ + 1 =>
                    pure $ Sum.inl ⟨_, (pop stack i, state)⟩


-- def boolToF2 (b : Bool) : Fin 2 := match b with
    -- | false => 0
    -- | true => 1
--
-- def stateIdentity {α : Type} (state : α) :=
    -- (state, state)
--
--
--
-- -- dual guarantees correct and easy typing for communication
-- def dynamicArityClient : Cmd Int (dual (externalChoice arithp)) :=
    -- dynamicSelect
        -- (fun aritySelector => ⟨aritySelector, boolToF2 (aritySelector <= 0)⟩ )
        -- (fun label => match label with
            -- | 0 =>
                -- send
                    -- stateIdentity
                    -- (send
                        -- stateIdentity
                        -- (recv (fun payload _ => payload) close))
            -- | 1 =>
                -- send
                    -- stateIdentity
                    -- (recv (fun payload _ => payload) close)
--
        -- )
--
-- def runServer
    -- {State : Type}
    -- {session : Session}
    -- (chApi : ChannelApi)
    -- (cmd : Cmd State session)
    -- (state : State) :=
        -- chApi.primAccept >>= exec chApi cmd state
