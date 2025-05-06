inductive Typpi
  | nat : Typpi
  | bool : Typpi
deriving DecidableEq, BEq, Repr

abbrev Typpi.de (typpi : Typpi) : Type :=
  match typpi with
    | .nat => Nat
    | .bool => Bool

-- instance : Repr (Typpi.de x) where
--   reprPrec := fun n m => Std.Format.text " "

abbrev Role := Nat

inductive GlobalProtocol
  | seq : GlobalProtocol -> GlobalProtocol -> GlobalProtocol
  | comm : (sender : Role) -> (receiver : Role) -> Typpi -> GlobalProtocol
  | sum : (conditionExecutor : Role) -> GlobalProtocol -> GlobalProtocol -> GlobalProtocol -- ifThenElse
deriving Repr

-- IfThenElse mit Entscheidung, wer was ausführt
inductive GlobalExpr : Typpi -> Role -> Type
  | comm : GlobalExpr Message sender -> GlobalExpr Message receiver -- one explicit role, either sender or receiver
  | add : GlobalExpr .nat executor -> GlobalExpr .nat executor -> GlobalExpr .nat executor
  | ifThenElse: GlobalExpr .bool conditionExecutor -> GlobalExpr Case casesExecutor -> GlobalExpr Case casesExecutor -> GlobalExpr Case casesExecutor
  -- | const : {Value : Typpi} -> (executor : Role) -> (value : Value.de) -> GlobalExpr Value executor
  | nat : Nat -> GlobalExpr .nat executor -- maybe keep this way without explicit role
  | bool : Bool -> GlobalExpr .bool executor
  -- | place : (executor : Role) -> GlobalExpr Value executor -> GlobalExpr Value executor
deriving Repr

-- def a := place 1 (add (comm (place 2 (nat 5)))) (6))

abbrev GlobalExpr.place (executor : Role) (expr : GlobalExpr Value executor) : GlobalExpr Value executor := expr

inductive LocalProtocol
  | seq : LocalProtocol -> LocalProtocol -> LocalProtocol
  | send : (receiver : Role) -> Typpi -> LocalProtocol
  | sumSend : LocalProtocol -> LocalProtocol -> LocalProtocol -- sends to everyone
  | sumRecv : (sender : Role) -> LocalProtocol -> LocalProtocol -> LocalProtocol
  | recv : (sender : Role) -> Typpi -> LocalProtocol
  | noop : LocalProtocol
deriving Repr

-- Zwei IfThenElse mit Unterscheidung, ob man selbst die "Person" ist, die entscheidet, welcher Branch genommen wird oder ob man nur ein Nachricht bekommt, welche für dich entscheidet, welchen Branch du nehmen sollst
-- Evtl. auch nur mit einem IfThenElse möglich (oder sogar besser)
inductive LocalExpr : LocalProtocol -> Typpi -> Type
  | add : LocalExpr LeftProtocol .nat -> LocalExpr RightProtocol .nat -> LocalExpr (.seq LeftProtocol RightProtocol) .nat
  | send : (receiver : Role) -> LocalExpr Protocol Message -> LocalExpr (.seq Protocol (.send receiver Message)) Message
  | recv : (sender : Role) -> LocalExpr (.recv sender Message) Message
  | IfThenElseSend : LocalExpr ConditionProtocol .bool -> LocalExpr ThenProtocol Case -> LocalExpr ElseProtocol Case -> LocalExpr (LocalProtocol.sumSend ThenProtocol ElseProtocol) Case
  | IfThenElseRecv : (sender : Role) -> LocalExpr ThenProtocol Case -> LocalExpr ElseProtocol Case -> LocalExpr (LocalProtocol.sumRecv sender ThenProtocol ElseProtocol) Case
  -- | const : {Value : Typpi} -> (value : Value.de) -> LocalExpr Protocol executor
  | nat : Nat -> LocalExpr LocalProtocol.noop .nat
  | bool : Bool -> LocalExpr LocalProtocol.noop .bool
  | noop : LocalExpr LocalProtocol.noop _
  | seq : LocalExpr LeftProtocol LeftValue -> LocalExpr RightProtocol RightValue -> LocalExpr (.seq LeftProtocol RightProtocol) RightValue
deriving Repr

abbrev LocalExpr.seq3 (expr1 : LocalExpr Protocol1 _1) (expr2 : LocalExpr Protocol2 _2) (expr3 : LocalExpr Protocol3 Value3) : LocalExpr (LocalProtocol.seq Protocol1 (LocalProtocol.seq Protocol2 Protocol3)) Value3 := LocalExpr.seq expr1 (LocalExpr.seq expr2 expr3)

def x := GlobalExpr.place 1 (GlobalExpr.add (GlobalExpr.nat 5) (GlobalExpr.comm (GlobalExpr.place 2 (GlobalExpr.nat 7))))

#eval x
-- #eval (GlobalExpr.add 5 (GlobalExpr.nat (executor := 5) 2) (GlobalExpr.nat 3))

-- Interpreter für globales Programm (Rollen dann nicht benötigt). Interpreter für lokale Programme sind mehrere Programme gleichzeitig auszuführen (evtl. mit Threads (nicht in StdLib))
-- Globales Programm (mit toString) zu lokalen Lean-Programmen umschreiben
-- Loops (würde vieles ändern)
-- Mehr Expressions, um bessere Beispielprogramme schreiben zu können (gucken, was andere für Programme geschrieben haben)
-- Umschreiben, dass eine Zeile nur eine Operation ist (Liste an Operationen (kein Nesting mehr)). Dadurch abtrennen/schneiden des Programms möglich

-- Changelog-Datei mit Meeting-Beschreibung

-- In zwei Schritten: Erst LocalExpr ohne den Protokoll-Typparameter (damit man sich nicht dependent types rumschlagen muss). Danach richtig
def projection (globalExpr: GlobalExpr Value executor) (target : Role) : (protocol : LocalProtocol) × (LocalExpr protocol Value) :=
  match globalExpr with
    | GlobalExpr.comm (sender := sender) messageExpr =>
      let ⟨_, messageLocalExpr⟩ := projection messageExpr target
      let receiver := executor
      if target == receiver then
        ⟨_, LocalExpr.recv sender⟩
      else if target == sender then
        ⟨_, LocalExpr.send receiver messageLocalExpr⟩
      else
        ⟨_, LocalExpr.noop⟩
    | GlobalExpr.add leftExpr rightExpr =>
      let ⟨_, leftLocalExpr⟩ := projection leftExpr target
      ---
      let ⟨_, rightLocalExpr⟩ := projection rightExpr target
      if executor == target then ⟨_ , leftLocalExpr.add rightLocalExpr⟩ else ⟨_, leftLocalExpr.seq rightLocalExpr⟩
    | GlobalExpr.ifThenElse (conditionExecutor := conditionExecutor) conditionExpr thenExpr elseExpr =>
      let ⟨_, conditionLocalExpr⟩ := projection conditionExpr target
      let ⟨_, thenLocalExpr⟩ := projection thenExpr target
      let ⟨_, elseLocalExpr⟩ := projection elseExpr target
      if target == conditionExecutor then
        ⟨_, LocalExpr.IfThenElseSend conditionLocalExpr thenLocalExpr elseLocalExpr⟩
      else
        ⟨_, LocalExpr.IfThenElseRecv conditionExecutor thenLocalExpr elseLocalExpr⟩
    | (GlobalExpr.nat val) => if executor == target then ⟨_, LocalExpr.nat val⟩ else ⟨_, LocalExpr.noop⟩
    -- | (GlobalExpr.nat number : (GlobalExpr _ other)) => LocalExpr.noop
    | GlobalExpr.bool val => if executor == target then ⟨_, LocalExpr.bool val⟩ else ⟨_, LocalExpr.noop⟩

-- let f := join <| l.intersperse <| ", " ++ Format.line group (nest 1 <| "[" ++ f ++ "]")

def y := GlobalExpr.place 1 (GlobalExpr.add (GlobalExpr.nat 5) (GlobalExpr.comm (GlobalExpr.place 2 (GlobalExpr.nat 7))))
#eval projection y 1

def customLocalExprRepr : (LocalExpr α β) -> Nat -> Std.Format := fun localExpr precedence  =>
    match localExpr with
      | LocalExpr.seq leftExpr rightExpr =>
        let left := customLocalExprRepr leftExpr precedence
        let right := customLocalExprRepr rightExpr precedence
        (left.append (Std.Format.text "; ")).append right
      | LocalExpr.noop => "-"
      | x => Repr.reprPrec x precedence

instance : Repr (LocalExpr α β) where
  reprPrec := customLocalExprRepr

def customLocalProtocolRepr : LocalProtocol -> Nat -> Std.Format := fun localProtocol precedence =>
    match localProtocol with
      | LocalProtocol.seq leftProtocol rightProtocol =>
        ---
        ---
        let left := customLocalProtocolRepr leftProtocol precedence
        let right := customLocalProtocolRepr rightProtocol precedence
        (left.append (Std.Format.text "; ")).append right
      | LocalProtocol.noop => "-"
      | x => reprPrec x precedence

instance : Repr LocalProtocol where
  reprPrec := customLocalProtocolRepr

-- def seqToList (expr : AnyLocalExpr) : List AnyLocalExpr :=
--   match expr with
--     | LocalExpr.seq leftExpr rightExpr =>
--       let leftList := seqToList leftExpr
--       let rightList := seqToList rightExpr
--       leftList ++ rightList
--     | x => [x]


#check inferInstanceAs (Repr String)

def yy := GlobalExpr.place 1 (GlobalExpr.add (GlobalExpr.nat 5) (GlobalExpr.comm (GlobalExpr.place 2 (GlobalExpr.nat 7))))
#eval projection yy 2

def xx := Task.spawn (fun () => 5)

#eval xx.get

inductive InterpretationResult : Type
  | send : {Value : Typpi} -> (receiver : Role) -> Task Value.de -> InterpretationResult
  | recv : {Value : Typpi} -> (sender : Role) -> Value.de -> InterpretationResult


-- def interpret (localExpr : LocalExpr Protocol Value) (k : (LocalExpr Protocol Value) -> Value.de) : Value.de :=
--   match localExpr with
--     |

-- toString hat höhere Präzedenz, also evtl das benutzen (Repr sollte eher wie Code formatiert sein (also wieder "einlesbar"))
-- Netzwerkcode simulieren, um besser alles nachzuvollziehen

-- Why const not possible Repr?
-- comm notwendig? Kann man ja auch implizit entscheiden, oder?
-- Pattern match types? -> type class resolution system
-- LocalProtocol as list (in LocalExpr) -> HList?
-- How to match values (in variables)? -> nicht möglich -> pattern match mit werten könnte man selbst machen

-- ProgramCounter müssen gleich sein, aber können Befehle auf einer Zeile unterschiedlich sein?
-- Wie seqToList? Brauche any-type oder?
