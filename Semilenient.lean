import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
open Std













inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
| nil : HList β []
| cons : β i → HList β is → HList β (i :: is)

infix:67 " :: " => HList.cons

notation "[" "]" => HList.nil

inductive NType : Type 1
  | func : (In : NType) -> (Out : NType) -> NType
  | arbitrary : (α : Type) -> NType
  | unit

abbrev NType.de (nType : NType) : Type :=
  match nType with
    | .func In Out => In.de -> Out.de
    | .arbitrary α => α
    | .unit => Unit

inductive NMember : NType → List NType → Type 1
| head : NMember a (a::as)
| tail : NMember a bs → NMember a (b::bs)

-- def HList.get : HList β is → Member i is → β i
-- | a::as, .head => a
-- | a::as, .tail h => as.get h

-- variable {NProcessName: Type} [DecidableEq NProcessName] [ToString NProcessName]
abbrev NProcessName := String

inductive NChoiceLabel where
  | mk : String -> NChoiceLabel
deriving BEq, Hashable


inductive NProcedureName
  | f
  | g
  | h

abbrev NProcedureName.type : NProcedureName -> NType
  | f => NType.arbitrary String
  | g => NType.func (NType.arbitrary String) NType.unit
  | h => NType.arbitrary Nat

abbrev NProcedureName.argumentCount : NProcedureName -> Nat
  | f => 0
  | g => 1
  | h => 2

mutual
  inductive NValue : (processes : List NProcessName) -> (varTypes : List NType) -> (exprType : NType) -> Type 1 where
    | NConst : (a : α) -> NValue processes varTypes (NType.arbitrary α)
    | NUnit : NValue processes varTypes NType.unit
    | NVar : NMember exprType varTypes -> NValue processes varTypes exprType
    | NFun :
      {In : NType} ->
      NProcess processes (In :: varTypes) Out -> -- TODO: check correctness of processes (and also of return type)
      NValue processes varTypes (NType.func In Out)
    | NSend :
      (receiver : NProcessName) ->
      (receiver ∈ processes) ->
      NValue processes varTypes (NType.func Payload NType.unit)
    | NRecv :
      (sender : NProcessName) ->
      (sender ∈ processes) ->
      NValue processes varTypes (NType.func NType.unit Payload)

  inductive NProcess : (processes : List NProcessName) -> (varTypes : List NType) -> (exprType : NType) -> Type 1 where
    | NValueExpr :
      NValue processes varTypes exprType ->
      NProcess processes varTypes exprType
    | NApply :
      NProcess processes varTypes (NType.func In Out) ->
      NProcess processes varTypes In  ->
      NProcess processes varTypes Out
    | NIf :
      NProcess processes varTypes (NType.arbitrary Bool) ->
      NProcess processes varTypes exprType ->
      NProcess processes varTypes exprType ->
      NProcess processes varTypes exprType
    | NOffer :
      (chooser ∈ processes) ->
      (chooser : NProcessName) ->
      ((chosen : NChoiceLabel) -> NProcess processes varTypes exprType) ->
      NProcess processes varTypes exprType
    | NChoose :
      (offerer ∈ processes) ->
      (offerer : NProcessName) ->
      (chosen : NChoiceLabel) ->
      (continuation : NProcess processes varTypes exprType) ->
      NProcess processes varTypes exprType
    | NProcedure : -- not finished
      -- nProcedurs NProcedureName ["q"] _ ->
      (procedure : NProcedureName) ->
      (substitutes : Vector NProcessName procedure.argumentCount) ->
      (substitutes.toList ⊆ processes) ->
      NProcess processes varTypes procedure.type


  -- abbrev NProcedureName.type : NProcedureName -> Type
  --   | f => (a : NProcessName) -> (b : NProcessName) -> NProcess processes varTypes exprType

end



def nProcedures
  (procedure : NProcedureName) :
  (substitutes : Vector NProcessName procedure.argumentCount) ->
  (substitutes.toList ⊆ processes) ->
  NProcess processes varTypes procedure.type :=
    fun substitutes => match procedure with
      | .f => fun h =>
        NProcess.NValueExpr (NValue.NConst "a")
      | .g => fun h =>
        let n := substitutes.head
        -- NProcess.NValueExpr (NValue.NRecv sorry sorry)
        -- NProcess.NValueExpr $ NValue.NFun (In:=NType.unit) (processes:=processes) (varTypes:=varTypes) (NProcess.NValueExpr (NValue.NConst ""))
        NProcess.NValueExpr
          (NValue.NSend n (by
            have h' : n ∈ substitutes.toList := by simp; exact Vector.mem_of_getElem rfl
            have h'' := h h'
            exact h''))
      | .h => fun h => NProcess.NValueExpr (NValue.NConst 1)


abbrev NNetwork processes :=
  List (NProcessName × NProcess processes [] NType.unit)
def testNetwork : NNetwork [] :=
  [("a", NProcess.NValueExpr (NValue.NUnit))]

def evalSingleProcess
  (expr : NProcess processes varTypes exprType)
  (env: HList (NValue processes varTypes) varTypes) -- weglassen und substitution machen, x vllt rauslöschen, weil ja dann nicht mehr da
  : NProcess processes varTypes' exprType :=
  match expr with
    | NProcess.NValueExpr value => sorry
    | NProcess.NApply
          (NProcess.NValueExpr (NValue.NFun funBody))
          (NProcess.NValueExpr argValue) =>
        let newEnv := HList.cons argValue env
        let replacedBody := evalSingleProcess funBody (HList.cons argValue env)
        sorry
    | NProcess.NIf test then' else' => sorry
    | NProcess.NOffer chooser_in_processes chooser choose => sorry
    | NProcess.NChoose offerer_in_processes offerer chosen continuation => sorry
    | NProcess.NProcedure procedure substitutes substitutes_in_processes => sorry



-- def fs := [f, g]
-- def f := Vector NProcessName n -> NProcess processes [] exprType
-- def g := Vector NProcessName m -> NProcess processes [] exprType'

-- abbrev NProcedureName.type : NProcedureName -> Type 1
--     | f =>
--       {processes : List NProcessName} ->
--       (sub1 : NProcessName) ->
--       (sub1 ∈ processes) ->
--       (sub2 : NProcessName) ->
--       (sub2 ∈ processes) ->
--       NProcess processes [] (NType.arbitrary String)
--     | g => {processes : List NProcessName} -> NProcess processes [] NType.unit
--     | h => {processes : List NProcessName} -> NProcess processes [] (NType.arbitrary Nat)


-- abbrev NProcedureName.impl : (procedure : NProcedureName) -> procedure.type
--     | f => fun sub1 h1 sub2 h2 =>
--       NProcess.NApply
--         (NProcess.NValueExpr
--           (NValue.NRecv sub2 h2))
--         (NProcess.NApply
--           (NProcess.NValueExpr (NValue.NSend sub1 h1))
--           (NProcess.NValueExpr (NValue.NConst 5)))
--         -- (NProcess.NApply (NValue.NRecv sub2 h2) (NValue.NUnit))
--     | g => NProcess.NValueExpr $ NValue.NUnit
--     | h =>
--       NProcess.NApply
--         (NProcess.NValueExpr
--           (NValue.NFun (NProcess.NValueExpr (NValue.NVar NMember.head))))
--         (NProcess.NValueExpr
--           (NValue.NConst 5))


-- notation:60 a "@" b "#" c => Located c b a


inductive CType : Type 1
  | func : (In : CType) -> (Out : CType) -> (proxies : List NProcessName) -> CType
  | arbitrary : (α : Type) -> (location : NProcessName) -> CType

abbrev CType.de (cType : CType) : Type :=
  match cType with
    | .func In Out _ => In.de -> Out.de
    | .arbitrary α _ => α

notation:60 α "@" location => CType.arbitrary α location

inductive CMember : CType → List CType → Type 1
| head : CMember a (a::as)
| tail : CMember a bs → CMember a (b::bs)

def HList.cGet : HList β is → CMember i is → β i
| a::as, .head => a
| a::as, .tail h => as.cGet h

-- def Located α := NProcessName × α
-- def located (location : NProcessName) (a : α) : Located α := (location, a)
-- notation:60 α "@" location => Located location α

-- How to implement "dot" from paper?
-- How to procedures?
-- How to access mutually when def etc?
-- Why List not Set

-- def cMentionedProcesses (choreo : CChoreo)

def cMentionedProcessesInTypes (cType : CType) : List NProcessName :=
  match cType with
    | .func In Out proxies =>
      List.append
        proxies
        (List.append
          (cMentionedProcessesInTypes In)
          (cMentionedProcessesInTypes Out))
    | .arbitrary _ location => [location]




inductive CProcedureName
  | g

abbrev CProcedureName.argumentCount : CProcedureName -> Nat
  | g => 1

def CProcedureName.type (name : CProcedureName) (typeLocations : Vector NProcessName name.argumentCount) : CType := match name with
  | g => CType.arbitrary String typeLocations.head



-- def functionProxies : List α := []

mutual
  inductive CValue : (processes : List NProcessName) -> (varTypes : List CType) -> (exprType : CType) -> Type 1 where
    | CConst :
      (a : α) ->
      (location : NProcessName) ->
      (location ∈ processes) ->
      CValue processes varTypes (CType.arbitrary α location)
    | CVar :
      CMember exprType varTypes ->
      CValue processes varTypes exprType
    | CFun :
      {In : CType} ->
      CChoreo processes (In :: varTypes) Out -> -- TODO: check correctness of processes (and also of return type)
      CValue processes varTypes (CType.func In Out functionProxies)

  inductive CChoreo : (processes : List NProcessName) -> (varTypes : List CType) -> (exprType : CType) -> Type 1 where
    | CValueExpr :
      CValue processes varTypes exprType ->
      CChoreo processes varTypes exprType
    | CApply :
      CChoreo processes varTypes (CType.func In Out functionProxies) ->
      CChoreo processes varTypes In ->
      CChoreo processes varTypes Out
    | CIf :
      (location ∈ processes) ->
      CChoreo processes varTypes (CType.arbitrary Bool location) ->
      CChoreo processes varTypes exprType ->
      CChoreo processes varTypes exprType ->
      CChoreo processes varTypes exprType
    | CSelect :
      (chooser ∈ processes) ->
      (chooser : NProcessName) ->
      (offerer ∈ processes) ->
      (offerer : NProcessName) ->
      (selection : NChoiceLabel) ->
      CChoreo processes varTypes exprType ->
      CChoreo processes varTypes exprType
    | CProcedure : -- not finished
      (procedure : CProcedureName) ->
      (substitutes : Vector NProcessName procedure.argumentCount) ->
      (substitutes.toList ⊆ processes) ->
      CChoreo processes varTypes (procedure.type substitutes)
end

def cProcedures
  (procedure : CProcedureName) :
  (substitutes : Vector NProcessName procedure.argumentCount) ->
  (substitutes.toList ⊆ processes) -> -- also has to be distinct
  CChoreo processes varTypes (procedure.type substitutes) :=
    fun substitutes => match procedure with
      | .g => fun h =>
        let n := substitutes.head
        -- NProcess.NValueExpr (NValue.NRecv sorry sorry)
        -- NProcess.NValueExpr $ NValue.NFun (In:=NType.unit) (processes:=processes) (varTypes:=varTypes) (NProcess.NValueExpr (NValue.NConst ""))
        CChoreo.CValueExpr
          (CValue.CConst "Test" n (by
            have h' : n ∈ substitutes.toList := by simp; exact Vector.mem_of_getElem rfl
            have h'' := h h'
            exact h''))
 
mutual
  def cMentionedProcesses (choreo : CChoreo processes varTypes exprType) : List NProcessName :=
    match choreo with
      | CChoreo.CValueExpr value => cMentionedProcessesValues value
      | CChoreo.CApply func input =>
          List.append
            (cMentionedProcesses func)
            (cMentionedProcesses input)
      | CChoreo.CIf location_in_processes test then' else' =>
            (cMentionedProcesses test) ++
            (cMentionedProcesses then') ++
            (cMentionedProcesses else')
      | CChoreo.CSelect
          chooser_in_processes
          chooser
          offerer_in_processes
          offerer
          selection
          continuation =>
            chooser :: offerer :: (cMentionedProcesses continuation)
      | CChoreo.CProcedure procedure substitutes substitutes_in_processes =>
          -- Following line errors with "Can't show termination"
          -- cMentionedProcesses $ cProcedures procedure substitutes substitutes_in_processes
          substitutes.toList -- What if procedure doesn't use an argument?

  def cMentionedProcessesValues (value : CValue processes varTypes exprType) : List NProcessName :=
    match value with
      | CValue.CConst constValue location location_in_processes =>
          [location]
      | CValue.CVar index => cMentionedProcessesInTypes exprType
      | CValue.CFun (In:=In) body =>
          List.append
            (cMentionedProcessesInTypes In)
            (cMentionedProcesses body)
end










  -- abbrev NProcedureName.returnType : NProcedureName -> NType
  --   | f => NType.arbitrary String
  --   | g => NType.unit
  --   | h => NType.arbitrary Nat
  -- abbrev NProcedureName.argumentCount : NProcedureName -> Nat
  --   | f => 0
  --   | g => 1
  --   | h => 2



  -- abbrev NProcedureName.type : NProcedureName -> Type
  --   | f => (a : NProcessName) -> (b : NProcessName) -> NProcess processes varTypes exprType



-- def p : NProcess ["a"] [] (NType.func NType.unit (NType.arbitrary String)) :=
--   NProcedures NProcedureName.g (Vector.singleton "a")

-- #eval p











-- inductive NProcessName where
--   | mk : String -> NProcessName
-- deriving BEq, Hashable

-- inductive NChoiceLabel where
--   | mk : String -> NChoiceLabel
-- deriving BEq, Hashable

-- mutual
--   inductive NValue where
--     | NConst : α -> NValue
--     | NUnit
--     | NVar : String -> NValue
--     | NFun : String -> NProcess -> NValue
--     | NSend : (receiver : NProcessName) -> (payload : NValue) -> NValue
--     | NRecv : (sender : NProcessName) -> Unit -> NValue

--   inductive NProcess where
--     | NValueExpr : NValue -> NProcess
--     | NApply : NProcess -> NProcess -> NProcess
--     | NIf : NProcess -> NProcess -> NProcess -> NProcess
--     | NReceiveChoice : (NChoiceLabel -> NProcess) -> NProcess
--     | NSendChoice : (receiver : NProcessName) -> (choiceLabel : NChoiceLabel) -> (continuation : NProcess) -> NProcess
--     | NProcedure : ((parameter : List NProcessName) -> NProcess) -> NProcess
-- end

-- def NProcedureDefinitions : List ((List NProcessName) -> NProcess) := []
