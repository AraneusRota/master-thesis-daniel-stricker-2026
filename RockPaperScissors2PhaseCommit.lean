-- import Mathlib.Tactic.DeriveFintype
-- import Lean
-- import Lean.Data.Json.Basic
-- import Lean.Data.Json.Parser
-- import Lean.Data.Json.Printer

-- import Chorlean.utils
import Chorlean.Choreo

-- import Mathlib.Tactic.DeriveFintype

import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer



open Lean Json ToJson FromJson



-- inductive Actor where
-- | Player1 | Player2
-- deriving DecidableEq, ToJson, FromJson, Repr, Inhabited
-- open Actor
abbrev Actor := String


-- instance : FinEnum Actor :=
  -- FinEnum.ofEquiv _ (proxy_equiv% Actor).symm

-- instance: ToString Actor where
--   toString
--   | Player1 => "P1"
--   | Player2 => "P2"

inductive Hand where
  | Rock
  | Paper
  | Scissors
deriving ToJson, FromJson, Repr, Inhabited
open Hand

instance: ToString Hand where
  toString
  | Rock => "Rock"
  | Paper => "Paper"
  | Scissors => "Scissors"

class OfString (α:Type) where
  ofString: String -> Option α

instance: OfString Hand where
  ofString
  | "Rock" => Rock
  | "Paper" => Paper
  | "Scissors" => Scissors
  | _ => none

inductive RPSException where
  | P1WrongInput
  | P2WrongInput
open RPSException

def outcome (hand1 : String) (hand2 : String): Except RPSException (Option Actor) :=
  let maybeHand1 : Option Hand := OfString.ofString hand1
  let maybeHand2 : Option Hand := OfString.ofString hand2

  do
    match maybeHand1 with
      | none => Except.error P1WrongInput
      | some hand1 =>
          match maybeHand2 with
            | none => Except.error P2WrongInput
            | some hand2 =>
                match hand1 with
                  | Rock =>
                      match hand2 with
                        | Rock => pure none
                        | Paper => pure "Player2"
                        | Scissors => pure "Player1"
                  | Paper =>
                      match hand2 with
                        | Rock => pure "Player1"
                        | Paper => pure none
                        | Scissors => pure "Player2"
                  | Scissors =>
                      match hand2 with
                        | Rock => pure "Player2"
                        | Paper => pure "Player1"
                        | Scissors => pure none


def play: Choreo ["Player1", "Player2"] target incensus (Option $ Option Actor) :=
  do
    -- Not possible:
    -- let promptHand := fun (actor : Actor) =>
      -- let p :=
        -- do
          -- Print.info shoot
          -- Input.readString
      -- locally actor p

    let promptHand : IO String :=
      do
        let shoot := "Rock 👊, Paper ✋, Scissors ✌️, shoot:"
        IO.println shoot
        IO.getLine

    let handPlayer1 <- (
      locally "Player1" promptHand
    )
    let handPlayer2 <- (
      locally "Player2" promptHand
    )
    let handPlayer2Shared <- com "Player1" handPlayer2 (Choreo.Return "PlaceholderString")

    let gameResultLocated <- locally "Player1" (
      do
        let un1 := handPlayer1.un
        match outcome un1 handPlayer2Shared.un with
          | Except.ok result => pure $ some result
          | Except.error exception => do
              -- 'Except' has no trivial Serialize instance so we have to handle it here
              match exception with
                | P1WrongInput => IO.println "Wrong input of Player 1"
                | P2WrongInput => IO.println "Wrong input of Player 2"
              pure none
    ) >>= fun msg => com "Player2" msg (Choreo.Return "PlaceholderActor")
    let gameResult := gameResultLocated.un

    let printResultMessageFor := fun (player : Actor) =>
      do
        let winMessage := "You win :>"
        let looseMessage := "You lose :`("
        let tieMessage := "Tie :o"
        let message :=
          match gameResult with
            | some result =>
                match result with
                  | some winner =>
                    if player == winner then
                      winMessage
                    else
                      looseMessage
                  | none => tieMessage
            | none => "Someone entered an invalid input."
        do
          IO.println message

    let _ <- locally "Player1" $ printResultMessageFor "Player1"
    let _ <- locally "Player2" $ printResultMessageFor "Player2"

    pure gameResult

def addresses: Actor -> Actor -> Address
| "Player1", "Player1" => .v4 (.mk 127 0 0 1) 70001
| "Player1", "Player2" => .v4 (.mk 127 0 0 1) 70002
| "Player2", "Player1" => .v4 (.mk 127 0 0 1) 70004
| "Player2", "Player2" => .v4 (.mk 127 0 0 1) 70005
| "Coordinator", "Coordinator" => .v4 (.mk 127 0 0 1) 70006
| "Coordinator", "Player2" => .v4 (.mk 127 0 0 1) 70007
| "Player2", "Coordinator" => .v4 (.mk 127 0 0 1) 70008
| "Coordinator", "Player1" => .v4 (.mk 127 0 0 1) 70009
| "Player1", "Coordinator" => .v4 (.mk 127 0 0 1) 70010
| _, _ => .v4 (.mk 127 0 0 1) 70000

def main := CHORLEAN_MAIN addresses "Coordinator" (λ _args => do
  -- let rec inputHandRec :=
  --   do
  --     let maybeWinner <- inputHand
  --     pure $
  --       match maybeWinner with
  --         | some winner => some winner
  --         | none => none

  let rec playRec (tries : Nat) :=
    if tries = 0 then
      do
        let message := "Too many failed attempts"
        let _ <- locally "Player1" $ IO.println message
        let _ <- locally "Player2" $ IO.println message
        pure none
    else
      do
        let maybeWinner <- play
        match maybeWinner with
          | some noExceptionWinner =>
              match noExceptionWinner with
                | some winner => Choreo.Return maybeWinner
                | none => playRec (tries - 1)
          | none => playRec (tries - 1)


  let gameResult <- playRec 3
  return (fun _ _ => 0))
