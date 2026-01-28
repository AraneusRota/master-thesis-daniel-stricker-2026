-- import Chorlean.Choreo
-- import Chorlean.scattergather
-- import Chorlean.Effects
-- import Mathlib.Tactic.DeriveFintype
-- import Lean
-- import Lean.Data.Json.Basic
-- import Lean.Data.Json.Parser
-- import Lean.Data.Json.Printer

import Chorlean.utils
import Chorlean.Choreo

import Mathlib.Tactic.DeriveFintype

import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer



open Lean Json ToJson FromJson


variable {Role: Type} [DecidableEq Role] [ToString Role]

-- inductive Actor where
-- | Player1 | Player2
-- deriving DecidableEq, ToJson, FromJson, Repr, Inhabited
-- open Actor
abbrev Actor := String
abbrev Player1 := "Player1"
abbrev Player2 := "Player2"


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
                        | Paper => pure Player2
                        | Scissors => pure Player1
                  | Paper =>
                      match hand2 with
                        | Rock => pure Player1
                        | Paper => pure none
                        | Scissors => pure Player2
                  | Scissors =>
                      match hand2 with
                        | Rock => pure Player2
                        | Paper => pure Player1
                        | Scissors => pure none


def play: Choreo [Player1, Player2] target incensus (Option $ Option Actor) :=
  do
    -- Not possible:
    -- let promptHand := fun (actor : Actor) =>
      -- let p :=
        -- do
          -- Print.info shoot
          -- Input.readString
      -- locally actor p

    let promptHand :=
      do
        let shoot := "Rock 👊, Paper ✋, Scissors ✌️, shoot:"
        Print.info shoot
        Input.readString

    let handPlayer1 <- (
      locally Player1 (fun {_} => promptHand)
    )
    let handPlayer2 <- (
      locally Player2 (fun {_} => promptHand)
    )
    let handPlayer2Shared <- com Player1 handPlayer2

    let gameResultLocated <- locally Player1 (
      do
        match outcome handPlayer1.un handPlayer2Shared.un with
          | Except.ok result => pure $ some result
          | Except.error exception => do
              -- 'Except' has no trivial Serialize instance so we have to handle it here
              match exception with
                | P1WrongInput => Print.info "Wrong input of Player 1"
                | P2WrongInput => Print.info "Wrong input of Player 2"
              pure none
    ) >>= com Player2
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
          Print.info message

    let _ <- locally Player1 $ printResultMessageFor Player1
    let _ <- locally Player2 $ printResultMessageFor Player2

    pure gameResult

def addresses: Actor -> Actor -> Address
| "Player1", "Player1" => .v4 (.mk 127 0 0 1) 70001
| "Player1", "Player2" => .v4 (.mk 127 0 0 1) 70002
| "Player2", "Player1" => .v4 (.mk 127 0 0 1) 70004
| "Player2", "Player2" => .v4 (.mk 127 0 0 1) 70005
| _, _ => sorry

def main := CHORLEAN_MAIN addresses (census:=[Player1, Player2]) (λ _args => do
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
        let _ <- locally Player1 $ Print.info message
        let _ <- locally Player2 $ Print.info message
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
