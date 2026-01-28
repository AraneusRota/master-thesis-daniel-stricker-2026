module Playground where

import CLI (CLI, getInput, putOutput, getstr, putstr)
import Choreography
import Data (TestArgs(reference))
import EasyMain (easyMain)
import Test.QuickCheck
  ( Arbitrary,
    arbitrary,
  )

data Winner = Alpha | Beta | Draw | Fail deriving (Eq, Show, Read)

choreography :: Choreo '["alpha", "beta"] (CLI m) ()
choreography = do
  let alpha :: Member "alpha" '["alpha", "beta"] = listedFirst
      beta  :: Member "beta"  '["alpha", "beta"] = listedSecond
  a <- locally alpha \_ -> getInput @String "Enter hand:"
  _ <- locally beta \_ -> getstr "Press enter for Beta to continute. (Without this you can get problems starting the parties in the wrong order)"
  a' <- (alpha, (singleton @"alpha", a)) ~> beta @@ nobody
  b <- locally beta \_ -> getInput @String "Enter hand:"
  b' <- (beta, (singleton @"beta", b)) ~> alpha @@ nobody

  winner <- locally alpha \un ->
    pure
      if (un singleton a) == (un singleton b') then "Draw"
      else if (un singleton a) == "rock" && (un singleton b') == "paper" then "Beta"
      else if (un singleton a) == "rock" && (un singleton b') == "scissors" then "Alpha"
      else if (un singleton a) == "paper" && (un singleton b') == "rock" then "Alpha"
      else if (un singleton a) == "paper" && (un singleton b') == "scissors" then "Beta"
      else if (un singleton a) == "scissors" && (un singleton b') == "rock" then "Beta"
      else if (un singleton a) == "scissors" && (un singleton b') == "paper" then "Alpha"
      else "Fail"

  
  -- winnerShared <- (alpha, (singleton @"alpha", winner)) ~> beta @@ nobody

  locally_ alpha \un -> putOutput "Winner:" $
    if (un singleton a) == (un singleton b') then "Draw"
    else if (un singleton a) == "rock" && (un singleton b') == "paper" then "Beta"
    else if (un singleton a) == "rock" && (un singleton b') == "scissors" then "Alpha"
    else if (un singleton a) == "paper" && (un singleton b') == "rock" then "Alpha"
    else if (un singleton a) == "paper" && (un singleton b') == "scissors" then "Beta"
    else if (un singleton a) == "scissors" && (un singleton b') == "rock" then "Beta"
    else if (un singleton a) == "scissors" && (un singleton b') == "paper" then "Alpha"
    else "Fail"
  locally_ beta \un -> putOutput "Winner:" $
    if (un singleton a') == (un singleton b) then "Draw"
    else if (un singleton a') == "rock" && (un singleton b) == "paper" then "Beta"
    else if (un singleton a') == "rock" && (un singleton b) == "scissors" then "Alpha"
    else if (un singleton a') == "paper" && (un singleton b) == "rock" then "Alpha"
    else if (un singleton a') == "paper" && (un singleton b) == "scissors" then "Beta"
    else if (un singleton a') == "scissors" && (un singleton b) == "rock" then "Beta"
    else if (un singleton a') == "scissors" && (un singleton b) == "paper" then "Alpha"
    else "Fail"


main :: IO ()
main = easyMain choreography



data Args = Args
  { foo :: String,
    bar :: String
  }
  deriving (Eq, Show, Read)

instance TestArgs Args (String, String) where
  reference Args{foo, bar} = (bar, foo)

instance Arbitrary Args where
  arbitrary = Args <$> arbitrary <*> arbitrary
