module Testable.Provider

import System
import Providers

import Effects
import Effect.Random
import Effect.StdIO

import Testable.Propositions
import Testable.Syntax
import Testable.Testing

record TestConfig : Type where
  Config : (attempt, required : Nat) -> (verbose : Bool) -> TestConfig

defaultConfig : TestConfig
defaultConfig = Config 5 10 False

testP' : Nat -> Nat -> Bool -> Prop [] -> { [RND, STDIO] } Eff (Provider Type)
testP' _     Z     v p = return (Provide (propAsType p))
testP' Z     (S n) v p = return (Error $ "Could not generate enough cases. " ++ show (S n) ++ " tests remaining.")
testP' (S m) (S n) v p =
  case !(test p) of
    MkResult ok args =>
      case ok of
        Nothing => do if v then putStrLn ("Skipping: " ++ show args) else return ()
                      testP' m (S n) v p
        Just False => return (Error $ "Counterexample: " ++ show args)
        Just True => do if v then putStrLn ("Passed: " ++ show args) else return ()
                        testP' (S m) n v p

testP : TestConfig -> Prop [] -> IO (Provider Type)
testP c p = do t <- System.time
               let go = it t
               run go
  where it : Int -> { [RND, STDIO] } Eff (Provider Type)
        it t = do srand (cast t)
                  testP' (attempt c) (required c) (verbose c) p


