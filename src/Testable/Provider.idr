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
  Config : (count : Nat) -> (verbose : Bool) -> TestConfig

defaultConfig : TestConfig
defaultConfig = Config 10 False

testP' : Nat -> Bool -> Prop [] -> { [RND, STDIO] } Eff (Provider Type)
testP' Z     v p = return (Provide (propAsType p))
testP' (S n) v p = case !(test p) of
                     MkResult ok args =>
                       case ok of
                         Nothing => do if v then putStrLn ("Skipping: " ++ show args) else return ()
                                       testP' n v p
                         Just False => return (Error $ "Counterexample: " ++ show args)
                         Just True => do if v then putStrLn ("Passed: " ++ show args) else return ()
                                         testP' n v p

testP : TestConfig -> Prop [] -> IO (Provider Type)
testP c p = do t <- System.time
               let go = it t
               run go
  where it : Int -> { [RND, STDIO] } Eff (Provider Type)
        it t = do srand (cast t)
                  testP' (count c) (verbose c) p


