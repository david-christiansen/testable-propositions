module Testable.Provider

import System
import Providers

import Effects
import Effect.Random
import Effect.StdIO

import Testable.Propositions
import Testable.Syntax
import Testable.Testing

testP' : Nat -> Prop [] -> { [RND, STDIO] } Eff (Provider Type)
testP' Z     p = return (Provide (propAsType p))
testP' (S n) p = case !(test p) of
                   MkResult ok args =>
                     case ok of
                       Nothing => do putStrLn ("Skipping " ++ show args) ; testP' n p
                       Just False => return (Error $ "Counterexample: " ++ show args)
                       Just True => testP' n p

testP : Nat -> Prop [] -> IO (Provider Type)
testP n p = do t <- System.time
               let go = it t
               run go
  where it : Int -> { [RND, STDIO] } Eff (Provider Type)
        it t = do srand (cast t)
                  testP' n p

%language TypeProviders

%provide postulate foo with testP 10 $ prop ((x : STRING) -> x == x)

%provide postulate crap with testP 10 $ prop ((x, y : STRING) -> x == y)
