module Testable.Testing

import Debug.Trace

import Testable.Propositions
import Testable.Syntax

import Effects
import Effect.Random
import Effect.StdIO

%default partial

rndChar : { [RND] } Eff Char
rndChar = do i <- rndInt 0 255
             return $ cast (fromInteger {a=Int} i)



arbitrary : (t : PrimT) -> { [RND] } Eff (interpPrim t)
arbitrary INT = do i <- rndInt (-9223372036854775808) 9223372036854775807
                   return (fromInteger i)
arbitrary BOOL = rndSelect' [True, False]
arbitrary STRING = do len <- rndInt 0 20
                      return $ pack !(getChars len)
  where getChars : Integer -> { [RND] } Eff (List Char)
        getChars n = if n <= 0
                       then return []
                       else [| rndChar :: getChars (assert_smaller n (n-1)) |]
arbitrary CHAR = rndChar

||| Construct an arbitrary environment for a particular test
arbitraryEnv : (vars : Vect n PrimT) -> { [RND] } Eff (Env vars)
arbitraryEnv [] = pure []
arbitraryEnv (t::ts) = [| arbitrary t :: arbitraryEnv ts |]




||| The output of instiatiate is difficult to run without a bit of typecasing. `Testable` takes care of that.
class Testable a where
  partial
  runTest : a -> Maybe Bool

instance Testable Bool where
  runTest b = Just b

instance Testable b => Testable (so x -> b) where
  runTest {x} f with (choose x)
    runTest f | (Left ok) = runTest (f ok)
    runTest f | (Right fail) = Nothing

instance Testable (hType vars env hs Bool) where
  runTest {hs=[]} x = runTest x
  runTest {hs=(h::hs)} x = runTest x

instance Testable (testExecT p env inputs) where
  runTest {p=ForAll t p} {env} {inputs=i::inputs} x = runTest {a=testExecT p (i::env) inputs} x
  runTest {p=Given hs p} {inputs} x = runTest x



using (vars : Vect n PrimT)
  record Result : Vect n PrimT -> Type where
    MkResult : (ok : Maybe Bool) ->
               (args : Env vars) ->
               Result vars

  instance Show (interpPrim t) where
    show {t=BOOL}   x = show x
    show {t=INT}    x = show x
    show {t=CHAR}   x = show x
    show {t=STRING} x = show x

  instance Show (Env vars) where
    show [] = "[]"
    show (x::xs) = "[" ++ showCommas (x :: xs) ++ "]"
      where showCommas : Env vars -> String
            showCommas [] = ""
            showCommas [x] = show x
            showCommas (x::y::xs) = show x ++ ", " ++ showCommas (y::xs)

  instance Show (Result vars) where
    show (MkResult ok args) = showRes ok ++ " " ++ show args
      where showRes : Maybe Bool -> String
            showRes (Just True) = "Passed"
            showRes (Just False) = "Failed"
            showRes Nothing = "Skipped"

test : (p : Prop []) -> { [RND] } Eff (Result (testInputs p))
test p = do inputs <- arbitraryEnv (testInputs p)
            let res = runTest $ instantiate p inputs
            return $ MkResult res inputs

partial
ntests : (p : Prop []) -> (n : Nat) -> { [RND] } Eff (Vect n (Result (testInputs p)))
ntests p Z     = pure []
ntests p (S n) = [| test p :: ntests p n |]

myTest : { [RND, STDIO] } Eff ()
myTest = do res <- ntests (prop ((x : INT) -> x == x)) 20
            putStrLn (show res)


namespace Main
  partial
  main : IO ()
  main = run myTest


-- -}
-- -}
-- -}
