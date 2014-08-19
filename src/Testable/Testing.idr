module Testable.Testing

import Debug.Trace

import System.Random.TF.Gen

import Testable.Propositions
import Testable.Syntax


%default total

||| Generator (ported from first QuickCheck paper). Here, we parameterize the type by the random generator `r`.
data Gen r a = MkGen (Int -> r -> a)

instance Show (Gen r a) where
  show _ = "<gen>"

instance RandomGen r => Functor (Gen r) where
  map f (MkGen g) = MkGen $ \i, r => f (g i (snd (next r)))

instance RandomGen r => Applicative (Gen r) where
  pure x = MkGen (\i, r => x)
  (MkGen f) <$> (MkGen x) =
    MkGen $ \i, r =>
            let (r1, r2) = split r in
            f i (snd (next r1)) (x i (snd (next r2)))


instance RandomGen r => Monad (Gen r) where
  (MkGen m1) >>= k =
    MkGen $ \i, r => let (r1, r2) = split r
                         (MkGen m2) = k (m1 i (snd (next r1)))
                     in m2 i (snd (next r2))

||| Generate a random state
rand : (RandomGen r) => Gen r r
rand = MkGen (\n, r => r)


choose : (RandomGen r, Random a) => (a, a) -> Gen r a
choose bounds = map (fst . randomR bounds) rand


generate : RandomGen r => Int -> r -> Gen r a -> a
generate n rnd (MkGen m) = let (size, rnd') = randomR (0, n) rnd in
                           m size rnd'

sized : RandomGen r => (Int -> Gen r a) -> Gen r a
sized fgen = MkGen (\n, r => let MkGen m = fgen n in m n r)

elements : RandomGen r => Vect (S n) a -> Gen r a
elements xs = pure $ elements' !(choose (the Int 0, (cast $ length xs) - 1)) xs
  where elements' : Int -> Vect (S n) a -> a
        elements' i [x] = x
        elements' i (x::y::xs) = if i <= 0 then x else elements' (i-1) (y::xs)

||| Here we take advantage of the fact that we have a closed universe of
||| types, so `arbitrary` is not a type class method
arbitrary : RandomGen r => (t : PrimT) -> Gen r (interpPrim t)
arbitrary INT    = sized $ \n => choose (-n, n)
arbitrary BOOL   = elements [True, False]
arbitrary STRING = sized $ \n => map pack . sequence $
                                   repeatN !(choose (0, n))
                                           (arbitrary (assert_smaller STRING CHAR))
  where repeatN : Int -> a -> List a
        repeatN i x = if i <= 0 then [] else x :: repeatN (assert_smaller i (i-1)) x
arbitrary CHAR   = map (fst . randomR (chr 0, chr 255)) rand -- for now, just ASCII


||| Construct an arbitrary environment for a particular test
arbitraryEnv : RandomGen r => (vars : Vect n PrimT) -> Gen r (Env vars)
arbitraryEnv []      = pure []
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

partial
test : RandomGen r => (p : Prop []) -> Gen r (Result (testInputs p))
test p = do inputs <- arbitraryEnv (testInputs p)
            let res = runTest $ instantiate p inputs
            return $ MkResult res inputs

partial
ntests : (RandomGen r, Show r) => (seed : r) -> (p : Prop []) -> (n : Nat) -> Vect n (Result (testInputs p))
ntests seed p Z     = []
ntests seed p (S n) = let (seed', seed'') = split seed in
                      let head = generate 50 seed' (test p) in
                      let rest = ntests seed'' p n in
                      let _ = trace ("seed at " ++ show (S n) ++ ": " ++ show seed) () in
                      head :: rest

withSeed : RandomGen r => (seed : IO r) -> (r -> a) -> IO a
withSeed seed fn = map fn seed

withIndex : Nat -> Vect n a -> Vect n (Nat, a)
withIndex n [] = []
withIndex n (x::xs) = (n, x) :: withIndex (S n) xs

namespace Main
  partial
  main : IO ()
  main = do res <- withSeed (map seedTFGen mkSeed) $
                     \r => ntests r (prop ((x, y, z : INT) -> x == y+z)) 20
            putStrLn (show (withIndex 1 res))
