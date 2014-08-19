module Testable.URandom


import System.Random.TF.Random


-- A random generator built on unsafePerformIO and /dev/urandom

data URandomGen = MkURandomGen Bits32

instance Show URandomGen where { show = const "{gen}" }

stringNum : String -> Bits32 -> Bits32
stringNum s acc with (strM s)
  stringNum ""             acc | StrNil = acc
  stringNum (strCons x xs) acc | (StrCons x xs) =
    stringNum xs (prim__addB32 (prim__shlB32 acc 8) (prim__zextInt_B32 (prim__charToInt x)))

getRandom : IO Bits32
getRandom = do urandom <- openFile "/dev/urandom" Read
               stuff <- fread urandom
               closeFile urandom
               urandom <- openFile "/dev/urandom" Read
               stuff' <- fread urandom
               closeFile urandom
               return $ stringNum (stuff ++ stuff') 0

nextUR : URandomGen -> (Bits32, URandomGen)
nextUR _ = let x = unsafePerformIO getRandom in
           (x, MkURandomGen x)

splitUR : URandomGen -> (URandomGen, URandomGen)
splitUR x = (snd (nextUR x), snd (nextUR x))

instance RandomGen URandomGen where
  next = assert_total nextUR
  split = assert_total splitUR
