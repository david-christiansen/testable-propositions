module Testable.Examples

import Testable.Propositions
import Testable.Syntax

import Testable.Provider

%language TypeProviders

----------------------------------------------------------
-- Examples
----------------------------------------------------------


||| String equality is reflexive
propEqRefl : Property
propEqRefl = prop ((x : STRING) -> x == x)


||| The heads of equal strings are equal
propStrHeadEq : Property
propStrHeadEq = prop ((str1, str2 : STRING) ->
                      Given [str1 == str2]
                            (Prim__strHead str1 == Prim__strHead str2))

||| Dividing makes an Int smaller
propDivSmaller : Property
propDivSmaller = prop ((x,y: INT) -> Given [x > y] ((x `div` y) < x))

||| Every int is less than 1 greater than itself - fails for 9223372036854775807
propIntIncGt : Property
propIntIncGt = prop ((x : INT) ->  x < x + 1)



%provide postulate strEqRefl with testP (record {verbose = True} defaultConfig) $ propEqRefl

%provide postulate strHeadEq with testP (record {verbose = True, count=5} defaultConfig) $ propStrHeadEq

%provide postulate divSmaller with testP (record {verbose = True} defaultConfig) $ propDivSmaller

%provide postulate intIncGt with  testP (record {verbose = True} defaultConfig) $ propIntIncGt

