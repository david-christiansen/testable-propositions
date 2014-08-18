module Testable.Examples

import Testable.Propositions
import Testable.Syntax

----------------------------------------------------------
-- Examples
----------------------------------------------------------


||| String equality is reflexive
propEqReflP : Prop []
propEqReflP = prop ((x : STRING) -> x == x)


||| The heads of equal strings are equal
propStrHeadEq : Prop []
propStrHeadEq = prop ((str1, str2 : STRING) ->
                      Given [str1 == str2]
                            (Prim__strHead str1 == Prim__strHead str2))


||| Every int is less than 1 greater than itself - fails for 9223372036854775807
propIntIncGt : Prop []
propIntIncGt = prop ((x : INT) ->  x < x + 1)
