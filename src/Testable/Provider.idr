module Testable.Provider

import Providers

import Testable.Propositions
import Testable.Syntax

test : Prop [] -> IO (Provider Type)
test p = if True -- TODO: Actually test!
           then return (Provide (propAsType p))
           else return (Error "Failed to validate - TODO insert counterexample!")
