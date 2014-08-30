module Testable.Syntax

import Testable.Propositions

dsl prop
  pi          = ForAll
  variable    = Var
  index_first = Here
  index_next  = There

using (vars : Vect n PrimT)


  implicit itHolds : PExpr vars BOOL -> Prop vars
  itHolds expr = Given [] expr

  boolOp : (PExpr vars a -> PExpr vars a -> PExpr vars INT) -> PExpr vars a -> PExpr vars a -> PExpr vars BOOL
  boolOp op x y = IntToBool (op x y)

  (<) : PExpr vars INT -> PExpr vars INT -> PExpr vars BOOL
  (<) = boolOp Prim__sltInt

  (>) : PExpr vars INT -> PExpr vars INT -> PExpr vars BOOL
  (>) = boolOp Prim__sgtInt
  
  div : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
  div = Prim__sdivInt

  namespace String
    (==) : PExpr vars STRING -> PExpr vars STRING -> PExpr vars BOOL
    (==) = boolOp Prim__eqString

  namespace Char
    (==) : PExpr vars CHAR -> PExpr vars CHAR -> PExpr vars BOOL
    (==) = boolOp Prim__eqChar

  namespace Int
    (==) : PExpr vars INT -> PExpr vars INT -> PExpr vars BOOL
    (==) = boolOp Prim__eqInt

  instance Num (PExpr vars INT) where
    (+) = Prim__addInt
    (-) = Prim__subInt
    (*) = Prim__mulInt
    abs x = boolElim (x < 0) (-x) x
    fromInteger = Lit . fromInteger

