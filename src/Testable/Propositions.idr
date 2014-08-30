module Testable.Propositions

%default total


||| The primitive types that we are reasoning about
data PrimT = CHAR | STRING | INT | BOOL

||| Primitive types are codes in a universe - here we get back the real types
interpPrim : PrimT -> Type
interpPrim CHAR   = Char
interpPrim STRING = String
interpPrim INT    = Int
interpPrim BOOL   = Bool

using (vars : Vect n PrimT)

  ||| Well-typed de Bruijn indices. These give an index into a typing context.
  data HasType : Vect n PrimT -> PrimT -> Type where
    Here : HasType (t::vars) t
    There : HasType vars t -> HasType (t'::vars) t

  ||| Expressions made up of primitives
  data PExpr : Vect n PrimT -> PrimT -> Type where
    ||| Variable references
    Var : HasType vars t -> PExpr vars t

    ||| Embedding of actual primitive values
    Lit : interpPrim t -> PExpr vars t

    ||| Constructing Bool from Int
    IntToBool : PExpr vars INT -> PExpr vars BOOL

    ||| Conditional
    boolElim : PExpr vars BOOL -> PExpr vars t -> PExpr vars t -> PExpr vars t

    Not : PExpr vars BOOL -> PExpr vars BOOL

    Prim__addInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__strHead  : PExpr vars STRING -> PExpr vars CHAR
    Prim__eqChar : PExpr vars CHAR -> PExpr vars CHAR -> PExpr vars INT
    Prim__eqInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__eqString : PExpr vars STRING -> PExpr vars STRING -> PExpr vars INT
    Prim__lenString : PExpr vars STRING -> PExpr vars INT
    Prim__mulInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__sdivInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__sgtInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__sltInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT
    Prim__subInt : PExpr vars INT -> PExpr vars INT -> PExpr vars INT

  ||| A runtime environment corresponding to a typing context.
  data Env : Vect n PrimT -> Type where
    Nil : Env []
    (::) : interpPrim t -> Env vars -> Env (t::vars)

  %name Env env

  ||| Get a variable from its runtime environment
  lookup : HasType vars t -> Env vars -> interpPrim t
  lookup Here (x :: env) = x
  lookup (There at) (_ :: env) = lookup at env


  ||| Preconditions for expressions.
  |||
  ||| `precond expr` is something that must evaluate to true for `expr` to
  ||| have a value.
  |||
  ||| Preconditions are carefully chosen to only employ total primitives, so
  ||| we don't need to check _their_ preconditions.
  |||
  ||| The preconditions are required in order to avoid totality problems.
  ||| Right now, it simply checks that we don't try to take the head of an
  ||| empty string. In the future, it will need to check for things like
  ||| division by zero
  precond : PExpr vars t -> List (PExpr vars BOOL)
  precond (Var x)              = []
  precond (IntToBool x)        = precond x
  precond (boolElim c t f)     = precond c ++ precond t ++ precond f
  precond (Not b)              = precond b
  precond (Prim__addInt x y)   = precond x ++ precond y
  precond (Prim__strHead x)    = IntToBool (Prim__sgtInt (Prim__lenString x) (Lit 0)) :: precond x
  precond (Prim__eqChar x y)   = precond x ++ precond y
  precond (Prim__eqString x y) = precond x ++ precond y
  precond (Prim__lenString x)  = precond x
  precond (Prim__mulInt x y)   = precond x ++ precond y
  precond (Prim__sdivInt x y)  = [Not (IntToBool (Prim__eqInt y (Lit 0)))] ++ precond x ++ precond y
  precond (Prim__sgtInt x y)   = precond x ++ precond y
  precond (Prim__sltInt x y)   = precond x ++ precond y
  precond (Prim__eqInt x y)    = precond x ++ precond y
  precond (Prim__subInt x y)   = precond x ++ precond y
  precond (Lit x)              = []

  ||| A property is either a universally quantification of another property or
  ||| an implication.
  data Prop : Vect n PrimT -> Type where
    ForAll : (t : PrimT) -> Prop (t::vars) -> Prop vars
    Given :  List (PExpr vars BOOL) -> PExpr vars BOOL -> Prop vars

  ||| Expressions are tested by mapping them to their underlying primitive.
  |||
  ||| We assert totality here to get it to reduce, but we will need to use it
  ||| in a position where it is guarded by a check of the preconditions.
  %assert_total
  testExpr' : (vars : Vect n PrimT) -> (env : Env vars) -> PExpr vars t -> interpPrim t
  testExpr' vars env (Var x) = lookup x env
  testExpr' vars env (Lit x) = x
  testExpr' vars env (IntToBool x) = intToBool $ testExpr' vars env x
  testExpr' vars env (boolElim c t f) = if testExpr' vars env c then testExpr' vars env t else testExpr' vars env f
  testExpr' vars env (Not b) = not (testExpr' vars env b)
  testExpr' vars env (Prim__addInt x y) = prim__addInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__strHead x) = prim__strHead $ testExpr' vars env x
  testExpr' vars env (Prim__eqChar x y) = prim__eqChar (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__eqInt x y) = prim__eqInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__eqString x y) = prim__eqString (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__lenString x) = prim_lenString (testExpr' vars env x)
  testExpr' vars env (Prim__mulInt x y) = prim__mulInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__sdivInt x y) = prim__sdivInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__sgtInt x y) = prim__sgtInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__sltInt x y) = prim__sltInt (testExpr' vars env x) (testExpr' vars env y)
  testExpr' vars env (Prim__subInt x y) = prim__subInt (testExpr' vars env x) (testExpr' vars env y)

  ||| Test an expression, converting the result to a Boolean in the same way as the stdlib.
  testExpr : (vars : Vect n PrimT) -> (env : Env vars) -> PExpr vars BOOL -> Bool
  testExpr vars env x = assert_total $ testExpr' vars env x


  hType : (vars : Vect n PrimT) -> (env : Env vars) -> List (PExpr vars BOOL) -> Type -> Type
  hType vars env []        body = body
  hType vars env (hy :: hs) body = so (testExpr vars env hy) -> hType vars env hs body


  testExprTot : (vars : Vect n PrimT) -> (env : Env vars) ->
                (requires : List (PExpr vars BOOL)) -> (x : PExpr vars BOOL) ->  hType vars env requires Bool
  testExprTot vars env [] x = assert_total $ testExpr vars env x
  testExprTot vars env (y :: xs) x = \pre => testExprTot vars env xs x


  -- Testing properties
  ||| Bind variables for a test
  partial
  testType : (vars : Vect n PrimT) -> (env : Env vars) -> Prop vars -> Type
  testType vars env (ForAll t x) = (y : interpPrim t) -> testType (t::vars) (y::env) x
  testType vars env (Given h x) = hType vars env (h ++ precond x) Bool

  partial
  testProp' : (vars : Vect n PrimT) -> (env : Env vars) -> (p : Prop vars) -> testType vars env p
  testProp' vars env (ForAll t body) = \x => testProp' (t::vars) (x::env) body
  testProp' vars env (Given hs x) with (hs)
    testProp' vars env (Given hs x) | []          = testExprTot vars env (precond x) x
    testProp' vars env (Given hs x) | (hy :: hys) = \prf => testProp' vars env (Given hys x)

  partial
  testProp : (p : Prop []) -> testType [] [] p
  testProp = testProp' [] []

  countForalls : Prop vars -> Nat
  countForalls (ForAll t x) = S $ countForalls x
  countForalls (Given xs x) = Z

  testInputs : (p : Prop vars) -> Vect (countForalls p) PrimT
  testInputs (ForAll t x) = t :: testInputs x
  testInputs (Given xs x) = []

  testExecT : (p : Prop vars) -> (envV : Env vars) -> (env : Env (testInputs p)) -> Type
  testExecT (ForAll t x) envV (y :: env) = testExecT x (y :: envV) env 
  testExecT (Given xs x) envV env = testType _ envV (Given xs x)

  partial
  instantiate' : (p : Prop vars) -> (e : Env vars) -> (input : Env (testInputs p)) -> testExecT p e input
  instantiate' (ForAll t x) e (v::input) = instantiate' x (v::e) input
  instantiate' (Given xs x) e []         = testProp' _ e (Given xs x)


  ||| Nothing means that the input didn't satisfy the precondition
  partial
  instantiate : (p : Prop []) -> (input : Env (testInputs p)) -> testExecT p [] input
  instantiate p input = instantiate' p [] input



  -- Properties as postulates

  partial
  propAsType' : Prop vars -> Env vars -> Type
  propAsType' (ForAll t body) env = (x : interpPrim t) -> propAsType' body (x::env)
  propAsType' (Given hs body) env = hType _ env (hs ++ precond body) $ so (testExpr _ env body)
   
  partial
  propAsType : Prop [] -> Type
  propAsType p = propAsType' p []

Property : Type
Property = Prop []
