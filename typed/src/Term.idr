
module Term

-- Simply-typed lambda calculus with 
--   (1) natural numbers as the only base type, and
--   (2) general recursion.
-- This calculus is also referred to as PCF.
--
-- Note that variables in the lambda calculus are not
-- named but identified by their de Bruijn index.


import Data.Fin
import public Data.Vect


%default total
%access public export


---------------------------------------------------
-- Begin: TYPES IN THE SIMPLY-TYPED LAMBDA CALCULUS

-- Data type 'Ty' represents the types in the
-- simply-typed lambda calculus:
--   (1) Base type 'TyNat' of natural numbers.
--   (2) Type constructor 'TyFun' for forming
--       function types.
data Ty = TyNat | TyFun Ty Ty


-- Simplified syntax for function types:
infixr 10 :->:
(:->:) : Ty -> Ty -> Ty
(:->:) t1 t2 = TyFun t1 t2

-- End: TYPES IN THE SIMPLY-TYPED LAMBDA CALCULUS
-------------------------------------------------



---------------------------------------------------------
-- Begin: CONTEXT FOR TYPING TERMS IN THE LAMBDA CALCULUS

Context : Nat -> Type
Context n = Vect n Ty

-- End: CONTEXT FOR TYPING TERMS IN THE LAMBDA CALCULUS
-------------------------------------------------------



-------------------------------------------------
-- Begin: WELL-TYPED TERMS OF THE LAMBDA CALCULUS

-- Data type of well-typed terms in the 
-- simply-typed lambda calculus:
data Term : Context n -> Ty -> Type where
  -- Variable:
  -- The data constructor for variables ('Var') takes
  -- as arguments a de Bruijn index ('i') and a proof
  -- ('prf') that the variable at index 'i' in the 
  -- context 'ctx' has type 't'.
  TVar  : (i : Fin n) -> {auto prf : index i ctx = t} -> 
          Term ctx t
  -- Abstraction:
  -- The data constructor for abstractions ('Abs')
  -- takes as its first (implicit) argument the
  -- type of the variable that is bound by this
  -- abstraction.
  TAbs  : {s : Ty} -> Term (s::ctx) t ->
          Term ctx (s :->: t)
  -- Application:
  TApp  : Term ctx (s :->: t) -> Term ctx s -> 
          Term ctx t    
  -- Fix-point operator:
  TFix  : Term ctx (t :->: t) -> 
          Term ctx t
  -- Constant 'Zero' (natural number):
  TZero : Term ctx TyNat
  -- Successor:
  TSucc : Term ctx TyNat ->
          Term ctx TyNat
  -- Predecessor:
  TPred : Term ctx TyNat ->
          Term ctx TyNat
  -- Test for equality with 'Zero' 
  -- (with terms for the "then" and
  -- "else" branches):
  TIfz  : Term ctx TyNat -> Term ctx t -> Term ctx t ->
          Term ctx t

-- End: WELL-TYPED TERMS OF THE LAMBDA CALCULUS
-----------------------------------------------



---------------------------------------
-- Begin: VALUES IN THE LAMBDA CALCULUS 

-- The following lambda calculus terms
-- are values (i.e. normal forms for 
-- reduction under the "Step" relation):
--   (1) lambda abstractions (that are
--       not applied),
--   (2) the constant 'Zero',
--   (3) the natural number constants
--       (formed by applying 'Succ' to
--       another value). 
data Value : Term [] t -> Type where
  VZero : Value TZero
  VSucc : Value e -> Value (TSucc e)
  VAbs  : Value (TAbs e)


valueTerm : {e : Term [] t} -> Value e -> Term [] t
valueTerm {e = e} _ = e

-- End: VALUES IN THE LAMBDA CALCULUS 
-------------------------------------
