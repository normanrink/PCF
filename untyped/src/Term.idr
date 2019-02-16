
module Term

-- Untyped lambda calculus with built-in natural numbers. 
--
-- Note that variables in the lambda calculus are not
-- named but identified by their de Bruijn index.


import Data.Fin
import public Data.Vect


%default total
%access public export


--------------------------------------
-- Begin: TERMS OF THE LAMBDA CALCULUS

-- Data type of well-scoped terms
-- in the lambda calculus:
data Term : Nat -> Type where
  -- Variable:
  -- The data constructor for variables ('Var') takes
  -- as arguments a de Bruijn index ('i').
  TVar  : (i : Fin n) -> Term n
  -- Abstraction:
  TAbs  : Term (S n) -> Term n
  -- Application:
  TApp  : Term n -> Term n -> Term n
  -- Constant 'Zero' (natural number):
  TZero : Term n
  -- Successor:
  TSucc : Term n -> Term n
  -- Predecessor:
  TPred : Term n -> Term n
  -- Test for equality with 'Zero' 
  -- (with terms for the "then" and
  -- "else" branches):
  TIfz  : Term n -> Term n -> Term n ->
          Term n

-- End: TERMS OF THE LAMBDA CALCULUS
------------------------------------



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
data Value : Term 0 -> Type where
  VZero : Value TZero
  VSucc : Value e -> Value (TSucc e)
  VAbs  : Value (TAbs e)


valueTerm : {e : Term 0} -> Value e -> Term 0
valueTerm {e = e} _ = e

-- End: VALUES IN THE LAMBDA CALCULUS 
-------------------------------------
