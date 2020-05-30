
module Term

-- Simply-typed lambda calculus with 
--   (1) natural numbers as the only base type, and
--   (2) primitive recursion.
--
-- Terms in the lambda calculus are initially untyped.
-- The usual typing judgement is defined as a separate
-- data type in a separate module.
-- Note that meta-theory developed in yet other modules
-- will rely on the typing judgement.
--
-- Note that variables in the lambda calculus are not
-- named but identified by their de Bruijn index.
-- Since terms in our lambda calculus are initially
-- untyped, they may therefore also be ill-scoped.
-- Hence, de Bruijn indices are represented simply
-- by natural numbers (since they will only be
-- required to be valid in a context that is chosen
-- later, during typing of a term).


%default total
%access public export



------------------------------------------------
-- Begin: (UNTYPED) TERMS OF THE LAMBDA CALCULUS

data Term : Type where
  TVar  : (i : Nat) -> Term
  TAbs  : Term -> Term
  TApp  : Term -> Term -> Term
  TRec  : Term -> Term -> Term ->
          Term
  TZero : Term
  TSucc : Term -> Term
  TPred : Term -> Term
  TIfz  : Term -> Term -> Term ->
          Term



-- Construction of terms is a congruence for equality.
-- The following straightforward lemmas are often useful
-- for writing shorter proofs.

congVar : i = j -> TVar i = TVar j
congVar Refl = Refl


congAbs : e = e' -> TAbs e = TAbs e'
congAbs Refl = Refl


congApp : e1 = e1' -> e2 = e2' -> TApp e1 e2 = TApp e1' e2'
congApp Refl Refl = Refl


congRec : e1 = e1' -> e2 = e2' -> e3 = e3' ->
          TRec e1 e2 e3 = TRec e1' e2' e3'
congRec Refl Refl Refl = Refl


congZero : TZero = TZero
congZero = Refl


congSucc : e = e' -> TSucc e = TSucc e'
congSucc Refl = Refl


congPred : e = e' -> TPred e = TPred e'
congPred Refl = Refl


congIfz : e1 = e1' -> e2 = e2' -> e3 = e3' ->
          TIfz e1 e2 e3 = TIfz e1' e2' e3'
congIfz Refl Refl Refl = Refl

-- End: (UNTYPED) TERMS OF THE LAMBDA CALCULUS
----------------------------------------------




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
data Value : Term -> Type where
  VZero : Value TZero
  VSucc : Value e -> Value (TSucc e)
  VAbs  : Value (TAbs e)

-- End: VALUES IN THE LAMBDA CALCULUS 
-------------------------------------
