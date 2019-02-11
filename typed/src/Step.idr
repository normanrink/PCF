
module Step

-- Relation 'Step' for reducing terms
-- in the simply-typed lambda calculus.
 

import Term
import Subst


%default total
%access public export


-------------------------------------------------------------------------
-- Begin: SMALL-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS

-- The relation 'Step' defines evaluation of terms in the lambda
-- calculus following small-step semantics. 'Step' relates two 
-- terms 'x' and 'y' precisely when 'x' can be rewritten into 'y'
-- in a single step of evaluation.
--
-- (Note that the arguments 'x' and 'y' to the type constructor 'Step'
-- are named only for the purpose of easing documentation.) 
--
-- Note that the 'Step' relation automatically enforces preservation
-- since the arguments 'x' and 'y' are required to have the same type 't'.
data Step : (x : Term [] t) -> (y : Term [] t) -> Type where
  StApp1     : Step t1 t1' ->
               Step (TApp t1 t2) (TApp t1' t2)
  --
  StApp2     : Value v -> Step t2 t2' ->
               Step (TApp v t2) (TApp v t2')
  --
  StBeta     : Value v -> 
               Step (TApp (TAbs t) v) (subst v FZ t)
  --              
  StFix      : Step t t' ->
               Step (TFix t) (TFix t')
  --
  StFixBeta  : Step (TFix (TAbs t)) (subst (TFix (TAbs t)) FZ t)
  --
  StSucc     : Step t t' -> 
               Step (TSucc t) (TSucc t')
  --
  StPred     : Step t t' -> 
               Step (TPred t) (TPred t')
  --              
  StPredZero : Step (TPred TZero) TZero
  --
  StPredSucc : Value v ->
               Step (TPred (TSucc v)) v
  --
  StIfz      : Step t1 t1' ->
               Step (TIfz t1 t2 t3) (TIfz t1' t2 t3)
  --
  StIfzZero  : Step (TIfz TZero t1 t2) t1
  --
  StIfzSucc  : Value v ->
               Step (TIfz (TSucc v) t1 t2) t2
 
-- End: SMALL-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS
-----------------------------------------------------------------------



----------------------------
-- Begin: TRANSITIVE CLOSURE

-- Data type for representing the transistive closure
-- of an arbitrary relation 'rel : a -> a -> Type'.
using (a : Type, rel : a -> a -> Type)
  data TransCl : {a : Type} -> (a -> a -> Type) -> (a -> a -> Type) where
    TClRefl   : (x : a) -> TransCl rel x x 
    TClSingle : rel x y  -> TransCl rel x y
    TClTrans  : TransCl rel x y -> TransCl rel y z -> TransCl rel x z

        
-- Data type specifically for representing the
-- transitive closure of the 'Step' relation.
data TransStep : Term [] t -> Term [] t -> Type where
   TStRefl   : (e : Term [] t) -> TransStep e e
   TStTrans  : {e : Term [] t} -> {e' : Term [] t} -> {e'' : Term [] t} ->
               Step e e' -> TransStep e' e'' -> TransStep e e''


-- 'TransStep' is indeed transitive.
transStepTransitive : TransStep e1 e2 -> TransStep e2 e3 -> TransStep e1 e3
transStepTransitive (TStRefl _) y    = y
transStepTransitive (TStTrans x y) z = TStTrans x (transStepTransitive y z)


-- Correctness proof for 'TransStep', i.e.: TransStep => (TransCl Step).
transStepCorrect : TransStep e e' -> TransCl Step e e'
transStepCorrect (TStRefl e)    = TClRefl e
transStepCorrect (TStTrans x y) = TClTrans (TClSingle x) (transStepCorrect y)


-- Completeness proof for 'TransStep', i.e.: (TransCl Step) => TransStep.
transStepComplete : TransCl Step e e' -> TransStep e e'
transStepComplete (TClRefl e)    = TStRefl e
transStepComplete (TClSingle x)  = TStTrans x (TStRefl _)
transStepComplete (TClTrans x z) = transStepTransitive (transStepComplete x)
                                                       (transStepComplete z)

-- Operators for compact notation:
infixl 10 .++.
(.++.) : TransStep e1 e2 -> TransStep e2 e3 -> TransStep e1 e3
(.++.) = transStepTransitive 

infixl 10 .+.
(.+.) : TransStep e1 e2 -> Step e2 e3 -> TransStep e1 e3
(.+.) x y = x .++. (TStTrans y (TStRefl _))

-- End: TRANSITIVE CLOSURE
--------------------------
