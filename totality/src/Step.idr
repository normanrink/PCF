
module Step

-- Relation 'Step' for reducing terms
-- in the simply-typed lambda calculus.
 

import Term
import Subst


%default total
%access public export



-------------------------------------------------------------------------
-- Begin: SMALL-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS

data Step : (x : Term) -> (y : Term) -> Type where
  StApp1     : Step t1 t1' ->
               Step (TApp t1 t2) (TApp t1' t2)
  --
  StApp2     : Value v -> Step t2 t2' ->
               Step (TApp v t2) (TApp v t2')
  --
  StBeta     : Value v -> 
               Step (TApp (TAbs t) v) (subst v Z t)
  --
  StRec      : Step t t' -> 
               Step (TRec t t0 t1) (TRec t' t0 t1)
  --
  StRecZero  : Step (TRec TZero t0 t1) t0
  --
  StRecSucc  : Value (TSucc n) ->
               Step (TRec (TSucc n) t0 t1) 
                    (TApp ((TApp t1) n) (TRec n t0 t1))
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




--------------------------------
-- Begin: VALUES ARE IRREDUCIBLE

valueIrreducible : (e : Term) ->
                   Value e -> 
                   (Step e e' -> Void)
valueIrreducible TZero     VZero     step impossible
valueIrreducible (TSucc e) (VSucc v) (StSucc step) =
  valueIrreducible e v step
valueIrreducible (TAbs e)  VAbs      step impossible

-- End: VALUES ARE IRREDUCIBLE
------------------------------




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
data TransStep : Term -> Term -> Type where
   TStRefl   : (e : Term) -> TransStep e e
   TStTrans  : {e : Term} -> {e' : Term} -> {e'' : Term} ->
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




--------------------
-- Begin: CONGRUENCE

-- Construction of terms is a congruence
-- for the transitive closure of 'Step'.

-- Congruence lemma for '(TApp _ e)':
congApp1 : TransStep e1 e2 -> TransStep (TApp e1 e) (TApp e2 e)
congApp1 (TStRefl e1)   = TStRefl (TApp e1 _)
congApp1 (TStTrans x y) = TStTrans (StApp1 x) (congApp1 y)


-- Congruence lemma for '(TApp e _)':
congApp2 : {v : Value e} -> 
           TransStep e1 e2 -> TransStep (TApp e e1) (TApp e e2)
congApp2         (TStRefl e1)   = TStRefl (TApp _ e1)
congApp2 {v = v} (TStTrans x y) = TStTrans (StApp2 v x) (congApp2 {v = v} y)


-- Congruence lemma for '(Succ _)':
congSucc : TransStep e1 e2 -> TransStep (TSucc e1) (TSucc e2)
congSucc (TStRefl e1)   = TStRefl (TSucc e1)
congSucc (TStTrans x y) = TStTrans (StSucc x) (congSucc y)


-- Congruence lemma for '(Pred _)':
congPred : TransStep e1 e2 -> TransStep (TPred e1) (TPred e2)
congPred (TStRefl e1)   = TStRefl (TPred e1)
congPred (TStTrans x y) = TStTrans (StPred x) (congPred y)


-- Congruence lemma for '(Ifz _ ez es)':
congIfz : TransStep e1 e2 -> TransStep (TIfz e1 ez es) (TIfz e2 ez es)
congIfz (TStRefl e1)   = TStRefl (TIfz e1 _ _)
congIfz (TStTrans x y) = TStTrans (StIfz x) (congIfz y)


-- Congruence lemma for '(TRec _ e0 e1)':
congRec : TransStep e e' -> TransStep (TRec e e0 e1) (TRec e' e0 e1)
congRec (TStRefl e)    = TStRefl (TRec e _ _)
congRec (TStTrans x y) = TStTrans (StRec x) (congRec y)

-- End: CONGRUENCE
------------------
