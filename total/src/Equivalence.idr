
module Equivalence

-- Proof that small-step and big-step semantics for
-- the simply-typed lambda calculus are equivalent.


import BigStep
import Step
import Subst
import Term


%default total
%access export


--------------------------
-- Begin: STEP => BIG-STEP

stepToBigStep : Step e1 e2 -> BigStep e2 e3 ->
                BigStep e1 e3
-- case split in the following order: (Step e1 e2), (BigStep e2 e3)
stepToBigStep (StRec x) (BStValue _) impossible
--
stepToBigStep (StRec x) (BStRecZero z w) = let ih = stepToBigStep x z
                                           in BStRecZero ih w
--
stepToBigStep (StRec x) (BStRecSucc y z) = let ih = stepToBigStep x y
                                           in BStRecSucc ih z
--
stepToBigStep StRecZero x = BStRecZero (BStValue VZero) x
--                                    
stepToBigStep (StRecSucc x) y = BStRecSucc (BStValue x) y

stepToBigStep (StApp1 x) (BStValue _) impossible
--
stepToBigStep (StApp1 x) (BStApp w s1 t1) = let ih = stepToBigStep x w
                                            in BStApp ih s1 t1
--
stepToBigStep (StApp2 x z) (BStValue v) impossible
--
stepToBigStep (StApp2 x z) (BStApp s1 t1 u) = let ih = stepToBigStep z t1
                                              in BStApp s1 ih u
--
stepToBigStep (StBeta x) y = BStApp (BStValue VAbs) (BStValue x) y
--
stepToBigStep (StSucc x) (BStValue v) = case v of
  VAbs     impossible
  VZero    impossible
  VSucc v' => BStSucc $ stepToBigStep x (BStValue v')
--
stepToBigStep (StSucc x) (BStSucc y) = BStSucc $ stepToBigStep x y
--
stepToBigStep (StPred x) (BStValue _) impossible
--
stepToBigStep (StPred x) (BStPredZero z) = BStPredZero $ stepToBigStep x z
--
stepToBigStep (StPred x) (BStPredSucc y) = let ih = stepToBigStep x y 
                                           in BStPredSucc ih
--
stepToBigStep StPredZero (BStValue _) = BStPredZero (BStValue VZero)
--
stepToBigStep (StPredSucc x) y = BStPredSucc (BStSucc y)
--
stepToBigStep (StIfz x) (BStValue _) impossible
--
stepToBigStep (StIfz x) (BStIfzZero z w) = let ih = stepToBigStep x z
                                           in BStIfzZero ih w
--
stepToBigStep (StIfz x) (BStIfzSucc w s) = let ih = stepToBigStep x w
                                           in BStIfzSucc ih s
--
stepToBigStep StIfzZero y = BStIfzZero (BStValue VZero) y
--
stepToBigStep (StIfzSucc x) y = BStIfzSucc (BStValue (VSucc x)) y

-- End: STEP => BIG-STEP
------------------------



-------------------------------
-- Begin: TRANSSTEP => BIG-STEP

transStepToBigStep : (TransStep e1 e2) -> (v : Value e2) ->
                     BigStep e1 e2
transStepToBigStep (TStRefl _)    v = BStValue v
transStepToBigStep (TStTrans x y) v = let ih = transStepToBigStep y v
                                      in stepToBigStep x ih

-- End: TRANSSTEP => BIG-STEP
-----------------------------



-------------------------------
-- Begin: BIG-STEP => TRANSSTEP

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


bigStepToTransStep : BigStep e1 e2 -> (TransStep e1 e2, Value e2)
--
bigStepToTransStep (BStRecZero y z) = 
  let (tst1, v1) = bigStepToTransStep y
      (tst2, v2) = bigStepToTransStep z
      tst = (congRec tst1) .+. StRecZero .++. tst2
  in (tst, v2)
--  
bigStepToTransStep (BStRecSucc x y) = 
  let (tst1, v1) = bigStepToTransStep x
      (tst2, v2) = bigStepToTransStep y
      tst = (congRec tst1) .+. (StRecSucc v1) .++. tst2
  in (tst, v2)
--
bigStepToTransStep (BStValue v) = (TStRefl _, v)
--
bigStepToTransStep (BStApp z w t1) = 
  let (tst1, v1) = bigStepToTransStep z
      (tst2, v2) = bigStepToTransStep w
      (tst3, v3) = bigStepToTransStep t1
      tst = (congApp1 tst1) .++. (congApp2 {v = VAbs} tst2) .+. (StBeta v2) .++. tst3
  in (tst, v3)
--
bigStepToTransStep (BStSucc x) = 
  let (tst1, v1) = bigStepToTransStep x
  in (congSucc tst1, VSucc v1)
--
bigStepToTransStep (BStPredZero y) = 
  let (tst1, v1) = bigStepToTransStep y
      tst = congPred tst1 .+. StPredZero
  in (tst, VZero)
--
bigStepToTransStep (BStPredSucc x) = 
  let (tst1, VSucc v1) = bigStepToTransStep x
      tst = (congPred tst1) .+. (StPredSucc v1)
  in (tst, v1)

bigStepToTransStep (BStIfzZero z w) = 
  let (tst1, v1) = bigStepToTransStep z
      (tst2, v2) = bigStepToTransStep w
      tst = (congIfz tst1) .+. StIfzZero .++. tst2
  in (tst, v2)
  
bigStepToTransStep (BStIfzSucc w s) = 
  let (tst1, VSucc v1) = bigStepToTransStep w
      (tst2, v2) = bigStepToTransStep s
      tst = (congIfz tst1) .+. (StIfzSucc v1) .++. tst2
  in (tst, v2)

-- End: BIG-STEP => TRANSSTEP
-----------------------------



