
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
stepToBigStep (StApp1 x) (BStValue v) impossible
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
stepToBigStep (StFix x) (BStValue v) impossible
--
stepToBigStep (StFix x) (BStFix z w) = let ih = stepToBigStep x z
                                       in BStFix ih w
--
stepToBigStep StFixBeta y = BStFix (BStValue VAbs) y
--
stepToBigStep (StSucc x) (BStValue v) = case v of
  VAbs     impossible
  VZero    impossible
  VSucc v' => BStSucc $ stepToBigStep x (BStValue v')
--
stepToBigStep (StSucc x) (BStSucc y) = BStSucc $ stepToBigStep x y
--
stepToBigStep (StPred x) (BStValue v) impossible
--
stepToBigStep (StPred x) (BStPredZero z) = BStPredZero $ stepToBigStep x z
--
stepToBigStep (StPred x) (BStPredSucc y) = let ih = stepToBigStep x y 
                                           in BStPredSucc ih
--
stepToBigStep StPredZero (BStValue v) = BStPredZero (BStValue VZero)
--
stepToBigStep (StPredSucc x) y = BStPredSucc (BStSucc y)
--
stepToBigStep (StIfz x) (BStValue v) impossible
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


-- Congruence lemma for '(Fix _)':
total congFix : TransStep e1 e2 -> TransStep (TFix e1) (TFix e2)
congFix (TStRefl e1)   = TStRefl (TFix e1)
congFix (TStTrans x y) = TStTrans (StFix x) (congFix y)


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


bigStepToTransStep : BigStep e1 e2 -> (TransStep e1 e2, Value e2)
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
bigStepToTransStep (BStFix y z) = 
  let (tst1, v1) = bigStepToTransStep y
      (tst2, v2) = bigStepToTransStep z
      tst = (congFix tst1) .+. StFixBeta .++. tst2
  in (tst, v2)
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



-------------------------------------
-- Begin: CO-BIG-STEP => CO-TRANSSTEP

-- The relations 'CoTransStep' and 'CoBigStep' are not equivalent;
-- only one direction of the equivalence holds. To establish the
-- one-directional equivalence, the following lemma is needed, which
-- has the flavour of a progress lemma for big-step semantics: 
-- (cf. the proof of Lemma 36 in "Coinductive big-step operational
-- semantics" by X. Leroy and H. Grall)
coBigStepProgress : (e1 : Term [] t) -> (e2 : Term [] t) ->
                    CoBigStep e1 e2 -> 
                    Either (Value e1) (b : Term [] t ** (Step e1 b, CoBigStep b e2))
coBigStepProgress (TVar _) e2 cbst impossible
--
coBigStepProgress (TAbs _) e2 cbst = Left VAbs
--
coBigStepProgress (TApp x y) (TApp x y) (CoBStValue v) impossible
coBigStepProgress (TApp x y) e2 (CoBStApp {e=e2} {e1'=e1'} {e2'=e2'} cbst1 cbst2 cbst3) = 
  case coBigStepProgress x (TAbs e1') cbst1 of
       Left v => case v of
                      VAbs => case cbst1 of
                                   (CoBStValue {e=(TAbs e)} v') => case coBigStepProgress y e2' cbst2 of
                                                                        Left v'' => let eq     = coBigStepValueIrreducible cbst2 v''
                                                                                        cbst3' = replace {P = \z => CoBigStep (subst z First e) e2} (sym eq) cbst3 
                                                                                    in Right (_ ** (StBeta v'', cbst3'))
                                                                        Right (b ** (st, cbst)) => let cbst' = CoBStApp (CoBStValue v) cbst cbst3
                                                                                                   in Right (_ ** (StApp2 VAbs st, cbst'))
       Right (b ** (st, cbst)) => let st'   = StApp1 st
                                      cbst' = CoBStApp cbst cbst2 cbst3
                                  in Right (_ ** (st', cbst'))
--
coBigStepProgress (TFix x) (TFix x) (CoBStValue v) impossible
coBigStepProgress (TFix x) e2 (CoBStFix {e'=e'} cbst1 cbst2) = 
  case coBigStepProgress x (TAbs e') cbst1 of
       Left v => case v of
                      VAbs => case cbst1 of
                                   (CoBStValue {e=(TAbs e)} v) => Right (_ ** (StFixBeta, cbst2))
       Right (b ** (st, cbst)) => let st'   = StFix st
                                      cbst' = CoBStFix cbst cbst2
                                  in Right (_ ** (st', cbst'))
--
coBigStepProgress TZero e2 _ = Left VZero
--
coBigStepProgress (TSucc x) (TVar y) cbst impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStValue _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStApp _ _ _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStFix _ _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStSucc _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStPredZero _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStPredSucc _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStIfzZero _ _) impossible
coBigStepProgress (TSucc _) (TApp _ _) (CoBStIfzSucc _ _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStValue _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStApp _ _ _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStFix _ _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStSucc _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStPredZero _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStPredSucc _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStIfzZero _ _) impossible
coBigStepProgress (TSucc _) (TFix _) (CoBStIfzSucc _ _) impossible
coBigStepProgress (TSucc _) TZero (CoBStValue _) impossible
coBigStepProgress (TSucc _) TZero (CoBStApp _ _ _) impossible
coBigStepProgress (TSucc _) TZero (CoBStFix _ _) impossible
coBigStepProgress (TSucc _) TZero (CoBStSucc _) impossible
coBigStepProgress (TSucc _) TZero (CoBStPredZero _) impossible
coBigStepProgress (TSucc _) TZero (CoBStPredSucc _) impossible
coBigStepProgress (TSucc _) TZero (CoBStIfzZero _ _) impossible
coBigStepProgress (TSucc _) TZero (CoBStIfzSucc _ _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStValue _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStApp _ _ _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStFix _ _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStSucc _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStPredZero _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStPredSucc _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStIfzZero _ _) impossible
coBigStepProgress (TSucc _) (TPred _) (CoBStIfzSucc _ _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStValue _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStApp _ _ _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStFix _ _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStSucc _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStPredZero _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStPredSucc _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStIfzZero _ _) impossible
coBigStepProgress (TSucc _) (TIfz _ _ _) (CoBStIfzSucc _ _) impossible
coBigStepProgress (TSucc y) (TSucc y) (CoBStValue v) = Left v
coBigStepProgress (TSucc x) (TSucc y) (CoBStSucc cbst) = 
  case coBigStepProgress x y cbst of
       Left v => Left (VSucc v)
       Right (b ** (st, cbst)) => let st'   = StSucc st
                                      cbst' = CoBStSucc cbst
                                  in Right (_ ** (st', cbst'))
--
coBigStepProgress (TPred x) (TPred x) (CoBStValue v) impossible
coBigStepProgress (TPred x) TZero (CoBStPredZero cbst) = 
  case coBigStepProgress x TZero cbst of
       Left v => case v of
                      VZero    => Right (_ ** (StPredZero, CoBStValue VZero))
                      VSucc v' => case coBigStepValueIrreducible cbst v of
                                       Refl impossible
       Right (b ** (st, cbst)) => let st'   = StPred st
                                      cbst' = CoBStPredZero cbst
                                  in Right (_ ** (st', cbst'))
coBigStepProgress (TPred x) e2 (CoBStPredSucc cbst) = 
  case coBigStepProgress x (TSucc e2) cbst of
       Left v => case v of
                      VZero => case coBigStepValueIrreducible cbst v of
                                    Refl impossible
                      VSucc v' => case coBigStepValueIrreducible cbst v of
                                       Refl => Right (_ ** (StPredSucc v', CoBStValue v'))
       Right (b ** (st, cbst)) => let st' = StPred st
                                  in Right (_ ** (st', CoBStPredSucc cbst))
--
coBigStepProgress (TIfz x y z) (TIfz x y z) (CoBStValue v) impossible
coBigStepProgress (TIfz x y z) e2 (CoBStIfzZero cbst1 cbst2) = 
  case coBigStepProgress x TZero cbst1 of
       Left v => case coBigStepValueIrreducible cbst1 v of
                      Refl => Right (_ ** (StIfzZero, cbst2))
       Right (b ** (st, cbst)) => let st'   = StIfz st
                                      cbst' = CoBStIfzZero cbst cbst2
                                  in Right (_ ** (st', cbst'))
coBigStepProgress (TIfz x y z) e2 (CoBStIfzSucc cbst1 cbst2) = 
  case coBigStepProgress x (TSucc _) cbst1 of
       Left v => case coBigStepValueIrreducible cbst1 v of
                      Refl => case v of 
                                   VSucc v' => Right (_ ** (StIfzSucc v', cbst2))
       Right (b ** (st, cbst)) => let st'   = StIfz st
                                      cbst' = CoBStIfzSucc cbst cbst2
                                  in Right (_ **(st', cbst'))


-- With the previous lemma, one can finally prove the
-- implication 'CoBigStep' => 'CoTransStep':
-- (i.e. Lemma 36 in "Coinductive big-step operational semantics"
-- by X. Leroy and H. Grall)
coBigStepToTransStep : (e1 : Term [] t) -> (e2 : Term [] t) ->
                       CoBigStep e1 e2 -> CoTransStep e1 e2
coBigStepToTransStep e1 e2 cbst = 
  case coBigStepProgress e1 e2 cbst of
       Left v => case coBigStepValueIrreducible cbst v of
                      Refl => CoTStRefl e1
       Right (b ** (st, cbst)) => CoTStTrans st $ coBigStepToTransStep b e2 cbst 

-- End: CO-BIG-STEP => CO-TRANSSTEP
-----------------------------------


---------------------------------------
-- Begin: CO-TRANSSTEP =/=> CO-BIG-STEP

-- The following application serves to show that the relations
-- 'CoTransStep' and 'CoBigStep' are not equivalent:
-- (This example follows Lemma 36 in "Coinductive big-step
-- operational semantics" by X. Leroy and H. Grall.)
appOmega : Term [] TyNat
appOmega = TApp (TAbs {s=TyNat} TZero) (Subst.omega {t=TyNat})


-- Under 'CoTransStep' the term 'appOmega' evaluates to anything:
appOmegaCoTransStepAny : (e : Term [] TyNat) -> CoTransStep Equivalence.appOmega e
appOmegaCoTransStepAny e = let st = StApp2 {v=(TAbs TZero)} VAbs StFixBeta
                           in CoTStTrans st (appOmegaCoTransStepAny e)


-- The following re-states a result from 'Determinism.idr'
-- (in order to avoid importing 'Determinism.idr', which
-- would lead to a cycle of imports):
coBigStepOmegaAny : CoBigStep Subst.omega e
coBigStepOmegaAny = CoBStFix (CoBStValue VAbs) Equivalence.coBigStepOmegaAny


appOmegaCoBigStepZero : CoBigStep Equivalence.appOmega TZero
appOmegaCoBigStepZero = let cbst1  = CoBStValue {e=(TAbs TZero)} VAbs
                            cbst2  = Equivalence.coBigStepOmegaAny {e=Subst.omega}
                            cbst3  = CoBStValue VZero
                        in CoBStApp cbst1 cbst2 cbst3


-- Under 'CoBigStep' the term 'appOmega' only evaluates
-- to 'TZero' (and to nothing else):                                                
appOmegaCoBigStepOnlyZero : (e : Term [] TyNat) ->
                            CoBigStep Equivalence.appOmega e -> 
                            e = TZero                        
appOmegaCoBigStepOnlyZero _ (CoBStValue VZero)     impossible
appOmegaCoBigStepOnlyZero _ (CoBStValue (VSucc _)) impossible
appOmegaCoBigStepOnlyZero _ (CoBStValue VAbs)      impossible
appOmegaCoBigStepOnlyZero e (CoBStApp cbst1 cbst2 cbst3) = 
  case coBigStepValueIrreducible cbst1 VAbs of
       Refl => sym $ coBigStepValueIrreducible cbst3 VZero

-- End: CO-TRANSSTEP =/=> CO-BIG-STEP
-------------------------------------                   

