
module Determinism



import Step
import Term


%default total
%access export



stepDeterministic : {e1 : Term} -> {e2 : Term} -> {e3 : Term} ->
                    (Step e1 e2) -> (Step e1 e3) ->
                    e2 = e3
-- case split in the following order: (Step e1 e2), (Step e1 e3)
stepDeterministic (StApp1 st1) (StApp1 st2) = 
  let ih = stepDeterministic st1 st2
  in congApp ih Refl
stepDeterministic (StApp1 st1) (StApp2 v2 st2) = 
  absurd $ valueIrreducible _ v2 st1
stepDeterministic (StApp1 st1) (StBeta v2) impossible
--
stepDeterministic (StApp2 v1 _) (StApp1 st) = 
  absurd $ valueIrreducible _ v1 st
stepDeterministic (StApp2 v1 st1) (StApp2 v2 st2) = 
  let ih = stepDeterministic st1 st2
  in congApp Refl ih
stepDeterministic (StApp2 v1 st1) (StBeta v2) =
  absurd $ valueIrreducible _ v2 st1
--
stepDeterministic (StBeta v1) (StApp2 v2 st2) =
  absurd $ valueIrreducible _ v1 st2 
stepDeterministic (StBeta v1) (StBeta _) = Refl

--
stepDeterministic (StRec st1) (StRec st2) = 
  let ih = stepDeterministic st1 st2
  in congRec ih Refl Refl
stepDeterministic (StRec st1) StRecZero impossible
stepDeterministic (StRec st1) (StRecSucc v) = 
  absurd $ valueIrreducible _ v st1
--
stepDeterministic StRecZero (StRec _) impossible
stepDeterministic StRecZero StRecZero = Refl
--
stepDeterministic (StRecSucc v) (StRec st) = 
  absurd $ valueIrreducible _ v st
stepDeterministic (StRecSucc v) (StRecSucc _) = Refl
--
stepDeterministic (StSucc st1) (StSucc st2) = 
  congSucc $ stepDeterministic st1 st2
--
stepDeterministic (StPred st1) (StPred st2) = 
  congPred $ stepDeterministic st1 st2
stepDeterministic (StPred st1) StPredZero impossible
stepDeterministic (StPred st1) (StPredSucc v) = 
  absurd $ valueIrreducible _ (VSucc v) st1
--
stepDeterministic StPredZero (StPred _) impossible
stepDeterministic StPredZero StPredZero = Refl
--
stepDeterministic (StPredSucc v1) (StPred st) =
  absurd $ valueIrreducible _ (VSucc v1) st
stepDeterministic (StPredSucc v1) (StPredSucc _) = Refl 
--
stepDeterministic (StIfz st1) (StIfz st2) = 
  let ih = stepDeterministic st1 st2
  in congIfz ih Refl Refl
stepDeterministic (StIfz st1) StIfzZero impossible
stepDeterministic (StIfz st1) (StIfzSucc v) = 
  absurd $ valueIrreducible _ (VSucc v) st1
--
stepDeterministic StIfzZero (StIfz _) impossible
stepDeterministic StIfzZero StIfzZero = Refl
--
stepDeterministic (StIfzSucc v1) (StIfz st2) =
  absurd $ valueIrreducible _ (VSucc v1) st2
stepDeterministic (StIfzSucc v1) (StIfzSucc v2) = Refl




transStepDeterministic : (v2 : Value e2) -> (TransStep e1 e2) ->
                         (v3 : Value e3) -> (TransStep e1 e3) ->
                         e2 = e3
--
transStepDeterministic v2 (TStRefl e3) v3 (TStRefl e3) = Refl
--
transStepDeterministic v2 (TStRefl e2) v3 (TStTrans x y) = 
  absurd $ valueIrreducible e2 v2 x
--
transStepDeterministic v2 (TStTrans x z) v3 (TStRefl e3) = 
  absurd $ valueIrreducible e3 v3 x
--
transStepDeterministic {e2 = e2} v2 (TStTrans x z) v3 (TStTrans y w) =
  let eq = stepDeterministic x y
      z' = replace {P = \x => x} (cong {f = \e => TransStep e e2} eq) z
  in transStepDeterministic v2 z' v3 w



