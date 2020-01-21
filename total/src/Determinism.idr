
module Determinism

--
-- WARNING: The totality checker needs about 
--
--                *** 87 minutes *** 
--
--          to check this file. This seems to
--          be due mostly to the function
--          'bigStepDeterministic'.
--
--          (Time measured on the following system:
--           Idris 1.3.0, Mac OS X 10.11.6,
--           Intel Core i7 2.5GHz, 16GB memory)
--


import BigStep
import Progress
import Step
import Subst
import Term


%default total
%access export


stepDeterministic : (Step e1 e2) -> (Step e1 e3) ->
                    e2 = e3
-- case split in the following order: (Step e1 e2), (Step e1 e3)
stepDeterministic {e1 = TRec _ e10 e11} (StRec x) (StRec y) = 
  cong {f = \e => TRec e e10 e11} $ stepDeterministic x y
--
stepDeterministic (StRec x) (StRecSucc y) = absurd $ valueIrreducible _ y x
--
stepDeterministic StRecZero StRecZero = Refl
--
stepDeterministic (StRecSucc x) (StRec y) = absurd $ valueIrreducible _ x y
--
stepDeterministic (StRecSucc x) (StRecSucc y) = Refl
--
stepDeterministic {e1 = TApp _ e11} (StApp1 x) (StApp1 y) = 
  cong {f = \e => TApp e e11} $ stepDeterministic x y
--
stepDeterministic (StApp1 x) (StApp2 y z) = absurd $ valueIrreducible _ y x
--  
stepDeterministic (StApp1 x) (StBeta y) = absurd $ valueIrreducible _ VAbs x
--
stepDeterministic (StApp2 x z) (StApp1 y) = absurd $ valueIrreducible _ x y
--
stepDeterministic {e1 = TApp e11 _} (StApp2 x z) (StApp2 y w) = 
  cong {f = \e => TApp e11 e} $ stepDeterministic z w
--  
stepDeterministic (StApp2 x z) (StBeta y) = absurd $ valueIrreducible _ y z
--
stepDeterministic (StBeta x) (StApp2 y z) = absurd $ valueIrreducible _ x z
--
stepDeterministic (StBeta x) (StBeta y) = Refl
--
stepDeterministic (StSucc x) (StSucc y) = cong $ stepDeterministic x y
--
stepDeterministic (StPred x) (StPred y) = cong $ stepDeterministic x y
--
stepDeterministic (StPred x) StPredZero = absurd $ valueIrreducible _ VZero x
--
stepDeterministic (StPred x) (StPredSucc y) = absurd $ valueIrreducible _ (VSucc y) x
--
stepDeterministic StPredZero (StPred x) = absurd $ valueIrreducible _ VZero x
--
stepDeterministic StPredZero StPredZero = Refl
--
stepDeterministic (StPredSucc x) (StPred y) = absurd $ valueIrreducible _ (VSucc x) y
--
stepDeterministic (StPredSucc x) (StPredSucc y) = Refl
--
stepDeterministic {e1 = TIfz _ e12 e13} (StIfz x) (StIfz y) = 
  cong {f = \e => TIfz e e12 e13} $ stepDeterministic x y
--  
stepDeterministic (StIfz x) StIfzZero = absurd $ valueIrreducible _ VZero x
--
stepDeterministic (StIfz x) (StIfzSucc y) = absurd $ valueIrreducible _ (VSucc y) x
--
stepDeterministic StIfzZero (StIfz x) = absurd $ valueIrreducible _ VZero x
--
stepDeterministic StIfzZero StIfzZero = Refl
--
stepDeterministic (StIfzSucc x) (StIfz y) = absurd $ valueIrreducible _ (VSucc x) y
--
stepDeterministic (StIfzSucc x) (StIfzSucc y) = Refl



transStepDeterministic : (v2 : Value e2) -> (TransStep e1 e2) ->
                         (v3 : Value e3) -> (TransStep e1 e3) ->
                         e2 = e3
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



--
-- The following proof of the determinism of 'BigStep'
-- relies on the equivalence of 'Step' and 'BigStep'.
--
-- import Equivalence   -- must go at the top of the file
--
-- bigStepDeterministic : (BigStep e1 e2 v2) ->
--                        (BigStep e1 e3 v3) ->
--                        e2 = e3
-- bigStepDeterministic x y = 
--   let (tst2, v2) = bigStepToTransStep x
--       (tst3, v3) = bigStepToTransStep y
--   in transStepDeterministic v2 tst2 v3 tst3
--



injectiveAbs : (TAbs e1 = TAbs e2) -> e1 = e2
injectiveAbs Refl = Refl


injectiveSucc : (TSucc e1 = TSucc e2) -> e1 = e2
injectiveSucc Refl = Refl


zeroNotSucc : (TZero = TSucc _) -> Void
zeroNotSucc Refl impossible


pairEq : a = b -> c = d -> (a, c) = (b, d)
pairEq Refl Refl = Refl


valueBigStepEq : Value e1 -> BigStep e1 e2 -> e1 = e2
valueBigStepEq VZero (BStValue _)     = Refl
valueBigStepEq (VSucc x) (BStValue _) = Refl
valueBigStepEq (VSucc x) (BStSucc y)  = cong $ valueBigStepEq x y
valueBigStepEq VAbs (BStValue _)      = Refl


bigStepDeterministic : (BigStep e1 e2) -> (BigStep e1 e3) ->
                       e2 = e3
-- case split in the following order: (BigStep e1 e2), (BigStep e1 e3)
bigStepDeterministic (BStRecZero y z) (BStValue _) impossible
--
bigStepDeterministic (BStRecZero y z) (BStRecZero w s) = bigStepDeterministic z s
--
bigStepDeterministic (BStRecZero y z) (BStRecSucc x w) = 
  let ih = bigStepDeterministic y x
  in absurd $ zeroNotSucc ih
--
bigStepDeterministic (BStRecSucc x y) (BStValue _) impossible
--
bigStepDeterministic (BStRecSucc x y) (BStRecZero w s) =
  let ih = bigStepDeterministic x w
  in absurd $ zeroNotSucc $ sym ih
--
bigStepDeterministic {e1 = TRec e e10 e11} {e2 = e2} (BStRecSucc x y) (BStRecSucc z w) = 
  let ih = injectiveSucc $ bigStepDeterministic x z
      y' = replace {P = \x => BigStep (subst x FZ (subst (TRec x e10 e11) FZ e11)) e2} ih y
  in bigStepDeterministic y' w
--
bigStepDeterministic (BStValue _) (BStValue _) = Refl
--
bigStepDeterministic (BStValue _) (BStApp z w t) impossible
--
bigStepDeterministic (BStValue v2) (BStSucc x) = case v2 of
  VAbs      impossible
  VZero     impossible
  VSucc v2' => cong $ valueBigStepEq v2' x
--  
bigStepDeterministic (BStValue _) (BStPredZero y) impossible
--
bigStepDeterministic (BStValue _) (BStPredSucc x) impossible
--
bigStepDeterministic (BStValue _) (BStIfzZero z w) impossible
--
bigStepDeterministic (BStValue _) (BStIfzSucc w s) impossible
--
bigStepDeterministic (BStApp w t u) (BStValue _) impossible
--
bigStepDeterministic {e2 = e2} (BStApp w t u) (BStApp z s v) = 
  let ih1 = injectiveAbs $ bigStepDeterministic w z
      ih2 = bigStepDeterministic t s
      peq = pairEq ih1 ih2
      u'  = replace {P = \x => BigStep (subst (snd x) FZ (fst x)) e2} peq u
  in bigStepDeterministic u' v
--
bigStepDeterministic (BStSucc x) (BStValue v3) = case v3 of
  VAbs      impossible
  VZero     impossible
  VSucc v3' => cong . sym $ valueBigStepEq v3' x
--
bigStepDeterministic (BStSucc x) (BStSucc y) = cong $ bigStepDeterministic x y
--
bigStepDeterministic (BStPredZero z) (BStValue _) impossible
--
bigStepDeterministic (BStPredZero z) (BStPredZero y) = Refl
--
bigStepDeterministic (BStPredZero z) (BStPredSucc x) = 
  let ih = bigStepDeterministic z x
  in absurd $ zeroNotSucc ih
--
bigStepDeterministic (BStPredSucc x) (BStValue _) impossible
--
bigStepDeterministic (BStPredSucc x) (BStPredZero z) = 
  let ih = bigStepDeterministic x z
  in absurd $ zeroNotSucc (sym ih)
--
bigStepDeterministic (BStPredSucc x) (BStPredSucc y) = injectiveSucc $ bigStepDeterministic x y
--
bigStepDeterministic (BStIfzZero w s) (BStValue _) impossible
--
bigStepDeterministic (BStIfzZero w s) (BStIfzZero y z) = bigStepDeterministic s z
--
bigStepDeterministic (BStIfzZero w s) (BStIfzSucc z t) = 
  let ih = bigStepDeterministic w z
  in absurd $ zeroNotSucc ih
--
bigStepDeterministic (BStIfzSucc s t) (BStValue _) impossible
--
bigStepDeterministic (BStIfzSucc s t) (BStIfzZero y z) = 
  let ih = bigStepDeterministic s y
  in absurd $ zeroNotSucc (sym ih)
--
bigStepDeterministic (BStIfzSucc s t) (BStIfzSucc z w) = bigStepDeterministic t w
