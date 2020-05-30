
module R

-- Definition of the logical relation 'R'
-- that is central to proving normalization
-- for the simply-typed lambda calculus
-- (with primitive recursion).


import Determinism
import PnP
import Step
import Term
import Typing


%default total
%access export



---------------------------
-- Begin: PREDICATE 'HALTS'

-- The predicate 'Halts' defines what it
-- means that the evaluation of a term 'e'
-- under 'Step' terminates - namely that
-- the term 'e' must evaluate to a value:
public export
data Halts : Term -> Type where
  H : (e : Term) ->
      (e' : Term ** (Value e', TransStep e e'))
      -> Halts e


-- For terms 'e1' and 'e2', if one of them steps
-- to the other, then either both satisfy 'Halts'
-- or neither term does; in formulae:
-- 
--   Step e1 e2 => (Halts e1 <=> Halts e2)
--
-- The following two lemmas establish this equivalence,
-- given 'Step e1 e2'.
-- The next two lemmas then extend this equivalence to
-- the 'TransStep' relation.

stepPreservesHalts_1 : (e : Term) -> (e' : Term) ->
                       Step e e' -> Halts e -> Halts e'
stepPreservesHalts_1 e e' step (H e ev) = case ev of
  (x ** (vx, tstx)) => case tstx of
                            (TStRefl e) => absurd $ valueIrreducible e vx step
                            (TStTrans st tst) => case stepDeterministic step st of
                                                      Refl => H e' (x ** (vx, tst))


stepPreservesHalts_2 : (e : Term) -> (e' : Term) ->
                       Step e e' -> Halts e' -> Halts e
stepPreservesHalts_2 e e' step (H e' ev) = case ev of
  (x ** (vx, tstx)) => H e (x ** (vx, TStTrans step tstx))



transStepPreservesHalts_1 : (e : Term) -> (e' : Term) ->
                          TransStep e e' -> Halts e -> Halts e'
transStepPreservesHalts_1 e e  (TStRefl e)       h = h
transStepPreservesHalts_1 e e' (TStTrans st tst) h = 
  let h' = stepPreservesHalts_1 _ _ st h
  in transStepPreservesHalts_1 _ _ tst h'


transStepPreservesHalts_2 : (e : Term) -> (e' : Term) ->
                          TransStep e e' -> Halts e' -> Halts e
transStepPreservesHalts_2 e e (TStRefl e)        h = h
transStepPreservesHalts_2 e e' (TStTrans st tst) h = 
  let h' = transStepPreservesHalts_2 _ _ tst h
  in stepPreservesHalts_2 _ _ st h'
  


haltsAbs : (e : Term) -> Halts (TAbs e)
haltsAbs e = H (TAbs e) (TAbs e ** (VAbs, TStRefl (TAbs e)))



haltsZero : Halts TZero
haltsZero = H TZero (TZero ** (VZero, TStRefl TZero))

-- End: PREDICATE 'HALTS'
-------------------------




--------------------------------------
-- Begin: (UNARY) LOGICAL RELATION 'R'

mutual
  public export
  r : (t : Ty) -> (e : Term) -> Type
  r TyNat       e = (Typing [] e TyNat,    Halts e)
  r (TyFun s t) e = (Typing [] e (s:->:t), Halts e, rFun s t e)

  public export
  rFun : (s : Ty) -> (t : Ty) -> (e : Term) -> Type
  rFun s t e = (y : Term) -> r s y -> r t (TApp e y)


rTyping : (e : Term) -> r t e -> Typing [] e t
rTyping {t = TyNat}         _ r = fst r
rTyping {t = (TyFun t1 t2)} _ r = fst r


rHalts : r t e -> Halts e
rHalts {t = TyNat}         r = snd r
rHalts {t = (TyFun t1 t2)} r = fst $ snd r


rHalts' : r t e -> (e' : Term ** (Value e', TransStep e e'))
rHalts' r = case rHalts r of
                 (H _ ev) => ev


rImplication : r (s :->: t) e -> rFun s t e
rImplication r =  snd $ snd r


-- Forward stepping preserves the predicate 'R':
mutual
  stepPreservesR_1 : (t : Ty) -> 
                     (e  : Term) -> (e' : Term) ->
                     Step e e' -> r t e -> r t e'
  stepPreservesR_1 TyNat       e e' st (ty, h) = 
    let ty' = preservation e ty st
        h'  = stepPreservesHalts_1 e e' st h
    in (ty', h')
  stepPreservesR_1 (TyFun s t) e e' st (ty, h, imp) =
    let ty'  = preservation e ty st
        h'   = stepPreservesHalts_1 e e' st h
        imp' = stepPreservesR_1_Fun s t e e' st imp 
    in (ty', h', imp')


  stepPreservesR_1_Fun : (s : Ty) -> (t : Ty) ->
                         (e  : Term) -> (e' : Term) ->
                         Step e e' -> rFun s t e -> rFun s t e'
  stepPreservesR_1_Fun s t e e' st imp y ry = 
    let r'  = imp y ry
        st' = StApp1 st
    in stepPreservesR_1 t _ _ st' r'



-- Backward stepping preserves the predicate 'R',
-- but an explicit typing of the expression 'e'
-- (i.e. the expression that steps) must be provided:
-- (For the forward direction, an explicit typing
-- argument is not required thanks to 'preservation'.)
mutual
  stepPreservesR_2 : (t : Ty) -> 
                     (e  : Term) -> (Typing [] e t) ->
                     (e' : Term) ->
                     Step e e' -> r t e' -> r t e
  stepPreservesR_2 TyNat       e ty e' st (_, h') = 
    let h = stepPreservesHalts_2 e e' st h'
    in (ty, h)
  stepPreservesR_2 (TyFun s t) e ty e' st (_, h', imp') = 
    let h   = stepPreservesHalts_2 e e' st h'
        imp = stepPreservesR_2_Fun s t e ty e' st imp'
    in (ty, h, imp)


  stepPreservesR_2_Fun : (s : Ty) -> (t : Ty) ->
                         (e  : Term) -> (Typing [] e (s :->: t)) ->
                         (e' : Term) ->
                         Step e e' -> rFun s t e' -> rFun s t e
  stepPreservesR_2_Fun s t e ty e' st imp' y ry = 
    let r   = imp' y ry 
        st' = StApp1 st
        tyy = rTyping y ry
        tya = TyApp ty tyy
    in stepPreservesR_2 t _ tya _ st' r



transStepPreservesR_1 : (t : Ty) -> 
                        (e  : Term) -> (e' : Term) ->
                        TransStep e e' -> r t e -> r t e'
transStepPreservesR_1 t e _  (TStRefl _)       re = re
transStepPreservesR_1 t e e' (TStTrans st tst) re = let r' = stepPreservesR_1 t _ _ st re
                                                    in transStepPreservesR_1 t _ _ tst r'

                                               
transStepPreservesR_2 : (t : Ty) -> 
                        (e  : Term) -> (Typing [] e t) ->
                        (e' : Term) ->
                        TransStep e e' -> r t e' -> r t e
transStepPreservesR_2 t e ty _  (TStRefl _)       re' = re'
transStepPreservesR_2 t e ty e' (TStTrans st tst) re' = 
  let ty1 = preservation e ty st
      r'  = transStepPreservesR_2 t _ ty1 _ tst re'
  in stepPreservesR_2 t _ ty _ st r'



rZero : r TyNat TZero
rZero = (TyZero, haltsZero)

-- End: (UNARY) LOGICAL RELATION 'R'
------------------------------------




-----------------------------------------
-- Begin: INVERT PREDICATE 'R' OF 'TSucc' 

transStepSuccInjective : TransStep (TSucc e1) (TSucc e2) -> TransStep e1 e2
transStepSuccInjective (TStRefl (TSucc e1)) = TStRefl _
transStepSuccInjective (TStTrans (StSucc st) tst) = 
  let ih = transStepSuccInjective tst
  in TStTrans st ih


transStepSuccSucc : TransStep (TSucc e1) e2 -> (e2' : Term ** e2 = TSucc e2')
transStepSuccSucc (TStRefl (TSucc e1)) = (e1 ** Refl)
transStepSuccSucc (TStTrans (StSucc st) tst) = transStepSuccSucc tst


succHaltsHalts : Typing ctx (TSucc e) TyNat -> Halts (TSucc e) -> Halts e
succHaltsHalts (TySucc ty) (H (TSucc e) (_ ** (v, tst))) = 
  let ty' = transPreservation (TSucc e) (TySucc ty) tst  
  in case canonicalNat _ ty' v of
          (Left Refl) => let (_ ** eq) = transStepSuccSucc tst
                         in case eq of Refl impossible
          (Right (_ ** (v', Refl))) => let tst' = transStepSuccInjective tst
                                       in H _ (_ ** (v', tst'))


succRR : r TyNat (TSucc e) -> r TyNat e
succRR re = let ty = rTyping _ re
                h  = rHalts re
            in case ty of
                    (TySucc ty') => (ty', succHaltsHalts ty h)
                
-- End: INVERT PREDICATE 'R' OF 'TSucc' 
---------------------------------------
