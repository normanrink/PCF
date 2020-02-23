
module BigStep

-- Relation 'BigStep' for fully reducing terms
-- in the simply-typed lambda calculus to values.
 

import Term
import Subst


%default total
%access public export


-----------------------------------------------------------------------
-- Begin: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS

-- The relation 'BigStep' defines evaluation of terms in the lambda
-- calculus following big-step semantics.
--
-- Big-step semantics fully evaluates terms to values.
-- (A proof of this statement appears below.)
data BigStep : Term [] t -> (y: Term [] t) -> Type where
  BStValue    : (v : Value e) -> BigStep e e
  --
  BStApp      : BigStep e1 (TAbs e1') ->
                BigStep e2 e2' ->
                BigStep (subst e2' First e1') e ->
                BigStep (TApp e1 e2) e
  --              
  BStFix      : BigStep e (TAbs e') ->
                BigStep (subst (TFix (TAbs e')) First e') e'' ->
                BigStep (TFix e) e''
  --           
  BStSucc     : BigStep e e' ->
                BigStep (TSucc e) (TSucc e')
  --            
  BStPredZero : BigStep e TZero ->
                BigStep (TPred e) TZero
  --                
  BStPredSucc : BigStep e (TSucc e') ->
                BigStep (TPred e) e'
  --                
  BStIfzZero  : BigStep e1 TZero ->
                BigStep e2 e ->
                BigStep (TIfz e1 e2 _) e
  --              
  BStIfzSucc  : BigStep e1 (TSucc _) ->
                BigStep e3 e ->
                BigStep (TIfz e1 _ e3) e


bigStepFst : {e : Term [] t} -> BigStep e _ -> Term [] t
bigStepFst {e = e} _ = e


bigStepSnd : {e : Term [] t} -> BigStep _ e -> Term [] t
bigStepSnd {e = e} _ = e


bigStepValue : BigStep _ e -> Value e
bigStepValue (BStValue v)     = v
bigStepValue (BStApp _ _ z)   = bigStepValue z
bigStepValue (BStFix _ z)     = bigStepValue z
bigStepValue (BStSucc z)      = VSucc (bigStepValue z)
bigStepValue (BStPredZero _)  = VZero
bigStepValue (BStPredSucc z)  = case bigStepValue z of
                                    VZero impossible
                                    VSucc v => v
bigStepValue (BStIfzZero _ z) = bigStepValue z
bigStepValue (BStIfzSucc _ z) = bigStepValue z
               
-- End: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------



---------------------------------------------------------
-- Begin: DIVERGENCE OF TERM 'Subst.omega' UNDER BIG-STEP

-- The following straightforward approach to proving
-- that 'omega' diverges does not pass Idris' totality
-- checker because of the rewriting of 'bst' in the
-- induction step:
--
-- divergenceOmega : BigStep Subst.omega e -> Void
-- divergenceOmega {e = _} (BStValue v) = case v of
--                                             VZero     impossible
--                                             (VSucc _) impossible
--                                             VAbs      impossible
-- divergenceOmega {e = e} (BStFix (BStValue v) bst) =
--   let bst' = replace {P = \x => BigStep x e} substOmega bst
--   in divergenceOmega bst'


-- To prove that 'omega' diverges under big-step semantics,
-- an indexed version of the 'BigStep' relation is introduced:
data BigStepN : Nat -> Term [] t -> (y: Term [] t) -> Type where
  BStValueN    : (v : Value e) -> BigStepN Z e e
  --
  BStAppN      : BigStepN k e1 (TAbs e1') ->
                 BigStepN m e2 e2' ->
                 BigStepN n (subst e2' First e1') e ->
                 BigStepN (S $ k+m+n) (TApp e1 e2) e
  --              
  BStFixN      : BigStepN m e (TAbs e') ->
                 BigStepN n (subst (TFix (TAbs e')) First e') e'' ->
                 BigStepN (S $ m+n) (TFix e) e''
  --           
  BStSuccN     : BigStepN n e e' ->
                 BigStepN (S n) (TSucc e) (TSucc e')
  --            
  BStPredZeroN : BigStepN n e TZero ->
                 BigStepN (S n) (TPred e) TZero
  --                
  BStPredSuccN : BigStepN n e (TSucc e') ->
                 BigStepN (S n) (TPred e) e'
  --                
  BStIfzZeroN  : BigStepN m e1 TZero ->
                 BigStepN n e2 e ->
                 BigStepN (S $ m+n) (TIfz e1 e2 _) e
  --              
  BStIfzSuccN  : BigStepN m e1 (TSucc _) ->
                 BigStepN n e3 e ->
                 BigStepN (S $ m+n) (TIfz e1 _ e3) e


bigStepToN : BigStep e1 e2 -> (n : Nat ** BigStepN n e1 e2)
bigStepToN (BStValue v) = (Z ** BStValueN v)
--
bigStepToN (BStApp bst1 bst2 bst3) = let (n1 ** bstn1) = bigStepToN bst1
                                         (n2 ** bstn2) = bigStepToN bst2
                                         (n3 ** bstn3) = bigStepToN bst3
                                     in ((S $ n1+n2+n3) ** BStAppN bstn1 bstn2 bstn3)
--                                     
bigStepToN (BStFix bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                    (n2 ** bstn2) = bigStepToN bst2
                                in ((S $ n1+n2) ** BStFixN bstn1 bstn2) 
--                            
bigStepToN (BStSucc bst) = let (n ** bstn) = bigStepToN bst
                           in ((S n) ** BStSuccN bstn)
--                            
bigStepToN (BStPredZero bst) = let (n ** bstn) = bigStepToN bst
                               in ((S n) ** BStPredZeroN bstn)
--                               
bigStepToN (BStPredSucc bst) = let (n ** bstn) = bigStepToN bst
                               in ((S n) ** BStPredSuccN bstn)
--
bigStepToN (BStIfzZero bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                        (n2 ** bstn2) = bigStepToN bst2
                                    in ((S $ n1+n2) ** BStIfzZeroN bstn1 bstn2) 
--                            
bigStepToN (BStIfzSucc bst1 bst2) = let (n1 ** bstn1) = bigStepToN bst1
                                        (n2 ** bstn2) = bigStepToN bst2
                                    in ((S $ n1+n2) ** BStIfzSuccN bstn1 bstn2) 


bigStepFromN : BigStepN n e1 e2 -> BigStep e1 e2
bigStepFromN (BStValueN v) = BStValue v
--
bigStepFromN (BStAppN bstn1 bstn2 bstn3) = let bst1 = bigStepFromN bstn1
                                               bst2 = bigStepFromN bstn2
                                               bst3 = bigStepFromN bstn3
                                           in BStApp bst1 bst2 bst3
--                                     
bigStepFromN (BStFixN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                         bst2 = bigStepFromN bstn2
                                     in BStFix bst1 bst2
--                                     
bigStepFromN (BStSuccN bstn) = let bst = bigStepFromN bstn
                               in BStSucc bst
--
bigStepFromN (BStPredZeroN bstn) = let bst = bigStepFromN bstn
                                   in BStPredZero bst
--
bigStepFromN (BStPredSuccN bstn) = let bst = bigStepFromN bstn
                                   in BStPredSucc bst
--
bigStepFromN (BStIfzZeroN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                             bst2 = bigStepFromN bstn2
                                         in BStIfzZero bst1 bst2
--
bigStepFromN (BStIfzSuccN bstn1 bstn2) = let bst1 = bigStepFromN bstn1
                                             bst2 = bigStepFromN bstn2
                                         in BStIfzSucc bst1 bst2


-- Divergence of 'omega' under the indexed version of big-step semantics:
divergenceOmega' : {e : Term [] TyNat} -> (n : Nat) -> BigStepN n Subst.omega e -> Void
divergenceOmega' Z (BStValueN v) = case v of
                                        VZero     impossible
                                        (VSucc _) impossible
                                        VAbs      impossible
divergenceOmega' {e} (S n) bstn = case bstn of
  (BStFixN (BStValueN v) bstn2) => let bstn2' = replace {P = \x => BigStepN n x e} substOmega bstn2
                                   in divergenceOmega' n bstn2'


divergenceOmega : BigStep Subst.omega e -> Void
divergenceOmega bst = let (n ** bstn) = bigStepToN bst
                      in divergenceOmega' n bstn

-- End: DIVERGENCE OF TERM 'Subst.omega' UNDER BIG-STEP
-------------------------------------------------------


