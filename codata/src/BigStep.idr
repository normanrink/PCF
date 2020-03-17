
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

               
bigStepValueIrreducible : BigStep e1 e2 -> Value e1 -> e1 = e2
bigStepValueIrreducible (BStValue VZero) VZero   = Refl
bigStepValueIrreducible (BStValue v1) (VSucc v2) = Refl
bigStepValueIrreducible (BStSucc bst) (VSucc v)  = 
  cong $ bigStepValueIrreducible bst v
bigStepValueIrreducible (BStValue v)  VAbs       = Refl


bigStepTransitive : BigStep e1 e2 -> BigStep e2 e3 -> BigStep e1 e3
bigStepTransitive (BStValue v) bst = bst
bigStepTransitive (BStApp x w t) y = BStApp x w $ bigStepTransitive t y
bigStepTransitive (BStFix x w) y = BStFix x $ bigStepTransitive w y
bigStepTransitive (BStSucc x) (BStValue v) = BStSucc x
bigStepTransitive (BStSucc x) (BStSucc y)  = BStSucc $ bigStepTransitive x y
bigStepTransitive (BStPredZero x) (BStValue v) = BStPredZero x
bigStepTransitive (BStPredSucc x) y = let bst1 = BStSucc y
                                          bst2 = bigStepTransitive x bst1
                                      in BStPredSucc bst2
bigStepTransitive (BStIfzZero w s) y = BStIfzZero w (bigStepTransitive s y)
bigStepTransitive (BStIfzSucc w s) y = BStIfzSucc w (bigStepTransitive s y)

-- End: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------



-------------------------------------------------------
-- Begin: CO-INDUCTIVE RELATION FOR BIG-STEP EVALUATION

codata CoBigStep : Term [] t -> (y: Term [] t) -> Type where
  CoBStValue    : (v : Value e) -> CoBigStep e e
  --
  CoBStApp      : CoBigStep e1 (TAbs e1') ->
                  CoBigStep e2 e2' ->
                  CoBigStep (subst e2' First e1') e ->
                  CoBigStep (TApp e1 e2) e
  --              
  CoBStFix      : CoBigStep e (TAbs e') ->
                  CoBigStep (subst (TFix (TAbs e')) First e') e'' ->
                  CoBigStep (TFix e) e''
  --           
  CoBStSucc     : CoBigStep e e' ->
                  CoBigStep (TSucc e) (TSucc e')
  --            
  CoBStPredZero : CoBigStep e TZero ->
                  CoBigStep (TPred e) TZero
  --                
  CoBStPredSucc : CoBigStep e (TSucc e') ->
                  CoBigStep (TPred e) e'
  --                
  CoBStIfzZero  : CoBigStep e1 TZero ->
                  CoBigStep e2 e ->
                  CoBigStep (TIfz e1 e2 _) e
  --              
  CoBStIfzSucc  : CoBigStep e1 (TSucc _) ->
                  CoBigStep e3 e ->
                  CoBigStep (TIfz e1 _ e3) e


coBigStepValueIrreducible : CoBigStep e1 e2 -> Value e1 -> e1 = e2
coBigStepValueIrreducible (CoBStValue VZero) VZero      = Refl
coBigStepValueIrreducible (CoBStValue v1)    (VSucc v2) = Refl
coBigStepValueIrreducible (CoBStSucc cbst)   (VSucc v)  = 
  cong $ coBigStepValueIrreducible cbst v
coBigStepValueIrreducible (CoBStValue v)     VAbs       = Refl


coBigStepTransitive : CoBigStep e1 e2 -> CoBigStep e2 e3 -> CoBigStep e1 e3
coBigStepTransitive (CoBStValue v) y = y
coBigStepTransitive (CoBStApp x z w) y = CoBStApp x z $ coBigStepTransitive w y 
coBigStepTransitive (CoBStFix x z) y = CoBStFix x $ coBigStepTransitive z y
coBigStepTransitive (CoBStSucc x) (CoBStValue v) = CoBStSucc x
coBigStepTransitive (CoBStSucc x) (CoBStSucc y) = CoBStSucc $ coBigStepTransitive x y
coBigStepTransitive (CoBStPredZero x) (CoBStValue v) = CoBStPredZero x
coBigStepTransitive (CoBStPredSucc x) y = let cbst1 = CoBStSucc y
                                          in CoBStPredSucc $ coBigStepTransitive x cbst1
coBigStepTransitive (CoBStIfzZero z w) y = CoBStIfzZero z $ coBigStepTransitive w y
coBigStepTransitive (CoBStIfzSucc w s) y = CoBStIfzSucc w $ coBigStepTransitive s y


bigStepToCoBigStep : BigStep e1 e2 -> CoBigStep e1 e2
bigStepToCoBigStep (BStValue v) = CoBStValue v
bigStepToCoBigStep (BStApp bst1 bst2 bst3) = CoBStApp (bigStepToCoBigStep bst1)
                                                      (bigStepToCoBigStep bst2)
                                                      (bigStepToCoBigStep bst3)
bigStepToCoBigStep (BStFix bst1 bst2) = CoBStFix (bigStepToCoBigStep bst1)
                                                 (bigStepToCoBigStep bst2)
bigStepToCoBigStep (BStSucc bst) = CoBStSucc $ bigStepToCoBigStep bst
bigStepToCoBigStep (BStPredZero bst) = CoBStPredZero $ bigStepToCoBigStep bst
bigStepToCoBigStep (BStPredSucc bst) = CoBStPredSucc $ bigStepToCoBigStep bst
bigStepToCoBigStep (BStIfzZero bst1 bst2) = CoBStIfzZero (bigStepToCoBigStep bst1)
                                                         (bigStepToCoBigStep bst2)
bigStepToCoBigStep (BStIfzSucc bst1 bst2) = CoBStIfzSucc (bigStepToCoBigStep bst1)
                                                         (bigStepToCoBigStep bst2)
                                                         
-- End: CO-INDUCTIVE RELATION FOR BIG-STEP EVALUATION
-----------------------------------------------------







