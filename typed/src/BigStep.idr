
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
                BigStep (subst e2' FZ e1') e ->
                BigStep (TApp e1 e2) e
  --              
  BStFix      : BigStep e (TAbs e') ->
                BigStep (subst (TFix (TAbs e')) FZ e') e'' ->
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

