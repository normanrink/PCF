
module BigStep

-- Relation 'BigStep' for fully reducing terms
-- in the untyped lambda calculus to values.
 

import Term
import Subst


%default total
%access public export


-----------------------------------------------------------------------
-- Begin: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS

-- The relation 'BigStep' defines evaluation of terms in the lambda
-- calculus following big-step semantics.
--
-- Since big-step semantics fully evaluates terms to values, the
-- type constructor 'BigStep' requires as its third argument
-- evidence that 'y' is indeed a value.
data BigStep : Term 0 -> (y: Term 0) -> Value y -> Type where
  BStValue    : (v : Value e) -> BigStep e e v
  --
  BStApp      : BigStep e1 (TAbs e1') _ ->
                BigStep e2 e2' _ ->
                BigStep (subst e2' FZ e1') e v ->
                BigStep (TApp e1 e2) e v
  --
  BStSucc     : BigStep e e' v ->
                BigStep (TSucc e) (TSucc e') (VSucc v)
  --            
  BStPredZero : BigStep e TZero _ ->
                BigStep (TPred e) TZero _
  --                
  BStPredSucc : BigStep e (TSucc e') (VSucc v) ->
                BigStep (TPred e) e' v
  --                
  BStIfzZero  : BigStep e1 TZero _ ->
                BigStep e2 e v ->
                BigStep (TIfz e1 e2 _) e v
  --              
  BStIfzSucc  : BigStep e1 (TSucc _) _ ->
                BigStep e3 e v ->
                BigStep (TIfz e1 _ e3) e v


bigStepFst : {e : Term 0} -> BigStep e _ _ -> Term 0
bigStepFst {e = e} _ = e


bigStepSnd : {e : Term 0} -> BigStep _ e _ -> Term 0
bigStepSnd {e = e} _ = e


bigStepValue : {e : Term 0} -> {v : Value e} ->
               BigStep _ e v -> Value e
bigStepValue {v = v} _ = v
               
-- End: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------

