
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
-- Since big-step semantics fully evaluates terms to values, the
-- type constructor 'BigStep' requires as its third argument
-- evidence that 'y' is indeed a value.
data BigStep : Term [] t -> (y: Term [] t) -> Value y -> Type where
  BStValue    : (v : Value e) -> BigStep e e v
  --
  BStApp      : BigStep e1 (TAbs e1') _ ->
                BigStep e2 e2' _ ->
                BigStep (subst e2' FZ e1') e v ->
                BigStep (TApp e1 e2) e v
  --
  BStRecZero  : BigStep e TZero _ ->
                BigStep e0 e0' v0 ->
                BigStep (TRec e e0 e1) e0' v0
  --
  BStRecSucc  : BigStep e (TSucc n) v ->
                BigStep (subst n FZ (subst (TRec n e0 e1) FZ e1)) e1' v1 ->
                BigStep (TRec e e0 e1) e1' v1
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


bigStepFst : {e : Term [] t} -> BigStep e _ _ -> Term [] t
bigStepFst {e = e} _ = e


bigStepSnd : {e : Term [] t} -> BigStep _ e _ -> Term [] t
bigStepSnd {e = e} _ = e


bigStepValue : {e : Term [] t} -> {v : Value e} ->
               BigStep _ e v -> Value e
bigStepValue {v = v} _ = v
               
-- End: BIG-STEP EVALUATION RELATION FOR TERMS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------

