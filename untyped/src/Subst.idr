
module Subst


import FinCmp
import Term


%default total


--------------------------------------------------------------
-- Begin: WEAKENING, I.E. ADDING UNUSED VARIABLES TO THE SCOPE

-- Abbreviate the name of the function 'weakenN'
-- from 'Data.Fin' (for better readability):
wkN : (n : Nat) -> Fin m -> Fin (m + n)
wkN = Data.Fin.weakenN

 
weakenContext : (m : Nat) -> (n : Nat) -> Term m -> Term (m + n)
weakenContext m n (TVar i)     = TVar (wkN n i)
weakenContext m n (TAbs x)     = TAbs (weakenContext (S m) n x)
weakenContext m n (TApp x y)   = TApp (weakenContext m n x)
                                      (weakenContext m n y)
weakenContext _ _ TZero         = TZero
weakenContext m n (TSucc x)     = TSucc (weakenContext m n x)
weakenContext m n (TPred x)     = TPred (weakenContext m n x)
weakenContext m n (TIfz x y z)  = TIfz (weakenContext m n x)
                                       (weakenContext m n y)
                                       (weakenContext m n z)

-- End: WEAKENING, I.E. ADDING UNUSED VARIABLES TO THE SCOPE
------------------------------------------------------------



    
-------------------------
-- Begin: TECHNICAL LEMMA

tightenBound :  {n : Nat} ->
                (j : Fin (S n)) -> (i : Fin (S n)) -> 
                j :<: i ->
                (j_ : Fin n ** (finToNat j_ = finToNat j))
--                
tightenBound             _         FZ      lt = absurd $ finNotLtZ lt
--
tightenBound {n = (S k)} FZ        (FS i') lt = (FZ ** Refl)
--
tightenBound {n = (S k)} (FS j') (FS i') lt = 
  let (j'_ ** eq') = tightenBound {n = k} j' i' (finLtPred lt)
  in (FS j'_ ** cong eq')

-- End: TECHNICAL LEMMA
-----------------------



------------------------------------------------------------------------------
-- Begin: SUBSTITUTION PRESERVES SCOPING OF EXPRESSIONS IN THE LAMBDA CALCULUS

subst_var : Term 0 ->           -- Term that is subtituted in.
            (i : Fin (S n)) ->  -- The i-th variable (Var i) is substituted for.
            (j : Fin (S n)) ->  -- Substitution takes place inside the term (Var j).
            Term n
-- An actual substitution occurs only if "i = j".
subst_var {n} ts i j = case finCmpDec i j of
  CmpEq eq => weakenContext 0 n ts
  CmpLt lt => case j of
                   FZ    => absurd $ finNotLtZ lt                   
                   FS j' => TVar j'
  CmpGt gt => case i of
                   FZ    => absurd $ finNotLtZ gt
                   FS i' => let (j_ ** _) = tightenBound j (FS i') gt
                            in TVar j_


export subst : Term 0 ->           -- Term that is substituted in.
               (i : Fin (S n)) ->  -- The i-th varibale (Var i) is substituted for.
               Term (S n) ->       -- Substitution takes place inside this term.
               Term n
--
-- The hard part is substitution in expressions that 
-- are variables, i.e. substitution in 'Var j'.
subst ts i (TVar j) = subst_var ts i j
--
-- Substitution in expressions that are not variables
-- is handled by recursing over (and substituting in)
-- subexpressions:
subst ts i (TAbs e)        = TAbs (subst ts (FS i) e)
subst ts i (TApp e1 e2)    = TApp (subst ts i e1) (subst ts i e2)
subst _  _ TZero           = TZero
subst ts i (TSucc e)       = TSucc (subst ts i e)
subst ts i (TPred e)       = TPred (subst ts i e)
subst ts i (TIfz e1 e2 e3) = TIfz (subst ts i e1) (subst ts i e2) (subst ts i e3)

-- End: SUBSTITUTION PRESERVES SCOPING OF EXPRESSIONS IN THE LAMBDA CALCULUS
----------------------------------------------------------------------------
