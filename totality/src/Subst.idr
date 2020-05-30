
module Subst

-- Substitution inside untyped lambda calculus terms.


import Term


%default total
%access public export



shift : (cutoff : Nat) -> (distance : Nat) ->
        Nat -> Nat
shift Z     distance k     = distance+k
shift (S c) distance Z     = Z
shift (S c) distance (S k) = S $ shift c distance k

            

shiftTerm : (cutoff : Nat) -> (distance : Nat) ->
            Term -> Term            
--
shiftTerm c d (TVar i) = TVar (shift c d i) 
--
shiftTerm c d (TAbs e) = TAbs $ shiftTerm (S c) d e
--
shiftTerm c d (TApp e1 e2) =
  let e1' = shiftTerm c d e1
      e2' = shiftTerm c d e2
  in TApp e1' e2'
--
shiftTerm c d (TRec e1 e2 e3) = 
  let e1' = shiftTerm c d e1
      e2' = shiftTerm c d e2
      e3' = shiftTerm c d e3
  in TRec e1' e2' e3'
--
shiftTerm c d TZero = TZero
--
shiftTerm c d (TSucc e) = TSucc $ shiftTerm c d e
--
shiftTerm c d (TPred e) = TPred $ shiftTerm c d e
--
shiftTerm c d (TIfz e1 e2 e3) = 
  let e1' = shiftTerm c d e1
      e2' = shiftTerm c d e2
      e3' = shiftTerm c d e3
  in TIfz e1' e2' e3'

  
  
subst_var : Term ->       -- Term that is subtituted in.
            (i : Nat) ->  -- The i-th variable (Var i) is substituted for.
            (j : Nat) ->  -- Substitution takes place inside the term (Var j).
            Term
subst_var ts Z     Z     = ts
subst_var ts Z     (S j) = TVar j
subst_var ts (S i) Z     = TVar Z
subst_var ts (S i) (S j) = shiftTerm Z (S Z) $ subst_var ts i j



subst : Term ->       -- Term that is substituted in.
        (i : Nat) ->  -- The i-th varibale (Var i) is substituted for.
        Term ->       -- Substitution takes place inside this term.
        Term
subst ts i (TVar j)        = subst_var ts i j
subst ts i (TAbs e)        = TAbs $ subst ts (S i) e
subst ts i (TApp e1 e2)    = TApp (subst ts i e1)
                                  (subst ts i e2)
subst ts i (TRec e1 e2 e3) = TRec (subst ts i e1)
                                  (subst ts i e2)
                                  (subst ts i e3)
subst _  _ TZero           = TZero
subst ts i (TSucc e)       = TSucc (subst ts i e)
subst ts i (TPred e)       = TPred (subst ts i e)
subst ts i (TIfz e1 e2 e3) = TIfz (subst ts i e1)
                                  (subst ts i e2)
                                  (subst ts i e3)

