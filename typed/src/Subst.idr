
module Subst

-- This module constructs an expressively typed substitution
-- function 'subst' for substituting variables in the simply-typed
-- lambda calculus.
-- 
-- The key point is that the expressive type signature of the
-- function 'subst' can be read as the following theorem:
--
--    "Given a context 'ctx' and a variable with
--     de Bruijn index 'i'. Given further the terms
--       ts : Term [] s, and
--       tt : Term (insertAt i s ctx) t.
--     Then 'subst ts i tt' has type 't' in context 'ctx'."
--
-- Note that 'subst ts i tt' is typically written as "tt[ts/(TVar i)]".
-- 
-- Note that the theorem that is expressed by the type signature
-- of 'subst' is usually referred to as 
--
--    *** the substitution lemma ***
--
-- ans casually summarized as 
-- 
--    *** substitution preserves type ***.
--


import FinCmp
import Term


%default total


-------------------------------------------------------------
-- Begin: WEAKENING, I.E. ADDING UNUSED VARIABLES TO CONTEXTS

-- Abbreviate the name of the function 'weakenN'
-- from 'Data.Fin' (for better readability):
wkN : (n : Nat) -> Fin m -> Fin (m + n)
wkN = Data.Fin.weakenN

 
-- Note that we only require weakening of a context 'ctx'
-- by appending another context on the right only.
weakeningPreservesType : {ctx : Context m} -> {ctx' : Context n} -> 
                         {i : Fin m} ->
                         (index i ctx = t) -> 
                         (index (wkN n i) (ctx ++ ctx') = t)
weakeningPreservesType {ctx = (_::_)}   {i = FZ}      eq = eq
weakeningPreservesType {ctx = (_:: xs)} {i = (FS i')} eq =
  weakeningPreservesType {i = i'} eq


weakenContext : {m : Nat} -> (ctx : Context m) ->
                {n : Nat} -> (ctx' : Context n) -> 
                Term ctx t -> 
                Term (ctx ++ ctx') t
weakenContext ctx {n = n} ctx' (TVar i {prf = p}) = 
  TVar (wkN n i) {prf = weakeningPreservesType p}
--
weakenContext ctx ctx' (TAbs {s} e)    = TAbs (weakenContext (s::ctx) ctx' e)
weakenContext ctx ctx' (TApp e1 e2)    = TApp (weakenContext ctx ctx' e1)
                                              (weakenContext ctx ctx' e2)
weakenContext ctx ctx' (TFix e)        = TFix (weakenContext ctx ctx' e)
weakenContext _   _    TZero           = TZero
weakenContext ctx ctx' (TSucc e)       = TSucc (weakenContext ctx ctx' e)
weakenContext ctx ctx' (TPred e)       = TPred (weakenContext ctx ctx' e)
weakenContext ctx ctx' (TIfz e1 e2 e3) = TIfz (weakenContext ctx ctx' e1)
                                              (weakenContext ctx ctx' e2)
                                              (weakenContext ctx ctx' e3)

-- End: WEAKENING, I.E. ADDING UNUSED VARIABLES TO CONTEXTS
-----------------------------------------------------------



    
-----------------------------------------------------------------
-- Begin: TECHNICAL LEMMATA ABOUT INDEXING INTO MODIFIED CONTEXTS

-- Function 'lookupInserted' yields a proof of the following:
--
--     "Let ctx' = insertAt i s ctx, and let i = j.
--      If (index j ctx' = t), then t = s."
--  
lookupInserted : {ctx : Context n} -> {s : Ty} -> {t : Ty} ->
                 {i : Fin (S n)} -> {j : Fin (S n)} ->
                 i = j ->
                 index j (insertAt i s ctx) = t ->
                 t = s 
lookupInserted                {i = FZ}      {j = FZ}      _  prf = sym prf
lookupInserted {ctx} {s} {t}  {i = FZ}      {j = (FS j')} eq prf = 
  sym $ replace {P = \k => index k (insertAt FZ s ctx) = t} (sym eq) prf
--
lookupInserted {ctx} {s} {t}  {i = (FS i')} {j = FZ}      eq prf =
  sym $ replace {P = \k => index FZ (insertAt k s ctx) = t} eq prf
--  
lookupInserted {ctx = (_::_)} {i = (FS i')} {j = (FS j')} eq  prf =  
  lookupInserted (FSinjective eq) prf


-- Function 'shiftDown' yields a proof of the following:
--
--     "Let ctx' = insertAt i s ctx, and let i < (j+1).
--      If (index (j+1) ctx' = t), then (index j ctx = t)."
--
shiftDown : {ctx : Context n} -> {s : Ty} ->
            {i : Fin (S n)} -> {j : Fin n} ->
            i :<: (FS j) -> 
            index (FS j) (insertAt i s ctx) = t ->
            index j ctx = t
--         
shiftDown {i = FZ}     {j = _}      _  prf = prf
shiftDown {i = (FS _)} {j = FZ}     lt prf = 
  absurd $ finNotLtZ $ finLtPred lt
--
shiftDown {ctx = (_::xs)} {s} {i = (FS i')} {j = (FS j')} lt prf =
  shiftDown {ctx = xs} {s} {i = i'} {j = j'} (finLtPred lt) prf


-- Function 'indexZeroLemma' yields a proof of the following: 
--
--     "Let ctx a non-empty context, and let ctx' = insertAt t (i+1) ctx.
--      Then, (index 0 ctx') = (index 0 ctx)."
--
indexZeroLemma : {ctx : Context (S n)} -> 
                 (i : Fin (S n)) -> 
                 index FZ (insertAt (FS i) t ctx) = index FZ ctx
--
indexZeroLemma {ctx = (_::_)} _ = Refl


-- Function 'pushLemma' yields a proof of the following:
--
--    "Let ctx be a context, and let (index i ctx = t).
--     Then, index (i+1) (s::ctx) = t."
--
pushLemma : (s : Ty) -> 
            index i ctx = t -> 
            index (FS i) (s::ctx) = t
pushLemma _ eq = eq


-- Function 'tightenBound' yields a proof of the following:
--
--     "Let ctx be a context, and let ctx' = insertAt i s ctx.
--      If (j < i) and (index j ctx' = t), then index j ctx = t."
--
-- The function 'tightenBound' returns a dependent pair.
--
-- The first component of the pair is 'j_', which represents
-- the same value as the function argument 'j' (as natural
-- numbers); but note that the bound on the ordinal 'j_' has
-- been tightened (by using the assumption "j < i"):
--   "j_ : Fin n"  while  "j : Fin (S n)".
-- 
-- The second component of the dependent pair is a proof of
--   "index j_ ctx = t".
--
tightenBound :  {n : Nat} -> {ctx : Context n} -> 
                (j : Fin (S n)) -> {i : Fin (S n)} -> 
                j :<: i ->
                index j (insertAt i s ctx) = t ->
                (j_ : Fin n ** (index j_ ctx = t))
--                 
tightenBound                 _       {i = FZ}      lt _  =
  absurd $ finNotLtZ lt
--
tightenBound {n = (S n')}    FZ      {i = (FS i')} _  eq = 
  let izl = indexZeroLemma i'
      eq_ = trans (sym izl) eq
  in (FZ ** eq_)
--
tightenBound {ctx = (x::xs)} (FS j') {i = (FS i')} lt eq =
  let (j_ ** eq_) = tightenBound {ctx = xs} j' (finLtPred lt) eq
  in (FS j_ ** pushLemma x eq_)

-- End: TECHNICAL LEMMATA ABOUT INDEXING INTO MODIFIED CONTEXTS
---------------------------------------------------------------



-----------------------------------------------------------------------------
-- Begin: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS

subst_var : Term [] s ->        -- Term of type 's' is subtituted in.
            (i : Fin (S n)) ->  -- The i-th variable (Var i) is substituted for.
            (j : Fin (S n)) ->  -- Substitution takes place inside the term (Var j).
            index j (insertAt i s ctx) = t ->
            Term ctx t
--
-- An actual substitution occurs only if "i = j".
--
-- For "i /= j" no substitution occurs, but the proof 'prf'
-- in the returned expression 'TVar _ {prf}' has to be 
-- adjusted to account for the fact that the context has
-- been shortened from (insertAt s i ctx) to 'ctx'.
subst_var {ctx} {s} ts i j prf = case finCmpDec i j of
  CmpEq eq => let ts' = weakenContext [] ctx ts
              in rewrite (lookupInserted eq prf) in ts'
  CmpLt lt => case j of
    FZ    => absurd $ finNotLtZ lt                   
    FS j' => TVar j' {prf = shiftDown lt prf}
  CmpGt gt => case i of
    FZ    => absurd $ finNotLtZ gt
    FS i' => let (j_ ** prf_) = tightenBound j gt prf
             in TVar j_ {prf = prf_}


export subst : Term [] s ->                  -- Term of type 's' is substituted in.
               (i : Fin (S n)) ->            -- The i-th varibale (Var i) is substituted for.
               Term (insertAt i s ctx) t ->  -- Substitution takes place inside this
                                             -- term of type 't'
               Term ctx t                    -- The resulting term is again of type 't'.
--
-- The hard part is substitution in expressions that 
-- are variables, i.e. substitution in 'Var j'.
subst ts i (TVar j {prf}) = subst_var ts i j prf
--
-- Substitution in expressions that are not variables
-- is handled by recursing over (and substituting in)
-- subexpressions:
subst ts i (TAbs e)        = TAbs (subst ts (FS i) e)
subst ts i (TApp e1 e2)    = TApp (subst ts i e1) (subst ts i e2)
subst ts i (TFix e)        = TFix (subst ts i e)
subst _  _ TZero           = TZero
subst ts i (TSucc e)       = TSucc (subst ts i e)
subst ts i (TPred e)       = TPred (subst ts i e)
subst ts i (TIfz e1 e2 e3) = TIfz (subst ts i e1) (subst ts i e2) (subst ts i e3)

-- End: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------------
