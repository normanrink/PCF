
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
--       ts : Term sctx s, and
--       tt : Term (insertAt i s ctx) t.
--     Then 'subst ts i tt' has type 't' in context '(ctx++sctx)'."
--
-- Note that 'subst ts i tt' is typically written as "tt[ts/(TVar i)]".
-- 
-- Note that the theorem that is expressed by the type signature
-- of 'subst' is usually referred to as 
--
--    *** the substitution lemma ***
--
-- and casually summarized as 
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


-- When adding variables in 'ctx' in the middle of
-- a context 'ctx1++ctx2', de Bruijn indices must
-- be adjusted accordingly:
shift : {ctx1 : Context n1} -> {ctx2 : Context n2} -> {i : Fin (n1+n2)} ->
        (ctx : Context n) -> index i (ctx1++ctx2) = t ->
        (i' : Fin (n1+(n+n2)) ** index i' (ctx1++(ctx++ctx2)) = t)        
shift {ctx1 = []}         {i}         []       eq = (i ** eq)
--
shift {ctx1 = []}         {i}         (c::ctx) eq = 
  let (i' ** eq') = shift {ctx1=[]} ctx eq
  in (FS i' ** eq')
shift {ctx1 = (_::ctx1')} {i = FZ}    ctx      eq = (FZ ** eq)
--
shift {ctx1 = (_::ctx1')} {i = FS i'} ctx      eq = 
  let (i' ** eq') = shift {ctx1=ctx1'} ctx eq
  in (FS i' ** eq')


shiftTerm : (ctx : Context n) -> Term (ctx1++ctx2) t ->
            Term (ctx1++(ctx++ctx2)) t            
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TVar i {prf}) = 
  let (i' ** prf') = shift {ctx1=ctx1} {ctx2=ctx2} ctx prf
  in TVar i' {prf=prf'}
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} {t = t1 :->: t2} ctx (TAbs e) =
  let e' = shiftTerm {ctx1=(t1::ctx1)} {ctx2=ctx2} ctx e
  in TAbs e'
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TApp e1 e2) =
  let e1' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e1
      e2' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e2
  in TApp e1' e2'
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TFix e) =
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TFix e'
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx TZero = TZero
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TSucc e) =
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TSucc e'
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TPred e) =
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TPred e'
--
shiftTerm {n = n} {ctx1 = ctx1} {ctx2 = ctx2} ctx (TIfz e1 e2 e3) =
  let e1' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e1
      e2' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e2
      e3' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e3
  in TIfz e1' e2' e3'

-- End: TECHNICAL LEMMATA ABOUT INDEXING INTO MODIFIED CONTEXTS
---------------------------------------------------------------



-----------------------------------------------------------------------------
-- Begin: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS

subst_var' : Term sctx s ->      -- Term of type 's' is subtituted in.
             (i : Fin (S n)) ->  -- The i-th variable (Var i) is substituted for.
             (j : Fin (S n)) ->  -- Substitution takes place inside the term (Var j).
             index j (insertAt i s ctx) = t ->
             Term (ctx++sctx) t
subst_var' {sctx} {ctx} {s} {t} ts i j prf = case finCmpDec i j of
--
-- An actual substitution occurs only if "i = j".
--
-- For "i /= j" no substitution occurs, but the proof 'prf'
-- in the returned expression 'TVar _ {prf}' has to be 
-- adjusted to account for the fact that the context has
-- been shortened from (insertAt s i ctx) to 'ctx'.
  CmpEq eq => let eq' = lookupInserted eq prf
                  ts' = shiftTerm {ctx1 = []} {ctx2 = sctx} ctx ts
              in rewrite eq' in ts'
  CmpLt lt => case j of
    FZ    => absurd $ finNotLtZ lt
    FS j' => let t' = TVar j' {ctx = ctx} {prf = shiftDown lt prf}
             in weakenContext ctx sctx t'
  CmpGt gt => case i of 
    FZ    => absurd $ finNotLtZ gt
    FS i' => let (j_ ** prf_) = tightenBound j gt prf
                 t' = TVar j_ {ctx = ctx} {prf = prf_}
             in weakenContext ctx sctx t'


export subst : Term sctx s ->                -- Term of type 's' is substituted in.
               (i : Fin (S n)) ->            -- The i-th varibale (Var i) is substituted for.
               Term (insertAt i s ctx) t ->  -- Substitution takes place inside this
                                             -- term of type 't'
               Term (ctx++sctx) t            -- The resulting term is again of type 't'.
--
-- The hard part is substitution in expressions that 
-- are variables, i.e. substitution in 'Var j'.
subst ts i (TVar j {prf}) = subst_var' ts i j prf
--
-- Substitution in expressions that are not variables
-- is handled by recursing over (and substituting in)
-- subexpressions:
--
subst {ctx} {t = t1:->:t2} ts i (TAbs e) = 
  TAbs $ subst {ctx=t1::ctx} ts (FS i) e
--
subst ts i (TApp e1 e2)    = TApp (subst ts i e1) (subst ts i e2)
subst ts i (TFix e)        = TFix (subst ts i e)
subst _  _ TZero           = TZero
subst ts i (TSucc e)       = TSucc (subst ts i e)
subst ts i (TPred e)       = TPred (subst ts i e)
subst ts i (TIfz e1 e2 e3) = TIfz (subst ts i e1) (subst ts i e2) (subst ts i e3)

-- End: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------------



------------------------------
-- Begin: STRUCTURAL RELATIONS
--
-- Terms always exist in a specific context. As a consequence, terms with different 
-- contexts cannot be equal. In fact, they cannot even be compared because the contexts
-- are part of the (Idris) type of a term and therefore comparing terms that exist in
-- different contexts means attempting to compare Idris expressions at different Idris types.
--
-- The following defines relations (data types suffixed with 'R') that hold between
-- structurally equal terms, even if the terms are typed in different contexts.
-- The main result this leads to is captured by the function 'ctxREq' which shows
-- that two terms that are structurally equal and typed in the same context are
-- in fact equal.


-- Finite numbers can be structurally equal even
-- if subject to different bounds 'm' and 'n':
data FinR : {m : Nat} -> {n : Nat} ->
            Fin m -> Fin n -> Type where
  FRZ : FinR (FZ {k=m}) (FZ {k=n})
  FRS : FinR i j -> FinR (FS i) (FS j)


-- The relation 'FinR' holds, for example, bewteen
-- a bounded number 'i' and a weakened version of 'i'
-- where the bound has been weakend with '0':
weakenZeroFinR : (i : Fin m) -> FinR {m=(m+0)} {n=m} (weakenN 0 i) i
weakenZeroFinR FZ      = FRZ
weakenZeroFinR (FS i') = FRS $ weakenZeroFinR i'

    
-- If 'FinR' holds between finite numbers that are subject
-- to the same bound 'n', then the numbers are equal:
finREq : (i : Fin n) -> (j : Fin n) -> FinR i j -> i = j
finREq FZ      FZ      FRZ      = Refl
finREq (FS i') (FS j') (FRS fr) = cong $ finREq i' j' fr


-- The relation 'TermCtxR' holds for terms that
-- are structurally equal even if typed in different
-- contexts 'ctx1' and 'ctx2':
data TermCtxR : {ctx1 : Context m} -> {ctx2: Context n} ->
                Term ctx1 t -> Term ctx2 t -> Type where
  TCRVar  : {prf1 : index i ctx1 = t} -> {prf2 : index j ctx2 = t} ->
            FinR i j -> 
            TermCtxR {ctx1=ctx1} {ctx2=ctx2} 
                     (TVar {ctx=ctx1} i {prf=prf1}) 
                     (TVar {ctx=ctx2} j {prf=prf2})
  --
  TCRAbs  : TermCtxR {ctx1=(t::ctx1')} {ctx2=(t::ctx2')} e e' ->
            TermCtxR {ctx1=ctx1'} {ctx2=ctx2'} (TAbs e) (TAbs e')
  --
  TCRApp  : TermCtxR e1 e1' -> TermCtxR e2 e2' ->
            TermCtxR (TApp e1 e2) (TApp e1' e2')
  --
  TCRFix  : TermCtxR e e' -> TermCtxR (TFix e) (TFix e')
  --
  TCRZero : TermCtxR TZero TZero
  --
  TCRSucc : TermCtxR e e' -> 
            TermCtxR (TSucc e) (TSucc e')
  --
  TCRPred : TermCtxR e e' -> TermCtxR (TPred e) (TPred e')
  --
  TCRIfz  : TermCtxR e1 e1' -> TermCtxR e2 e2' -> TermCtxR e3 e3' ->
            TermCtxR (TIfz e1 e2 e3) (TIfz e1' e2' e3')


-- Structural equality of terms 'e1' and 'e2' in the
-- same context 'ctx' implies equality 'e1 = e2:
ctxREq : (e1 : Term ctx t) -> (e2 : Term ctx t) -> TermCtxR e1 e2 -> e1 = e2
--
ctxREq {ctx} {t} (TVar i {prf=prf1}) (TVar j {prf=prf2}) (TCRVar fr) = 
  case finREq i j fr of
       Refl => case prf1 of
                    Refl => case prf2 of
                                 Refl => Refl
               -- By matching on the equality proofs 'prf1' and 'prf2' one
               -- effectively ends up using "uniqueness of identity proofs":
               -- Both proofs are matched to the same constructor 'Refl',
               -- and this causes Idris to refine the two arguments of 'ctxREq'
               -- to identical (Idris) expressions, i.e. 'TVar i {prf=Refl}'.
--
ctxREq (TAbs e) (TAbs e') (TCRAbs r) = cong $ ctxREq e e' r
--
ctxREq (TApp e1 e2) (TApp e1' e2') (TCRApp r1 r2) = 
  let eq1 = ctxREq e1 e1' r1
      eq2 = ctxREq e2 e2' r2
  in rewrite eq1 in rewrite eq2 in Refl
--
ctxREq (TFix e) (TFix e') (TCRFix r) = cong $ ctxREq e e' r
--
ctxREq TZero TZero TCRZero = Refl
--
ctxREq (TSucc e) (TSucc e') (TCRSucc r) = cong $ ctxREq e e' r
--
ctxREq (TPred e) (TPred e') (TCRPred r) = cong $ ctxREq e e' r
--
ctxREq (TIfz e1 e2 e3) (TIfz e1' e2' e3') (TCRIfz r1 r2 r3) =
  let eq1 = ctxREq e1 e1' r1
      eq2 = ctxREq e2 e2' r2
      eq3 = ctxREq e3 e3' r3
  in rewrite eq1 in rewrite eq2 in rewrite eq3 in Refl


-- Weakening the context 'ctx' of a term 'e' with the empty context '[]'
-- retains the term's structure, i.e. the relation 'TermCtxR' holds
-- between the original term and the weakend one:
weakenEmptyCtxR : (e : Term ctx t) -> 
                  TermCtxR {ctx1=(ctx++[])} {ctx2=ctx} (weakenContext ctx [] e) e
--
weakenEmptyCtxR {ctx} (TVar i {prf}) = TCRVar {ctx1=(ctx++[])} {ctx2=ctx} {prf2=prf}
                                              (weakenZeroFinR i)
--                                         
weakenEmptyCtxR (TAbs e)        = TCRAbs (weakenEmptyCtxR e)
weakenEmptyCtxR (TApp e1 e2)    = TCRApp (weakenEmptyCtxR e1) (weakenEmptyCtxR e2)
weakenEmptyCtxR (TFix e)        = TCRFix (weakenEmptyCtxR e)
weakenEmptyCtxR TZero           = TCRZero
weakenEmptyCtxR (TSucc e)       = TCRSucc (weakenEmptyCtxR e)
weakenEmptyCtxR (TPred e)       = TCRPred (weakenEmptyCtxR e)
weakenEmptyCtxR (TIfz e1 e2 e3) = TCRIfz (weakenEmptyCtxR e1)
                                         (weakenEmptyCtxR e2)
                                         (weakenEmptyCtxR e3)


-- Finally, the previous developments of structural equality can be
-- used to show that a term 'e' remains unchanged when its context
-- is weakend with the empty context '[]':
weakenEmptyWithEmpty : (e : Term [] t) -> weakenContext [] [] e = e
weakenEmptyWithEmpty e = let wCtxR = weakenEmptyCtxR e
                         in ctxREq (weakenContext [] [] e) e wCtxR


-- Define 'omega' to be the diverging term that
-- is the fix-point of the identity function:
public export omega : Term [] TyNat
omega = TFix (TAbs $ TVar FZ)


-- To show (later) that 'omega' diverges, one needs the result that
-- substituting 'omega' into a single variable 'TVar FZ' reproduces
-- the term 'omega' itself: 
export substOmega : subst {ctx=[]} {s=TyNat} {t=TyNat} Subst.omega FZ (TVar FZ) = Subst.omega
-- Note that while 'substOmega' is a special case of the more general
-- result 'substInVar' (see above), the general result is in fact not 
-- needed. This is because the Idris type checker can evaluate
-- 'weakenContext _ _ omega' (resulting from 'subst'), but it cannot
-- evaluate 'weakenContext _ _ e' for a variable 'e' because 'weakenContext'
-- is defined by recursion on the structure of 'e'.
substOmega = Refl

-- End: STRUCTURAL RELATIONS
----------------------------
