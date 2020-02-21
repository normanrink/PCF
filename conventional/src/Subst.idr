
module Subst

-- This module constructs an expressively typed substitution
-- function 'subst' for substituting variables in the simply-typed
-- lambda calculus.
-- 
-- The key point is that the expressive type signature of the
-- function 'subst' can be read as the following theorem:
--
--    "Given a variable with de Bruijn index 'idx'.
--     Given further the terms
--       ts : Term sctx s, and
--       tt : Term ctx  t.
--     Then 'subst ts idx tt' has type 't' in context '(remove idx ctx)++sctx'."
--
-- Note that 'subst ts idx tt' is typically written as "tt[ts/(TVar idx)]".
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


import Term


%default total


------------------------------------------------------------
-- Begin: SHIFTING, I.E. ADDING UNUSED VARIABLES TO CONTEXTS

-- When adding variables in 'ctx' in the middle of
-- a context 'ctx1++ctx2', de Bruijn indices must
-- be adjusted accordingly:
shift : (ctx : Context) -> HasType (ctx1++ctx2) t ->
        HasType (ctx1++(ctx++ctx2)) t
shift {ctx1 = []}         []       x        = x
shift {ctx1 = []}         (_::ctx) x        = Next $ shift {ctx1=[]} ctx x
shift {ctx1 = (_::ctx1')} ctx      First    = First
shift {ctx1 = (_::ctx1')} ctx      (Next x) = Next $ shift {ctx1=ctx1'} ctx x


shift' : (ctx : Context) -> HasType (ctx1++ctx2) t -> 
         HasType ((ctx1++ctx)++ctx2) t
shift' {ctx1} {ctx2} ctx ht = let assoc = appendAssociative ctx1 ctx ctx2 
                                  sh    = shift {ctx1=ctx1} {ctx2=ctx2} ctx ht
                              in rewrite (sym assoc) in sh


-- Adjust terms for the (unused) variables in 'ctx':
shiftTerm : (ctx : Context) -> Term (ctx1++ctx2) t ->
            Term (ctx1++(ctx++ctx2)) t
--
shiftTerm ctx (TVar ht) = let sht = shift ctx ht
                          in TVar sht
--                          
shiftTerm {ctx1} {ctx2} {t = t1:->:t2} ctx (TAbs e) = 
  let e' = shiftTerm {ctx1=(t1::ctx1)} {ctx2=ctx2} ctx e
  in TAbs e'
--
shiftTerm {ctx1} {ctx2} ctx (TApp e1 e2) = 
  let e1' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e1
      e2' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e2
  in TApp e1' e2'
--
shiftTerm {ctx1} {ctx2} ctx (TFix e) = 
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TFix e'
--
shiftTerm ctx TZero = TZero
--
shiftTerm {ctx1} {ctx2} ctx (TSucc e) =
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TSucc e'
--
shiftTerm {ctx1} {ctx2} ctx (TPred e) =
  let e' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e
  in TPred e'
--
shiftTerm {ctx1} {ctx2} ctx (TIfz e1 e2 e3) =
  let e1' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e1
      e2' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e2
      e3' = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx e3
  in TIfz e1' e2' e3'


shiftTerm' : (ctx : Context) -> Term (ctx1++ctx2) t -> Term ((ctx1++ctx)++ctx2) t
shiftTerm' {ctx1} {ctx2} ctx ht = let assoc = appendAssociative ctx1 ctx ctx2 
                                      sh    = shiftTerm {ctx1=ctx1} {ctx2=ctx2} ctx ht
                                  in rewrite (sym assoc) in sh


-- Shifting a de Bruijn index 'x' with the empty
-- context '[]' preserves the de Bruijn index 'x':
shiftNil : {ctx1 : Context} -> {ctx2 : Context} ->
           {t : Ty} -> {x : HasType (ctx1++ctx2) t} ->
           shift [] x = x
shiftNil {ctx1 = []}      {ctx2 = ctx2} {x = x}        = Refl
shiftNil {ctx1 = _::ctx'} {ctx2 = ctx2} {x = First}    = Refl
shiftNil {ctx1 = _::ctx'} {ctx2 = ctx2} {x = (Next x)} = 
  let eq = shiftNil {ctx1=ctx'} {ctx2=ctx2} {x=x}
  in cong {f = \z => Next z} eq


-- Shifting a term 'e' with the empty
-- context '[]' preserves the term 'e':
shiftTermNil : {ctx1 : Context} -> {ctx2 : Context} ->
               {t : Ty} -> {e : Term (ctx1++ctx2) t} ->
               shiftTerm [] e = e
--               
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {t=t} {e = (TVar ht)} = 
  cong {f = \z => TVar z} $ shiftNil {ctx1=ctx1} {ctx2=ctx2} {t=t} {x=ht}
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {t=t1:->:t2} {e = (TAbs e')} = 
  let eq = shiftTermNil {ctx1=(t1::ctx1)} {ctx2=ctx2} {t=t2} {e=e'}
  in cong {f = \z => TAbs z} eq
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = (TApp e1 e2)} = 
  let eq1 = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e1}
      eq2 = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e2}
      c   = cong {f = \z => TApp z e2} eq1
      c'  = cong {f = \z => TApp (shiftTerm [] e1) z} eq2
  in trans c' c
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = (TFix e')} = 
  let eq = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e'}
  in cong {f = \z => TFix z} eq
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = TZero} = Refl
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = (TSucc e')} =
  let eq = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e'}
  in cong {f = \z => TSucc z} eq
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = (TPred e')} =
  let eq = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e'}
  in cong {f = \z => TPred z} eq
--
shiftTermNil {ctx1 = ctx1} {ctx2 = ctx2} {e = (TIfz e1 e2 e3)} =
  let eq1 = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e1}
      eq2 = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e2}
      eq3 = shiftTermNil {ctx1=ctx1} {ctx2=ctx2} {e=e3}
      c   = cong {f = \z => TIfz z e2 e3} eq1
      c'  = cong {f = \z => TIfz (shiftTerm [] e1) z e3} eq2
      c'' = cong {f = \z => TIfz (shiftTerm [] e1) (shiftTerm [] e2) z} eq3
  in trans (trans c'' c') c

-- End: SHIFTING, I.E. ADDING UNUSED VARIABLES TO CONTEXTS
----------------------------------------------------------



-----------------------------------------------------------------------------
-- Begin: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS

subst_var : Term sctx s ->            -- Term of type 's' is subtituted in.
            (idx : HasType ctx s) ->  -- Index of the variable in 'ctx' that is subsituted for.
                                      -- (and hence must have type 's').
            HasType ctx t ->          -- Substitution takes place inside the variable
                                      -- with this index.
            Term ((remove ctx idx)++sctx) t
--            
subst_var {sctx} {s=s} {ctx=s::ctx'} {t=s} ts First First = 
  shiftTerm' {ctx1=[]} {ctx2=sctx} ctx' ts
--
subst_var {sctx} {s=s} {ctx=s::ctx'} {t=t} ts First (Next htv) = 
  let anr1 = sym $ appendNilRightNeutral ctx' 
      htv1 = replace {P = \z => HasType z t} anr1 htv
      htv2 = shift {ctx1=ctx'} {ctx2=[]} sctx htv1
      anr2 = appendNilRightNeutral sctx
      htv3 = replace {P = \z => HasType (ctx'++z) t} anr2 htv2
   in TVar htv3
--
subst_var {sctx} {s=s} {ctx=u::ctx'} {t=u} ts (Next _) First = TVar First
--
subst_var {sctx} {s=s} {ctx=u::ctx'} {t=t} ts (Next x) (Next y) = 
  let t' = subst_var ts x y
  in shiftTerm {ctx1=[]} {ctx2=(remove ctx' x)++sctx} [u] t'


export subst : Term sctx s ->            -- Term of type 's' is substituted in.
               (idx : HasType ctx s) ->  -- Index of the variable in 'ctx' that is substituted for
                                         -- (and hence must have type 's').
               Term ctx t  ->            -- Substitution takes place inside this
                                         -- term of type 't'
               Term ((remove ctx idx)++sctx) t
--          
subst ts ht (TVar htv) = subst_var ts ht htv
--
subst {ctx} {t = t1:->:t2} ts ht (TAbs e) = 
  TAbs $ subst {ctx=t1::ctx} ts (Next ht) e
--
subst ts ht (TApp e1 e2)    = TApp (subst ts ht e1) (subst ts ht e2) 
subst ts ht (TFix e)        = TFix (subst ts ht e)
subst ts ht TZero           = TZero
subst ts ht (TSucc e)       = TSucc (subst ts ht e)
subst ts ht (TPred e)       = TPred (subst ts ht e)
subst ts ht (TIfz e1 e2 e3) = TIfz (subst ts ht e1)
                                   (subst ts ht e2)
                                   (subst ts ht e3)


-- Substituting a term 'e' into a single variable 'TVar First'
-- gives back the same term 'e' but in a shifted context:
substInVar' : (e : Term sctx t) -> 
             subst {ctx=(t::ctx')} {s=t} {t=t} e First (TVar First) = shiftTerm {ctx1=[]} {ctx2=sctx} ctx' e    
substInVar' e = Refl


-- Specialization of the previous result to a minimal
-- context '[t]' gives back exactly term 'e':
substInVar : (e : Term sctx t) -> 
             subst {ctx=[t]} {s=t} {t=t} e First (TVar First) = e    
substInVar {sctx} e = shiftTermNil {ctx1=[]} {ctx2=sctx} {e=e}

-- End: SUBSTITUTION PRESERVES TYPING OF EXPRESSIONS IN THE LAMBDA CALCULUS
---------------------------------------------------------------------------



--------------------------------
-- Begin: DIVERGING TERM 'omega'

-- Define 'omega' to be the diverging term that
-- is the fix-point of the identity function:
public export omega : Term [] TyNat
omega = TFix (TAbs $ TVar First)
 
 
-- To show (later) that 'omega' diverges, one needs the result that
-- substituting 'omega' into a single variable 'TVar FZ' reproduces
-- the term 'omega' itself: 
export substOmega : subst {ctx=[TyNat]} {s=TyNat} {t=TyNat} Subst.omega First (TVar First) = Subst.omega
-- Note that while 'substOmega' is a special case of the more general
-- result 'substInVar' (see above), the general result is in fact not 
-- needed. This is because the Idris type checker can evaluate
-- 'shiftTerm _ omega' (resulting from 'subst'), but it cannot
-- evaluate 'shiftTerm _ e' for a variable 'e' because 'shiftTerm'
-- is defined by recursion on the structure of 'e'.
substOmega = Refl

-- End: DIVERGING TERM 'omega'
------------------------------
