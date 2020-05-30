
module SubstLemmas

-- Lemmas about substitution (and the related
-- operations 'shiftTerm' and 'shift').


import Subst
import Term
import Typing


%default total
%access export



---------------------------------------
-- Begin: SUBSTITUTION PRESERVES TYPING

-- Lemmas about extending contexts (in the middle)
-- are required for the proof of the fact that
-- substitution preserves typing.
-- (In fact, the proof of preservation of typing under
-- substitution only requires a lemma about extending
-- the context at the front. However, to prove this
-- lemma about extending the context, one has to assume
-- that the context is extended in the middle in order
-- for induction to go through in the case of 'TAbs'.)


-- Extending a context 'ctx1++ctx2' in the middle preserves
-- the types that are in the context, but the index 'k' must
-- be shifted appropriately in order to retrieve the same
-- type from the extended context:
shiftTy : (k : Nat) ->
          index' k (ctx1++ctx2) = Just t -> 
          (ctx : Context) ->
          index' (shift (length ctx1) (length ctx) k) (ctx1++ctx++ctx2) = Just t
shiftTy {ctx1 = []}       k     prf  []       = prf
shiftTy {ctx1 = []}       k     prf  (s::ctx) = shiftTy {ctx1=[]} k prf ctx
shiftTy {ctx1 = t1::ctx1} Z     Refl ctx      = Refl
shiftTy {ctx1 = t1::ctx1} (S k) prf  ctx      = shiftTy {ctx1=ctx1} k prf ctx



-- Typing is preserved if a context 'ctx1++ctx2' is extended
-- in the middle provided the term 'e' is shifted appropriately:
shiftTermTy : (e : Term) ->
              Typing (ctx1++ctx2) e t -> 
              (ctx : Context) ->
              Typing (ctx1++ctx++ctx2) (shiftTerm (length ctx1) (length ctx) e) t
--
shiftTermTy (TVar i) (TyVar prf) ctx = 
  TyVar $ shiftTy i prf ctx
--
shiftTermTy (TAbs e) (TyAbs s ty) ctx {ctx1} = 
  TyAbs s $ shiftTermTy e ty ctx {ctx1=s::ctx1}
--
shiftTermTy (TApp e1 e2) (TyApp ty1 ty2) ctx = 
  TyApp (shiftTermTy e1 ty1 ctx)
        (shiftTermTy e2 ty2 ctx)
--
shiftTermTy (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) ctx =
  TyRec (shiftTermTy e1 ty1 ctx)
        (shiftTermTy e2 ty2 ctx)
        (shiftTermTy e3 ty3 ctx)
--
shiftTermTy TZero TyZero ctx = TyZero
--
shiftTermTy (TSucc e) (TySucc ty) ctx = 
  TySucc $ shiftTermTy e ty ctx
--  
shiftTermTy (TPred e) (TyPred ty) ctx = 
  TyPred $ shiftTermTy e ty ctx
--
shiftTermTy (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) ctx =
  TyIfz (shiftTermTy e1 ty1 ctx)
        (shiftTermTy e2 ty2 ctx)
        (shiftTermTy e3 ty3 ctx)



-- Finally, substitution preserves typing:
substPreservesTy : (e : Term) ->   -- Term in which substitution takes place.
                   Typing (ctx1++s::ctx2) e t -> 
                   (es : Term) ->  -- Term that is substituted in.
                   Typing ctx2 es s ->
                   Typing (ctx1++ctx2) (subst es (length ctx1) e) t
--
substPreservesTy {ctx1 = []}       (TVar Z)     (TyVar Refl) es esTy = esTy
substPreservesTy {ctx1 = []}       (TVar (S i)) (TyVar prf)  es esTy = TyVar prf
substPreservesTy {ctx1 = t1::ctx1} (TVar Z)     (TyVar prf)  es esTy = TyVar prf
substPreservesTy {ctx1 = t1::ctx1} (TVar (S k)) (TyVar prf)  es esTy = 
  let ih = substPreservesTy {ctx1=ctx1} (TVar k) (TyVar prf) es esTy
  in shiftTermTy _ ih [t1] {ctx1=[]}
--
substPreservesTy {ctx1} (TAbs e) (TyAbs s ty) es esTy = 
  TyAbs s $ substPreservesTy e ty es esTy {ctx1=s::ctx1} 
--
substPreservesTy (TApp e1 e2) (TyApp ty1 ty2) es esTy = 
  TyApp (substPreservesTy e1 ty1 es esTy)
        (substPreservesTy e2 ty2 es esTy)
--
substPreservesTy (TRec e1 e2 e3) (TyRec ty1 ty2 ty3) es esTy =
  TyRec (substPreservesTy e1 ty1 es esTy)
        (substPreservesTy e2 ty2 es esTy)
        (substPreservesTy e3 ty3 es esTy)        
--
substPreservesTy TZero TyZero es esTy = TyZero
--
substPreservesTy (TSucc e) (TySucc ty) es esTy =
  TySucc $ substPreservesTy e ty es esTy
--  
substPreservesTy (TPred e) (TyPred ty) es esTy = 
  TyPred $ substPreservesTy e ty es esTy
--
substPreservesTy (TIfz e1 e2 e3) (TyIfz ty1 ty2 ty3) es esTy =
  TyIfz (substPreservesTy e1 ty1 es esTy)
        (substPreservesTy e2 ty2 es esTy)
        (substPreservesTy e3 ty3 es esTy)

-- End: SUBSTITUTION PRESERVES TYPING
-------------------------------------




---------------------------------------
-- Begin: SEVERAL LEMMAS ABOUT SHIFTING

-- The following lemmas come in pairs: 
-- The really useful lemma in each pair
-- is the one about 'shiftTerm'.
-- However, the lemma in each pair that
-- is non-trivial to prove is usually the
-- other one, i.e. the one about 'shift'.


shiftByZero : (c : Nat) ->
              (k : Nat) ->
              shift c Z k = k
shiftByZero Z     k     = Refl
shiftByZero (S c) Z     = Refl
shiftByZero (S c) (S k) = cong $ shiftByZero c k


shiftTermByZero : (c : Nat) ->
                  (e : Term) ->
                  shiftTerm c Z e = e
shiftTermByZero c (TVar i) = congVar $ shiftByZero c i
shiftTermByZero c (TAbs e) = congAbs $ shiftTermByZero (S c) e
shiftTermByZero c (TApp e1 e2) = 
  congApp (shiftTermByZero c e1)
          (shiftTermByZero c e2)
shiftTermByZero c (TRec e1 e2 e3) = 
  congRec (shiftTermByZero c e1)
          (shiftTermByZero c e2)
          (shiftTermByZero c e3)
shiftTermByZero c TZero = congZero
shiftTermByZero c (TSucc e) = congSucc $ shiftTermByZero c e
shiftTermByZero c (TPred e) = congPred $ shiftTermByZero c e
shiftTermByZero c (TIfz e1 e2 e3) =
  congIfz (shiftTermByZero c e1)
          (shiftTermByZero c e2)
          (shiftTermByZero c e3)



shiftTwice : (c : Nat) ->
             (d1 : Nat) -> (d2 : Nat) ->
             (k : Nat) ->
             shift c d2 (shift c d1 k) = shift c (d2+d1) k
shiftTwice Z     d1 d2 k     = plusAssociative d2 d1 k
shiftTwice (S c) d1 d2 Z     = Refl
shiftTwice (S c) d1 d2 (S k) = cong $ shiftTwice c d1 d2 k


shiftTermTwice : (c : Nat) ->
                 (d1 : Nat) -> (d2 : Nat) ->
                 (e : Term) ->
                 shiftTerm c d2 (shiftTerm c d1 e) = shiftTerm c (d2+d1) e
shiftTermTwice c d1 d2 (TVar i) = congVar $ shiftTwice c d1 d2 i
shiftTermTwice c d1 d2 (TAbs e) = congAbs $ shiftTermTwice (S c) d1 d2 e
shiftTermTwice c d1 d2 (TApp e1 e2) = 
  congApp (shiftTermTwice c d1 d2 e1)
          (shiftTermTwice c d1 d2 e2)
shiftTermTwice c d1 d2 (TRec e1 e2 e3) =
  congRec (shiftTermTwice c d1 d2 e1)
          (shiftTermTwice c d1 d2 e2)
          (shiftTermTwice c d1 d2 e3)
shiftTermTwice c d1 d2 TZero = congZero
shiftTermTwice c d1 d2 (TSucc e) = congSucc $ shiftTermTwice c d1 d2 e
shiftTermTwice c d1 d2 (TPred e) = congPred $ shiftTermTwice c d1 d2 e
shiftTermTwice c d1 d2 (TIfz e1 e2 e3) = 
  congIfz (shiftTermTwice c d1 d2 e1)
          (shiftTermTwice c d1 d2 e2)
          (shiftTermTwice c d1 d2 e3)


shiftTermTwice' : (c : Nat) ->
                  (d1 : Nat) -> (d2 : Nat) ->
                  (e : Term) ->
                  shiftTerm c d2 (shiftTerm c d1 e) = shiftTerm c d1 (shiftTerm c d2 e)
shiftTermTwice' c d1 d2 e = 
  let eq1  = shiftTermTwice c d1 d2 e
      comm = cong {f = \q => shiftTerm c q e} $ plusCommutative d1 d2 
      eq1' = trans eq1 (sym comm)
      eq2  = shiftTermTwice c d2 d1 e
  in trans eq1' (sym eq2)



shiftSwap :  (c1 : Nat) -> (d1 : Nat) ->
             (c2 : Nat) -> (d2 : Nat) ->
             (k : Nat) ->
             shift (c1+d1+c2) d2 (shift c1 d1 k) = shift c1 d1 (shift (c1+c2) d2 k)
shiftSwap Z      Z      c2 d2 k     = Refl
shiftSwap Z      (S d1) c2 d2 k     = cong $ shiftSwap Z d1 c2 d2 k
shiftSwap (S c1) d1     c2 d2 Z     = Refl
shiftSwap (S c1) d1     c2 d2 (S k) = cong $ shiftSwap c1 d1 c2 d2 k


shiftTermSwap : (c1 : Nat) -> (d1 : Nat) ->
                (c2 : Nat) -> (d2 : Nat) ->                
                (e : Term) ->
                shiftTerm (c1+d1+c2) d2 (shiftTerm c1 d1 e) = 
                  shiftTerm c1 d1 (shiftTerm (c1+c2) d2 e)
shiftTermSwap c1 d1 c2 d2 (TVar i) = congVar $ shiftSwap c1 d1 c2 d2 i
shiftTermSwap c1 d1 c2 d2 (TAbs e) = congAbs $ shiftTermSwap (S c1) d1 c2 d2 e
shiftTermSwap c1 d1 c2 d2 (TApp e1 e2) = 
  congApp (shiftTermSwap c1 d1 c2 d2 e1)
          (shiftTermSwap c1 d1 c2 d2 e2)
shiftTermSwap c1 d1 c2 d2 (TRec e1 e2 e3) =
  congRec (shiftTermSwap c1 d1 c2 d2 e1)
          (shiftTermSwap c1 d1 c2 d2 e2)
          (shiftTermSwap c1 d1 c2 d2 e3)
shiftTermSwap c1 d1 c2 d2 TZero = congZero
shiftTermSwap c1 d1 c2 d2 (TSucc e) = congSucc $ shiftTermSwap c1 d1 c2 d2 e
shiftTermSwap c1 d1 c2 d2 (TPred e) = congPred $ shiftTermSwap c1 d1 c2 d2 e
shiftTermSwap c1 d1 c2 d2 (TIfz e1 e2 e3) =
  congIfz (shiftTermSwap c1 d1 c2 d2 e1)
          (shiftTermSwap c1 d1 c2 d2 e2)
          (shiftTermSwap c1 d1 c2 d2 e3)



-- Shifting acts as the identity if the
-- cutoff is set past the typing context:
shiftPastCtx : (k : Nat) -> 
               (ctx : Context) ->
               index' k ctx = Just t ->
               (n : Nat) -> (d : Nat) ->
               shift (length ctx + n) d k = k
shiftPastCtx Z     []       Refl _ _ impossible
shiftPastCtx (S _) []       Refl _ _ impossible
shiftPastCtx Z     (s::ctx) prf  n d = Refl
shiftPastCtx (S k) (s::ctx) prf  n d = 
  cong $ shiftPastCtx k ctx prf n d


shiftTermPastCtx : (e : Term) ->
                   (ctx : Context) -> 
                   Typing ctx e t ->
                   (n : Nat) -> (d : Nat) ->
                   shiftTerm (length ctx + n) d e = e
shiftTermPastCtx (TVar i) ctx (TyVar prf) n d = congVar $ shiftPastCtx i ctx prf n d
shiftTermPastCtx (TAbs e) ctx (TyAbs s ty) n d = congAbs $ shiftTermPastCtx e (s::ctx) ty n d
shiftTermPastCtx (TApp e1 e2) ctx (TyApp ty1 ty2) n d = 
  congApp (shiftTermPastCtx e1 ctx ty1 n d)
          (shiftTermPastCtx e2 ctx ty2 n d)
shiftTermPastCtx (TRec e1 e2 e3) ctx (TyRec ty1 ty2 ty3) n d =
  congRec (shiftTermPastCtx e1 ctx ty1 n d)
          (shiftTermPastCtx e2 ctx ty2 n d)
          (shiftTermPastCtx e3 ctx ty3 n d)          
shiftTermPastCtx TZero ctx TyZero n d = congZero
shiftTermPastCtx (TSucc e) ctx (TySucc ty) n d = congSucc $ shiftTermPastCtx e ctx ty n d
shiftTermPastCtx (TPred e) ctx (TyPred ty) n d = congPred $ shiftTermPastCtx e ctx ty n d
shiftTermPastCtx (TIfz e1 e2 e3) ctx (TyIfz ty1 ty2 ty3) n d = 
  congIfz (shiftTermPastCtx e1 ctx ty1 n d)
          (shiftTermPastCtx e2 ctx ty2 n d)
          (shiftTermPastCtx e3 ctx ty3 n d)          

-- End: SEVERAL LEMMAS ABOUT SHIFTING
-------------------------------------




-------------------------------------------
-- Begin: SHIFTING AND SUBSTITUTION COMMUTE

-- The following lemma is a convoluted way of
-- expressing 'k < length ctx'; it is used to
-- address the 'TVar' case in the subsequent
-- lemma.
substVarPastCtx : (k : Nat) -> 
                  (ctx : Context) ->
                  index' k ctx = Just t ->
                  subst_var x (length ctx + n) k = TVar k
substVarPastCtx Z     []       Refl impossible
substVarPastCtx (S _) []       Refl impossible
substVarPastCtx Z     (s::ctx) prf  = Refl
substVarPastCtx (S k) (s::ctx) prf  =
  let ih = substVarPastCtx k ctx prf
  in cong {f = \q => shiftTerm 0 1 q} ih


-- Subsituting at a de Bruijn index past the
-- context 'ctx' in which an expression 'e'
-- is typed yields 'e':
substPastCtx : (e : Term) -> 
               (ctx : Context) ->
               Typing ctx e t ->
               subst x (length ctx + n) e = e
substPastCtx (TVar i) ctx (TyVar prf) = substVarPastCtx i ctx prf
substPastCtx (TAbs e) ctx (TyAbs s ty) = congAbs $ substPastCtx e (s::ctx) ty
substPastCtx (TApp e1 e2) ctx (TyApp ty1 ty2) = 
  congApp (substPastCtx e1 ctx ty1)
          (substPastCtx e2 ctx ty2)
substPastCtx (TRec e1 e2 e3) ctx (TyRec ty1 ty2 ty3) = 
  congRec (substPastCtx e1 ctx ty1)
          (substPastCtx e2 ctx ty2)
          (substPastCtx e3 ctx ty3)
substPastCtx TZero ctx TyZero = congZero
substPastCtx (TSucc e) ctx (TySucc ty) = congSucc $ substPastCtx e ctx ty
substPastCtx (TPred e) ctx (TyPred ty) = congPred $ substPastCtx e ctx ty
substPastCtx (TIfz e1 e2 e3) ctx (TyIfz ty1 ty2 ty3) = 
  congIfz (substPastCtx e1 ctx ty1)
          (substPastCtx e2 ctx ty2)
          (substPastCtx e3 ctx ty3)


-- A less convoluted way of stating the lemma
-- that is used in the 'TVar' case above:
substVarPastCtx' : (k : Nat) ->
                   subst_var x (S k + n) k = TVar k
substVarPastCtx' Z     = Refl
substVarPastCtx' (S k) = let ih = substVarPastCtx' k
                         in cong {f = \q => shiftTerm 0 1 q} ih



-- Shifting and substituting for a variable commute:
shiftSubstVarComm : (c : Nat) -> (d : Nat) ->  (i : Nat) -> 
                    (x : Term) ->
                    (k : Nat) ->
                    shiftTerm c d (subst_var x (c+i) k) = subst_var x (c+d+i) (shift c d k)
--
shiftSubstVarComm Z     Z     i x k = shiftTermByZero Z (subst_var x i k)
--
shiftSubstVarComm Z     (S d) i x k = 
  let ih  = shiftSubstVarComm Z d i x k
      ih' = cong {f = \q => shiftTerm Z (S Z) q} ih
      eq  = shiftTermTwice Z d (S Z) (subst_var x i k)
  in trans (sym eq) ih' 
--
shiftSubstVarComm (S c)  d    i x Z     = Refl
--
shiftSubstVarComm (S c)  d    i x (S k) = 
  let ih  = shiftSubstVarComm c d i x k
      ih' = cong {f = \q => shiftTerm Z (S Z) q} ih
      eq  = shiftTermSwap Z (S Z) c d (subst_var x (c+i) k)
  in trans eq ih'


-- Shifting and substituting in a general term 'e' commute:
shiftTermSubstComm : (c : Nat) -> (d : Nat) -> (i : Nat) -> 
                     (x : Term) ->
                     (e : Term) ->
                     shiftTerm c d (subst x (c+i) e) = subst x (c+d+i) (shiftTerm c d e)
--
shiftTermSubstComm c d i x (TVar k) = shiftSubstVarComm c d i x k
shiftTermSubstComm c d i x (TAbs e) = congAbs $ shiftTermSubstComm (S c) d i x e
shiftTermSubstComm c d i x (TApp e1 e2) = 
  congApp (shiftTermSubstComm c d i x e1)
          (shiftTermSubstComm c d i x e2)
shiftTermSubstComm c d i x (TRec e1 e2 e3) = 
  congRec (shiftTermSubstComm c d i x e1)
          (shiftTermSubstComm c d i x e2)
          (shiftTermSubstComm c d i x e3)  
shiftTermSubstComm c d i x TZero = congZero
shiftTermSubstComm c d i x (TSucc e) = congSucc $ shiftTermSubstComm c d i x e
shiftTermSubstComm c d i x (TPred e) = congPred $ shiftTermSubstComm c d i x e
shiftTermSubstComm c d i x (TIfz e1 e2 e3) = 
  congIfz (shiftTermSubstComm c d i x e1)
          (shiftTermSubstComm c d i x e2)
          (shiftTermSubstComm c d i x e3)  

-- End: SHIFTING AND SUBSTITUTION COMMUTE
-----------------------------------------




-----------------------------------
-- Begin: SWAPPING OF SUBSTITUTIONS

-- Substitution in a shifted variable, below the 
-- cutoff 'c' of the 'shift' operation, preserves
-- the variable (modulo shifting):
substVarBelowShift : (c : Nat) -> (n : Nat) ->
                     (k : Nat) ->
                     (x : Term) ->
                     subst_var x c (shift c (S n) k) = TVar (shift c n k)
substVarBelowShift Z     n k     x = Refl
substVarBelowShift (S c) n Z     x = Refl
substVarBelowShift (S c) n (S k) x = 
  let ih  = substVarBelowShift c n k x
  in cong {f = shiftTerm Z (S Z)} ih


-- Substitution in a shifted term, below the 
-- cutoff 'c' of the 'shift' operation, preserves
-- the term (modulo shifting):
substBelowShiftTerm : (c : Nat) -> (n : Nat) ->
                      (e : Term) ->
                      (x : Term) ->
                      subst x c (shiftTerm c (S n) e) = shiftTerm c n e
substBelowShiftTerm c n (TVar i) x = substVarBelowShift c n i x
substBelowShiftTerm c n (TAbs e) x = congAbs $ substBelowShiftTerm (S c) n e x
substBelowShiftTerm c n (TApp e1 e2) x = 
  congApp (substBelowShiftTerm c n e1 x) 
          (substBelowShiftTerm c n e2 x)
substBelowShiftTerm c n (TRec e1 e2 e3) x = 
  congRec (substBelowShiftTerm c n e1 x)
          (substBelowShiftTerm c n e2 x)
          (substBelowShiftTerm c n e3 x)
substBelowShiftTerm c n TZero x = Refl
substBelowShiftTerm c n (TSucc e) x = cong $ substBelowShiftTerm c n e x
substBelowShiftTerm c n (TPred e) x = cong $ substBelowShiftTerm c n e x
substBelowShiftTerm c n (TIfz e1 e2 e3) x = 
  congIfz (substBelowShiftTerm c n e1 x)
          (substBelowShiftTerm c n e2 x)
          (substBelowShiftTerm c n e3 x)




-- Swapping substitutions in the variable with
-- de Bruijn index 'k' does not affect the result:
-- (Note that the typing for 'x' in the empty context
-- ensures that there are no free variables in 'x',
-- which could otherwise be affected by the second
-- substitution of 'y' on the left-hand side of the
-- equation in the conclusion of the lemma.)
substVarSwap : (k : Nat) -> 
               (i : Nat) ->
               (x : Term) -> (y : Term) ->
               (Typing [] x t) ->
               subst y i (subst_var x i k) = subst x i (subst_var y (S i) k)
--
substVarSwap Z     Z     x y tyx = substPastCtx x _ tyx {n=0}
--
substVarSwap Z     (S i) x y tyx = Refl
--
substVarSwap (S k) Z     x y tyx = 
  case k of
    Z     => let eq1 = substBelowShiftTerm Z Z y x
                 eq2 = shiftTermByZero Z y
             in sym (trans eq1 eq2)
    (S _) => Refl
--
substVarSwap (S k) (S i) x y tyx = 
  let ih  = substVarSwap k i x y tyx
      ih' = cong {f = shiftTerm Z (S Z)} ih
      eq1 = shiftTermSubstComm Z (S Z) i y (subst_var x i k)
      eq2 = trans (sym eq1) ih'
      eq3 = shiftTermSubstComm Z (S Z) i x (subst_var y (S i) k)
  in trans eq2 eq3


-- Swapping the order of two substitutions at adjacent
-- de Bruijn indices (indices 'i' and 'S i') preserves
-- the result:
-- (See the comment immediately before the previous
-- lemma for an explanation of why the typing of 'x'
-- in the empty context is needed.)
substSwap : (e : Term) ->
            (i : Nat) -> 
            (x : Term) -> (y : Term) ->
            Typing [] x t ->
            subst y i (subst x i e) = subst x i (subst y (S i) e)
--
substSwap (TVar k) i x y tyx = substVarSwap k i x y tyx
substSwap (TAbs e) i x y tyx = congAbs $ substSwap e (S i) x y tyx
substSwap (TApp e1 e2) i x y tyx = 
  congApp (substSwap e1 i x y tyx)
          (substSwap e2 i x y tyx)
substSwap (TRec e1 e2 e3) i x y tyx =
  congRec (substSwap e1 i x y tyx)
          (substSwap e2 i x y tyx)
          (substSwap e3 i x y tyx)
substSwap TZero i x y tyx = Refl
substSwap (TSucc e) i x y tyx = congSucc $ substSwap e i x y tyx
substSwap (TPred e) i x y tyx = congPred $ substSwap e i x y tyx
substSwap (TIfz e1 e2 e3) i x y tyx =
  congIfz (substSwap e1 i x y tyx)
          (substSwap e2 i x y tyx)
          (substSwap e3 i x y tyx)

-- End: SWAPPING OF SUBSTITUTIONS
---------------------------------









