{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product.Properties
open import Data.List
open import Data.Nat
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import ThirdOrderSignatures

module SystemF where

data FKnd : Set where
  * : FKnd

data FTyShape : Set where
  Arrow : FTyShape
  All : FTyShape

FTyPos : FTyShape → List (List FKnd × FKnd) × FKnd
-- _⇒_ * * : *
FTyPos Arrow = ([] , *) ∷ ([] , *) ∷ [] , *
-- ∀ [*]* : *
FTyPos All = (* ∷ [] , *) ∷ [] , *

⅀F₂ : SecondOrderSignature
Knd ⅀F₂ = FKnd
TyShape ⅀F₂ = FTyShape
TyPos ⅀F₂ = FTyPos

module _ where
  open import SecondOrderContexts ⅀F₂

  -- Aliases for type constructors
  ArrowTy : ∀{Γ} → Ty Γ * → Ty Γ * → Ty Γ *
  ArrowTy s t = tyConstr Arrow (s ∷ t ∷ [])

  AllTy : ∀{Γ} → Ty (* ∷ Γ) * → Ty Γ *
  AllTy t = tyConstr All (t ∷ [])

  data FShape : Set where
    Lam App Abs AppTy : FShape

  FTmTyPos : FShape → List (List FKnd × FKnd)
  FTmTyPos Lam = ([] , *) ∷ ([] , *) ∷ []
  FTmTyPos App = ([] , *) ∷ ([] , *) ∷ []
  FTmTyPos Abs = (* ∷ [] , *) ∷ []
  FTmTyPos AppTy = (* ∷ [] , *) ∷ ([] , *) ∷ []

  FTmPos : (s : FShape) (Γ : KndCtx) (ts : TyVec Γ (FTmTyPos s)) →
          List (Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ (Γ' ++ Γ))) × Typ Γ
  -- Lam (s : *) (t : *) [s]t : s ⇒ t
  FTmPos Lam Γ (s ∷ t ∷ []) = ([] , (* , s) ∷ [] , * , t) ∷ [] , * , ArrowTy s t
  -- App (s : *) (t : *) (s ⇒ t) s : t
  FTmPos App Γ (s ∷ t ∷ []) = ([] , [] , * , ArrowTy s t) ∷ ([] , [] , * , s) ∷ [] , * , t
  -- Abs (t : [*]*) [*]t : ∀t
  FTmPos Abs Γ (t ∷ []) = (* ∷ [] , [] , * , t) ∷ [] , * , AllTy t
  -- AppTy (t : [*]*) (s : *) ∀t s : t⟨s⟩
  FTmPos AppTy Γ (t ∷ s ∷ []) = ([] , [] , * , AllTy t) ∷ [] , * , tySub (TyIdSub ▸ s) t

  subVecFTmPos : ∀{Γ1 Γ2} (s : FShape) (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (FTmTyPos s)) →
                FTmPos s Γ2 (tySubVec σ ts) .snd ≡ subTyp σ (FTmPos s Γ1 ts .snd)        
  subVecFTmPos Lam   σ (s ∷ t ∷ []) = refl
  subVecFTmPos App   σ (s ∷ t ∷ []) = refl
  subVecFTmPos Abs   σ (t ∷ [])     = refl
  subVecFTmPos AppTy σ (t ∷ s ∷ []) = Σ-≡,≡↔≡ .Inverse.f (refl , (
    tySub (TyIdSub ▸ tySub σ s) (tySub (TyKeepSub σ) t)
      ≡⟨ sym (tySub◦ (TyIdSub ▸ tySub σ s) (TyKeepSub σ) t) ⟩
    tySub (((TyIdSub ▸ tySub σ s) ◦ TyDrop TyIdRen •◦ₜ σ) ▸ tySub σ s) t
      ≡⟨ cong (λ x → tySub (x ▸ tySub σ s) t) (
        (TyIdSub ▸ tySub σ s) ◦ TyDrop TyIdRen •◦ₜ σ
          ≡⟨ ◦•◦ (TyIdSub ▸ tySub σ s) (TyDrop TyIdRen) σ ⟩
        (TyIdSub ◦• TyIdRen) ◦ σ
          ≡⟨ cong (_◦ σ) (Id◦• TyIdRen) ⟩
        TyIdSub ◦ σ
          ≡⟨ Id◦ σ ⟩
        σ
          ≡⟨ sym (◦Id σ) ⟩
        σ ◦ TyIdSub ∎) ⟩
    tySub ((σ ◦ TyIdSub) ▸ tySub σ s) t
      ≡⟨ tySub◦ σ (TyIdSub ▸ s) t ⟩
    tySub σ (tySub (TyIdSub ▸ s) t) ∎))


  subVecKndCtxFTmPos : ∀{Γ1 Γ2} (s : FShape) (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (FTmTyPos s)) →
                        FTmPos s Γ2 (tySubVec σ ts) .fst ≡ subBinders σ (FTmPos s Γ1 ts .fst)
  subVecKndCtxFTmPos Lam   σ (s ∷ t ∷ []) = refl
  subVecKndCtxFTmPos App   σ (s ∷ t ∷ []) = refl
  subVecKndCtxFTmPos Abs   σ (t ∷ [])     = refl
  subVecKndCtxFTmPos AppTy σ (t ∷ s ∷ []) = refl

⅀F₃ : ThirdOrderSignature
⅀₂ ⅀F₃ = ⅀F₂
Shape ⅀F₃ = FShape
TmTyPos ⅀F₃ = FTmTyPos
TmPos ⅀F₃ = FTmPos
subVecTmPos ⅀F₃ = subVecFTmPos
subVecKndCtxTmPos ⅀F₃ = subVecKndCtxFTmPos

open import ThirdOrderLanguage ⅀F₃ renaming (_∷_ to _∷'_; [] to []')

-- Aliases for each constructor
LamTm : ∀{Γ Δ s t} → Tm Γ ((* , s) ∷ Δ) (* , t) → Tm Γ Δ (* , ArrowTy s t)
LamTm {Γ} {Δ} {s} {t} e = constr Lam (s ∷' t ∷' []') (e' ∷' []')
  -- Unfortunately we still need to use gross lemmas to construct terms
  -- in the expected way as many equalities do not hold on the nose
  where
  e' : Tm Γ ((* , s) ∷ renCtx (TyDrop* TyIdRen []) Δ) (* , t)
  e' = subst (λ x → Tm Γ ((* , s) ∷ x) (* , t)) (sym (renCtxId Δ)) e

AppTm : ∀{Γ Δ s t} → Tm Γ Δ (* , ArrowTy s t) → Tm Γ Δ (* , s) → Tm Γ Δ (* , t)
AppTm {Γ} {Δ} {s} {t} e1 e2 = constr App (s ∷' t ∷' []') (e1' ∷' e2' ∷' []')
  where
  e1' : Tm Γ (renCtx TyIdRen Δ) (* , ArrowTy s t)
  e1' = subst (λ x → Tm Γ x (* , ArrowTy s t)) (sym (renCtxId Δ)) e1

  e2' : Tm Γ (renCtx TyIdRen Δ) (* , s)
  e2' = subst (λ x → Tm Γ x (* , s)) (sym (renCtxId Δ)) e2

AbsTm : ∀{Γ Δ t} → Tm (* ∷ Γ) (renCtx (TyDrop TyIdRen) Δ) (* , t) → Tm Γ Δ (* , AllTy t)
AbsTm {Γ} {Δ} {t} e = constr Abs (t ∷' []') (e ∷' []')

AppTyTm : ∀{Γ Δ t} → Tm Γ Δ (* , AllTy t) → (s : Ty Γ *) → Tm Γ Δ (* , tySub (TyIdSub ▸ s) t)
AppTyTm {Γ} {Δ} {t} e s = constr AppTy (t ∷' s ∷' []') (e' ∷' []')
  where
  e' : Tm Γ (renCtx TyIdRen Δ) (* , AllTy t)
  e' = subst (λ x → Tm Γ x (* , AllTy t)) (sym (renCtxId Δ)) e

-- Values of the language
data Value : ∀{t} → Tm [] [] t → Set where
  valLam : ∀{s t} (e : Tm [] ((* , s) ∷ []) (* , t)) → Value (LamTm e)
  valAbs : ∀{t} (e : Tm (* ∷ []) [] (* , t)) → Value (AbsTm e)

isValue : ∀{t} (e : Tm [] [] t) → Dec (Value e)
isValue (constr Lam   (s ∷' t ∷' []') (e ∷' []'))        = yes (valLam e)
isValue (constr App   (s ∷' t ∷' []') (e1 ∷' e2 ∷' []')) = no λ ()
isValue (constr Abs   (t ∷' []')      (e ∷' []'))        = yes (valAbs e)
isValue (constr AppTy (t ∷' s ∷' []') (e ∷' []'))        = no λ ()

-- Operational semantics
data _⇒_ : ∀{t} → Tm [] [] t → Tm [] [] t → Set where
  stepFun : ∀{s t} (e1 e1' : Tm [] [] (* , ArrowTy s t)) (e2 : Tm [] [] (* , s)) →
            e1 ⇒ e1' → AppTm e1 e2 ⇒ AppTm e1' e2
  stepArg : ∀{s t} (e1 : Tm [] [] (* , ArrowTy s t)) (e2 e2' : Tm [] [] (* , s)) →
            Value e1 → e2 ⇒ e2' → AppTm e1 e2 ⇒ AppTm e1 e2'
  stepβ : ∀{s t} (e1 : Tm [] ((* , s) ∷ []) (* , t)) (e2 : Tm [] [] (* , s)) →
          AppTm (LamTm e1) e2 ⇒ sub (IdSub ▸ e2) e1
  
  stepTyFun : ∀{t} (e1 e1' : Tm [] [] (* , AllTy t)) (s : Ty [] *) →
              e1 ⇒ e1' → AppTyTm e1 s ⇒ AppTyTm e1' s
  stepTyβ : ∀{t} (e : Tm (* ∷ []) [] (* , t)) (s : Ty [] *) →
            AppTyTm (AbsTm e) s ⇒ subTy (TyIdSub ▸ s) e

-- Values cannot step
valNoStep : ∀{t} {e e' : Tm [] [] t} → Value e → ¬ (e ⇒ e')
valNoStep (valLam e) = λ ()
valNoStep (valAbs e) = λ ()

progress : ∀{t} (e : Tm [] [] t) →
           (Value e) ⊎ Σ[ e' ∈ Tm [] [] t ] (e ⇒ e')
progress (constr Lam   (s ∷' t ∷' []') (e ∷' []'))       = inl (valLam e)
progress (constr App   (s ∷' t ∷' []') (e1 ∷' e2 ∷' []')) with progress e1
... | inl (valLam e)     = inr (sub (IdSub ▸ e2) e , stepβ e e2)
... | inr (e1' , e1⇒e1') = inr (AppTm e1' e2 , stepFun e1 e1' e2 e1⇒e1')
progress (constr Abs   (t ∷' []')     (e ∷' []'))       = inl (valAbs e)
progress (constr AppTy (t ∷' s ∷' []') (e ∷' []'))       with progress e
... | inl (valAbs e)  = inr (subTy (TyIdSub ▸ s) e , stepTyβ e s)
... | inr (e' , e⇒e') = inr (AppTyTm e' s , stepTyFun e e' s e⇒e')     

infixr 5 _∷_
data _⇒*[_]_ : ∀{t} → Tm [] [] t → ℕ → Tm [] [] t → Set where
  [] : ∀{t} {e : Tm [] [] t} → e ⇒*[ zero ] e
  _∷_ : ∀{t n} {e1 e2 e3 : Tm [] [] t} → e1 ⇒ e2 → e2 ⇒*[ n ] e3 → e1 ⇒*[ suc n ] e3

_⇓_ : ∀{t} (e e' : Tm [] [] t) → Set
e ⇓ e' = Σ[ n ∈ ℕ ] (e ⇒*[ n ] e') × (Value e')

runFor : ∀{t} (gas : ℕ) (e : Tm [] [] t) →
         Σ[ e' ∈ Tm [] [] t ] (e ⇒*[ gas ] e' ⊎ e ⇓ e')
runFor zero e with isValue e
... | yes e-Value = e , inr (zero , [] , e-Value)
... | no ¬e-Value = e , inl []
runFor (suc gas) e with progress e
... | inl e-Val = e , inr (zero , [] , e-Val)
... | inr (e' , e⇒e') with runFor gas e'
... | e'' , inl e'⇒*e'' = e'' , inl (e⇒e' ∷ e'⇒*e'') 
... | e'' , inr (n , e'⇒e'' , e''-Value) = e'' , inr (suc n , e⇒e' ∷ e'⇒e'' , e''-Value)

-- idFunTy := ∀X.X⇒X
idFunTy : ∀{Γ} → Ty Γ *
idFunTy = AllTy (ArrowTy (tyVar TV0) (tyVar TV0))

-- idFun : idFunTy := ΛX.λx:X.x
idFun : ∀{Γ Δ} → Tm Γ Δ (* , idFunTy)
idFun = AbsTm (LamTm (var V0))

-- Nat := ∀X.X⇒(X⇒X)⇒X
Nat : ∀{Γ} → Ty Γ *
Nat = AllTy (ArrowTy (tyVar TV0) (ArrowTy (ArrowTy (tyVar TV0) (tyVar TV0)) (tyVar TV0)))

-- Zero : Nat := ΛX.λz:X.λs:X⇒X.z
Zero : ∀{Γ Δ} → Tm Γ Δ (* , Nat)
Zero = AbsTm (LamTm (LamTm (var (VS V0))))

-- Zero [Nat] Zero (idFun [Nat]) : Nat
alsoZero : ∀{Γ Δ} → Tm Γ Δ (* , Nat)
alsoZero = AppTm (AppTm (AppTyTm Zero Nat) Zero) (AppTyTm idFun Nat)

{-
Zero [Nat] Zero (idFun [Nat])
=
(ΛX.λz:X.λs:X⇒X.z) [Nat] Zero (idFun [Nat])
⇒
(λz:Nat.λs:Nat⇒Nat.z) Zero (idFun [Nat])
⇒
(λs:Nat⇒Nat.Zero) (idFun [Nat])
⇒
Zero
-}
_ : runFor 3 alsoZero .fst ≡ Zero
_ = refl

-- Suc : Nat⇒Nat := λn:Nat.ΛX.λz:X.λs:X⇒X.s (n [X] z s)
Suc : ∀{Γ Δ} → Tm Γ Δ (* , ArrowTy Nat Nat)
Suc = LamTm (AbsTm (LamTm (LamTm (AppTm (var V0) (
  AppTm (var V0) (AppTm (AppTm (AppTyTm (var (VS (VS V0))) (tyVar TV0)) (var (VS V0))) (var V0)))))))

-- [n]
fromℕ : ∀{Γ Δ} → ℕ → Tm Γ Δ (* , Nat)
fromℕ zero = Zero
fromℕ (suc n) = AppTm Suc (fromℕ n)

-- add : Nat⇒Nat⇒Nat := λm:Nat.λn:Nat.m [Nat] n Suc
add : ∀{Γ Δ} → Tm Γ Δ (* , ArrowTy Nat (ArrowTy Nat Nat))
add = LamTm (LamTm (AppTm (AppTm (AppTyTm (var (VS V0)) Nat) (var V0)) Suc))

{-
Because this is a Church encoding (and we don't reduce under binders),
you don't necessarily get on-the-nose equalities!
-}
_ : runFor 7 (AppTm (AppTm add (fromℕ 2)) (fromℕ 3)) .fst ≢ runFor 1 (fromℕ 5) .fst
_ = λ ()
