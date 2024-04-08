{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.List
open import Data.Nat
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common

module SystemF where

data Knd : Set where
  * : Knd

data Shape₀ : Set where
  Arrow : Shape₀
  All : Shape₀

Pos₀ : Shape₀ → List (List Knd × Knd) × Knd
-- _⇒_ * * : *
Pos₀ Arrow = ([] , *) ∷ ([] , *) ∷ [] , *
-- ∀ [*]* : *
Pos₀ All = (* ∷ [] , *) ∷ [] , *

open import ThirdOrderSyntax Knd * Shape₀ Pos₀

-- Aliases for type constructors
ArrowTy : ∀{Γ} → Ty Γ * → Ty Γ * → Ty Γ *
ArrowTy s t = constr Arrow (s ∷ t ∷ [])

AllTy : ∀{Γ} → Ty (* ∷ Γ) * → Ty Γ *
AllTy t = constr All (t ∷ [])

data Shape₁ : Set where
  Lam App Abs AppTy : Shape₁

Pos₀₁ : Shape₁ → List (List Knd × Knd)
Pos₀₁ Lam = ([] , *) ∷ ([] , *) ∷ []
Pos₀₁ App = ([] , *) ∷ ([] , *) ∷ []
Pos₀₁ Abs = (* ∷ [] , *) ∷ []
Pos₀₁ AppTy = (* ∷ [] , *) ∷ ([] , *) ∷ []

Pos₁ : (s : Shape₁) (Γ : List Knd) →
       TyVec Γ (Pos₀₁ s) →
       List (Σ[ Δ ∈ List Knd ] (Ctx1 (Δ ++ Γ) × Typ (Δ ++ Γ))) × Typ Γ
-- Lam (s : *) (t : *) [s]t : s ⇒ t
Pos₁ Lam Γ (s ∷ t ∷ []) = ([] , s ∷ [] , t) ∷ [] , ArrowTy s t
-- App (s : *) (t : *) (s ⇒ t) s : t
Pos₁ App Γ (s ∷ t ∷ []) = ([] , [] , ArrowTy s t) ∷ ([] , [] , s) ∷ [] , t
-- Abs (t : [*]*) [*]t : ∀t
Pos₁ Abs Γ (t ∷ []) = (* ∷ [] , [] , t) ∷ [] , AllTy t
-- AppTy (t : [*]*) (s : *) ∀t s : t⟨s⟩
Pos₁ AppTy Γ (t ∷ s ∷ []) = ([] , [] , AllTy t) ∷ [] , sub (IdSub ▸ s) t

{-
Still have to prove these coherence properties!
We should be able to abstract this detail away if
Pos₁ is specified using metavariables in the syntax
itself rather than a generic function.
This may require adding explicit substitutions though.
-}
renVecPos₁ : ∀{Γ1 Γ2 c} (ξ : Ren Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
             Pos₁ c Γ2 (renVec ξ ts) .snd ≡ ren ξ (Pos₁ c Γ1 ts .snd)
renVecPos₁ {c = Lam} ξ (s ∷ t ∷ []) = refl
renVecPos₁ {c = App} ξ (s ∷ t ∷ []) = refl
renVecPos₁ {c = Abs} ξ (t ∷ [])     = refl
renVecPos₁ {c = AppTy} ξ (t ∷ s ∷ []) =
  sub (IdSub ▸ ren ξ s) (ren (Keep ξ) t)
    ≡⟨ sym (sub◦• (IdSub ▸ ren ξ s) (Keep ξ) t) ⟩
  sub ((IdSub ◦• ξ) ▸ ren ξ s) t
    ≡⟨ cong (λ x → sub (x ▸ ren ξ s) t) (
      IdSub ◦• ξ   ≡⟨ Id◦• ξ ⟩
      ι ξ          ≡⟨ sym (•◦Id ξ) ⟩
      ξ •◦ IdSub   ∎) ⟩
  sub ((ξ •◦ IdSub) ▸ ren ξ s) t
    ≡⟨ sub•◦ ξ (IdSub ▸ s) t ⟩
  ren ξ (sub (IdSub ▸ s) t) ∎

renVecCtxPos₁ : ∀{Γ1 Γ2 c} (ξ : Ren Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                Pos₁ c Γ2 (renVec ξ ts) .fst ≡ renVecCtx ξ (Pos₁ c Γ1 ts .fst)
renVecCtxPos₁ {c = Lam}   ξ (s ∷ t ∷ []) = refl
renVecCtxPos₁ {c = App}   ξ (s ∷ t ∷ []) = refl
renVecCtxPos₁ {c = Abs}   ξ (t ∷ [])     = refl
renVecCtxPos₁ {c = AppTy} ξ (t ∷ s ∷ []) = refl

subVecPos₁ : ∀{Γ1 Γ2 c} (σ : Sub Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
              Pos₁ c Γ2 (subVec σ ts) .snd ≡ sub σ (Pos₁ c Γ1 ts .snd)
subVecPos₁ {c = Lam}   σ (s ∷ t ∷ []) = refl
subVecPos₁ {c = App}   σ (s ∷ t ∷ []) = refl
subVecPos₁ {c = Abs}   σ (t ∷ [])     = refl
subVecPos₁ {c = AppTy} σ (t ∷ s ∷ []) =
  sub (IdSub ▸ sub σ s) (sub (KeepSub σ) t)
    ≡⟨ sym (sub◦ (IdSub ▸ sub σ s) (KeepSub σ) t) ⟩
  sub (((IdSub ▸ sub σ s) ◦ Drop IdRen •◦ σ) ▸ sub σ s) t
    ≡⟨ cong (λ x → sub (x ▸ sub σ s) t) (
      (IdSub ▸ sub σ s) ◦ Drop IdRen •◦ σ
        ≡⟨ ◦•◦ (IdSub ▸ sub σ s) (Drop IdRen) σ ⟩
      (IdSub ◦• IdRen) ◦ σ
        ≡⟨ cong (_◦ σ) (Id◦• IdRen) ⟩
      IdSub ◦ σ
        ≡⟨ Id◦ σ ⟩
      σ
        ≡⟨ sym (◦Id σ) ⟩
      σ ◦ IdSub ∎) ⟩
  sub ((σ ◦ IdSub) ▸ sub σ s) t
    ≡⟨ sub◦ σ (IdSub ▸ s) t ⟩
  sub σ (sub (IdSub ▸ s) t) ∎

subVecCtxPos₁ : ∀{Γ1 Γ2 c} (σ : Sub Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                Pos₁ c Γ2 (subVec σ ts) .fst ≡ subVecCtx σ (Pos₁ c Γ1 ts .fst)
subVecCtxPos₁ {c = Lam}   σ (s ∷ t ∷ []) = refl
subVecCtxPos₁ {c = App}   σ (s ∷ t ∷ []) = refl
subVecCtxPos₁ {c = Abs}   σ (t ∷ [])     = refl
subVecCtxPos₁ {c = AppTy} σ (t ∷ s ∷ []) = refl

open Syntax1 Shape₁ Pos₀₁ Pos₁ renVecPos₁ renVecCtxPos₁ subVecPos₁ subVecCtxPos₁ public

-- Aliases for each constructor
LamTm : ∀{Γ Δ s t} → Tm Γ (s ∷ Δ) t → Tm Γ Δ (ArrowTy s t)
LamTm {Γ} {Δ} {s} {t} e =
  -- Unfortunately we still need to use gross lemmas to construct terms
  -- in the expected way as many equalities do not hold on the nose
  constr1 Lam (s ∷ t ∷ []) (e' ∷ [])
  where
  e' : Tm Γ (s ∷ renCtx1 IdRen Δ) t
  e' = subst (λ x → Tm Γ (s ∷ x) t) (sym (renCtxId1 Δ)) e

AppTm : ∀{Γ Δ s t} → Tm Γ Δ (ArrowTy s t) → Tm Γ Δ s → Tm Γ Δ t
AppTm {Γ} {Δ} {s} {t} e1 e2 = constr1 App (s ∷ t ∷ []) (e1' ∷ e2' ∷ [])
  where
  e1' : Tm Γ (renCtx1 IdRen Δ) (ArrowTy s t)
  e1' = subst (λ x → Tm Γ x (ArrowTy s t)) (sym (renCtxId1 Δ)) e1

  e2' : Tm Γ (renCtx1 IdRen Δ) s
  e2' = subst (λ x → Tm Γ x s) (sym (renCtxId1 Δ)) e2

AbsTm : ∀{Γ Δ t} → Tm (* ∷ Γ) (renCtx1 (Drop IdRen) Δ) t → Tm Γ Δ (AllTy t)
AbsTm {Γ} {Δ} {t} e = constr1 Abs (t ∷ []) (e ∷ [])

AppTyTm : ∀{Γ Δ t} → Tm Γ Δ (AllTy t) → (s : Ty Γ *) → Tm Γ Δ (sub (IdSub ▸ s) t)
AppTyTm {Γ} {Δ} {t} e s = constr1 AppTy (t ∷ s ∷ []) (e' ∷ [])
  where
  e' : Tm Γ (renCtx1 IdRen Δ) (AllTy t)
  e' = subst (λ x → Tm Γ x (AllTy t)) (sym (renCtxId1 Δ)) e

-- Values of the language
data Value : ∀{t} → Tm [] [] t → Set where
  valLam : ∀{s t} (e : Tm [] (s ∷ []) t) → Value (LamTm e)
  valAbs : ∀{t} (e : Tm (* ∷ []) [] t) → Value (AbsTm e)

isValue : ∀{t} (e : Tm [] [] t) → Dec (Value e)
isValue (constr1 Lam   (s ∷ t ∷ []) (e ∷ []))       = yes (valLam e)
isValue (constr1 App   (s ∷ t ∷ []) (e1 ∷ e2 ∷ [])) = no λ ()
isValue (constr1 Abs   (t ∷ [])     (e ∷ []))       = yes (valAbs e)
isValue (constr1 AppTy (t ∷ s ∷ []) (e ∷ []))       = no λ ()

-- Operational semantics
data _⇒_ : ∀{t} → Tm [] [] t → Tm [] [] t → Set where
  stepFun : ∀{s t} (e1 e1' : Tm [] [] (ArrowTy s t)) (e2 : Tm [] [] s) →
            e1 ⇒ e1' → AppTm e1 e2 ⇒ AppTm e1' e2
  stepArg : ∀{s t} (e1 : Tm [] [] (ArrowTy s t)) (e2 e2' : Tm [] [] s) →
            Value e1 → e2 ⇒ e2' → AppTm e1 e2 ⇒ AppTm e1 e2'
  stepβ : ∀{s t} (e1 : Tm [] (s ∷ []) t) (e2 : Tm [] [] s) →
          AppTm (LamTm e1) e2 ⇒ sub1 (IdSub1 ▸ e2) e1
  
  stepTyFun : ∀{t} (e1 e1' : Tm [] [] (AllTy t)) (s : Ty [] *) →
              e1 ⇒ e1' → AppTyTm e1 s ⇒ AppTyTm e1' s
  stepTyβ : ∀{t} (e : Tm (* ∷ []) [] t) (s : Ty [] *) →
            AppTyTm (AbsTm e) s ⇒ sub01 (IdSub ▸ s) e

-- Values cannot step
valNoStep : ∀{t} {e e' : Tm [] [] t} → Value e → ¬ (e ⇒ e')
valNoStep (valLam e) = λ ()
valNoStep (valAbs e) = λ ()

progress : ∀{t} (e : Tm [] [] t) →
           (Value e) ⊎ Σ[ e' ∈ Tm [] [] t ] (e ⇒ e')
progress (constr1 Lam   (s ∷ t ∷ []) (e ∷ []))       = inl (valLam e)
progress (constr1 App   (s ∷ t ∷ []) (e1 ∷ e2 ∷ [])) with progress e1
... | inl (valLam e)     = inr (sub1 (IdSub1 ▸ e2) e , stepβ e e2)
... | inr (e1' , e1⇒e1') = inr (AppTm e1' e2 , stepFun e1 e1' e2 e1⇒e1')
progress (constr1 Abs   (t ∷ [])     (e ∷ []))       = inl (valAbs e)
progress (constr1 AppTy (t ∷ s ∷ []) (e ∷ []))       with progress e
... | inl (valAbs e)  = inr (sub01 (IdSub ▸ s) e , stepTyβ e s)
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
idFunTy : ∀{Γ} → Typ Γ
idFunTy = AllTy (ArrowTy (var V0) (var V0))

-- idFun : idFunTy := ΛX.λx:X.x
idFun : ∀{Γ Δ} → Tm Γ Δ idFunTy
idFun = AbsTm (LamTm (var1 V0))

-- Nat := ∀X.X⇒(X⇒X)⇒X
Nat : ∀{Γ} → Typ Γ
Nat = AllTy (ArrowTy (var V0) (ArrowTy (ArrowTy (var V0) (var V0)) (var V0)))

-- Zero : Nat := ΛX.λz:X.λs:X⇒X.z
Zero : ∀{Γ Δ} → Tm Γ Δ Nat
Zero = AbsTm (LamTm (LamTm (var1 (VS V0))))

-- Zero [Nat] Zero (idFun [Nat]) : Nat
alsoZero : ∀{Γ Δ} → Tm Γ Δ Nat
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
Suc : ∀{Γ Δ} → Tm Γ Δ (ArrowTy Nat Nat)
Suc = LamTm (AbsTm (LamTm (LamTm (AppTm (var1 V0) (
  AppTm (var1 V0) (AppTm (AppTm (AppTyTm (var1 (VS (VS V0))) (var V0)) (var1 (VS V0))) (var1 V0)))))))

-- [n]
fromℕ : ∀{Γ Δ} → ℕ → Tm Γ Δ Nat
fromℕ zero = Zero
fromℕ (suc n) = AppTm Suc (fromℕ n)

-- add : Nat⇒Nat⇒Nat := λm:Nat.λn:Nat.m [Nat] n Suc
add : ∀{Γ Δ} → Tm Γ Δ (ArrowTy Nat (ArrowTy Nat Nat))
add = LamTm (LamTm (AppTm (AppTm (AppTyTm (var1 (VS V0)) Nat) (var1 V0)) Suc))

{-
Because this is a Church encoding (and we don't reduce under binders),
you don't necessarily get on-the-nose equalities!
-}
_ : runFor 7 (AppTm (AppTm add (fromℕ 2)) (fromℕ 3)) .fst ≢ runFor 1 (fromℕ 5) .fst
_ = λ ()