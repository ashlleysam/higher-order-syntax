{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common

module ThirdOrderSyntax
  -- Kinds
  (Knd : Set)
  -- Kind of types
  (* : Knd)
  -- Type constructor shape
  (Shape₀ : Set)
  -- Type constructor signature
  (Pos₀ : Shape₀ → List (List Knd × Knd) × Knd)
  where

-- Use lower syntax as types
open import SecondOrderSyntax Knd Shape₀ Pos₀ public renaming (Tm to Ty; TmVec to TyVec)

-- Types of * kind
Typ : Ctx → Set
Typ Γ = Ty Γ *

-- Typing contexts and their various operations
Ctx1 : Ctx → Set
Ctx1 Γ = List (Typ Γ)

renCtx1 : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → Ctx1 Γ1 → Ctx1 Γ2
renCtx1 ξ [] = []
renCtx1 ξ (t ∷ Δ) = ren ξ t ∷ renCtx1 ξ Δ

renCtx1++ : ∀{Γ1 Γ2} {ξ : Ren Γ1 Γ2} (Δ1 Δ2 : Ctx1 Γ1) →
            renCtx1 ξ (Δ1 ++ Δ2) ≡ renCtx1 ξ Δ1 ++ renCtx1 ξ Δ2
renCtx1++ [] Δ2 = refl
renCtx1++ {ξ = ξ} (t ∷ Δ1) Δ2 = cong (ren ξ t ∷_) (renCtx1++ Δ1 Δ2)

renCtxId1 : ∀{Γ} (Δ : Ctx1 Γ) → renCtx1 IdRen Δ ≡ Δ
renCtxId1 [] = refl
renCtxId1 (t ∷ Δ) = cong₂ _∷_ (renId t) (renCtxId1 Δ)

renCtx1• : ∀{Γ1 Γ2 Γ3} (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
          renCtx1 (ξ1 • ξ2) ≈ renCtx1 ξ1 ∘ renCtx1 ξ2
renCtx1• ξ1 ξ2 [] = refl
renCtx1• ξ1 ξ2 (t ∷ Δ) = cong₂ _∷_ (ren• ξ1 ξ2 t) (renCtx1• ξ1 ξ2 Δ)

renVecCtx : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) →
            List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ1) × Typ (Γ' ++ Γ1))) →
            List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ2) × Typ (Γ' ++ Γ2)))
renVecCtx ξ [] = []
renVecCtx ξ ((Γ' , Δ , t) ∷ ts) = (Γ' , renCtx1 (Keep* ξ Γ') Δ , ren (Keep* ξ Γ') t) ∷ renVecCtx ξ ts

subCtx1 : ∀{Γ1 Γ2} → Sub Γ1 Γ2 → Ctx1 Γ1 → Ctx1 Γ2
subCtx1 σ [] = []
subCtx1 σ (t ∷ Δ) = sub σ t ∷ subCtx1 σ Δ

subCtx1++ : ∀{Γ1 Γ2} {σ : Sub Γ1 Γ2} (Δ1 Δ2 : Ctx1 Γ1) →
            subCtx1 σ (Δ1 ++ Δ2) ≡ subCtx1 σ Δ1 ++ subCtx1 σ Δ2
subCtx1++ [] Δ2 = refl
subCtx1++ {σ = σ} (t ∷ Δ1) Δ2 = cong (sub σ t ∷_) (subCtx1++ Δ1 Δ2)

subCtxId1 : ∀{Γ} (Δ : Ctx1 Γ) → subCtx1 IdSub Δ ≡ Δ
subCtxId1 [] = refl
subCtxId1 (t ∷ Δ) = cong₂ _∷_ (subId t) (subCtxId1 Δ)

subCtx1◦ : ∀{Γ1 Γ2 Γ3} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
           subCtx1 (σ1 ◦ σ2) ≈ subCtx1 σ1 ∘ subCtx1 σ2
subCtx1◦ σ1 σ2 [] = refl
subCtx1◦ σ1 σ2 (t ∷ Δ) = cong₂ _∷_ (sub◦ σ1 σ2 t) (subCtx1◦ σ1 σ2 Δ)

subCtx1ι : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) →
           subCtx1 (ι ξ) ≈ renCtx1 ξ
subCtx1ι ξ [] = refl
subCtx1ι ξ (t ∷ Δ) = cong₂ _∷_ (subι ξ t) (subCtx1ι ξ Δ)

subVecCtx : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) →
            List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ1) × Typ (Γ' ++ Γ1))) →
            List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ2) × Typ (Γ' ++ Γ2)))
subVecCtx σ [] = []
subVecCtx σ ((Γ' , Δ , t) ∷ ts) = (Γ' , subCtx1 (KeepSub* σ Γ') Δ , sub (KeepSub* σ Γ') t) ∷ subVecCtx σ ts

module Syntax1
  -- Term constructor shape
  (Shape₁ : Set)
  -- Type part of constructor signature
  (Pos₀₁ : Shape₁ → List (Ctx × Knd))
  -- Term part of constructor signature, which depends on the type part
  (Pos₁ : (s : Shape₁) (Γ : Ctx) → TyVec Γ (Pos₀₁ s) → List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ) × Typ (Γ' ++ Γ))) × Typ Γ)
  -- Coherence requirements
  (renVecPos₁ : ∀{Γ1 Γ2 c} (ξ : Ren Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                Pos₁ c Γ2 (renVec ξ ts) .snd ≡ ren ξ (Pos₁ c Γ1 ts .snd))
  (renVecCtxPos₁ : ∀{Γ1 Γ2 c} (ξ : Ren Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                   Pos₁ c Γ2 (renVec ξ ts) .fst ≡ renVecCtx ξ (Pos₁ c Γ1 ts .fst))
  (subVecPos₁ : ∀{Γ1 Γ2 c} (σ : Sub Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                Pos₁ c Γ2 (subVec σ ts) .snd ≡ sub σ (Pos₁ c Γ1 ts .snd))
  (subVecCtxPos₁ : ∀{Γ1 Γ2 c} (σ : Sub Γ1 Γ2) (ts : TyVec Γ1 (Pos₀₁ c)) →
                  Pos₁ c Γ2 (subVec σ ts) .fst ≡ subVecCtx σ (Pos₁ c Γ1 ts .fst))
  where

  -- In-context variables
  data Var1 : (Γ : Ctx) (Δ : Ctx1 Γ) → Typ Γ → Set where
    V0 : ∀{Γ Δ} {t : Typ Γ} → Var1 Γ (t ∷ Δ) t
    VS : ∀{Γ Δ} {t s : Typ Γ} → Var1 Γ Δ t → Var1 Γ (s ∷ Δ) t

  data Tm (Γ : Ctx) (Δ : Ctx1 Γ) : Typ Γ → Set
  data TmVec (Γ : Ctx) (Δ : Ctx1 Γ) : List (Σ[ Γ' ∈ Ctx ] (Ctx1 (Γ' ++ Γ) × Typ (Γ' ++ Γ))) → Set

  -- Well-typed terms
  data Tm Γ Δ where
    var1 : ∀{t} → Var1 Γ Δ t → Tm Γ Δ t
    constr1 : (c : Shape₁) →
             (ts : TyVec Γ (Pos₀₁ c)) →
             (es : TmVec Γ Δ (Pos₁ c Γ ts .fst)) →
             Tm Γ Δ (Pos₁ c Γ ts .snd)

  -- Well-typed lists of terms
  -- infixr 5 _∷_
  data TmVec Γ Δ where
    [] : TmVec Γ Δ []
    _∷_ : ∀{Γ' t Θ} {Δ' : Ctx1 (Γ' ++ Γ)} →
          (e : Tm (Γ' ++ Γ) (Δ' ++ renCtx1 (Drop* IdRen Γ') Δ) t) →
          (es : TmVec Γ Δ Θ) →
          TmVec Γ Δ (((Γ' , Δ' , t)) ∷ Θ)

  --------------
  -- RENAMING --
  --------------

  data Ren1 (Γ : Ctx) : (Δ1 Δ2 : Ctx1 Γ) → Set where
    ε : Ren1 Γ [] []
    Keep1 : ∀{Δ1 Δ2 t} → Ren1 Γ Δ1 Δ2 → Ren1 Γ (t ∷ Δ1) (t ∷ Δ2)
    Drop1 : ∀{Δ1 Δ2 t} → Ren1 Γ Δ1 Δ2 → Ren1 Γ Δ1 (t ∷ Δ2)

  -- Weaken the kind context of a renaming
  wkRen : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : Ren Γ1 Γ2) → Ren1 Γ1 Δ1 Δ2 → Ren1 Γ2 (renCtx1 ξ Δ1) (renCtx1 ξ Δ2)
  wkRen ξ1 ε = ε
  wkRen ξ1 (Keep1 ξ2) = Keep1 (wkRen ξ1 ξ2)
  wkRen ξ1 (Drop1 ξ2) = Drop1 (wkRen ξ1 ξ2)

  IdRen1 : ∀{Γ Δ} → Ren1 Γ Δ Δ
  IdRen1 {Δ = []} = ε 
  IdRen1 {Δ = t ∷ Δ} = Keep1 IdRen1

  Keep1* : ∀{Γ Δ1 Δ2} → Ren1 Γ Δ1 Δ2 → ∀ Δ' → Ren1 Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
  Keep1* ξ [] = ξ
  Keep1* ξ (t ∷ Δ') = Keep1 (Keep1* ξ Δ')

  Keep01 : ∀{Γ Δ1 Δ2 κ} → Ren1 Γ Δ1 Δ2 → Ren1 (κ ∷ Γ) (renCtx1 (Drop IdRen) Δ1) (renCtx1 (Drop IdRen) Δ2)
  Keep01 ε = ε
  Keep01 (Keep1 ξ) = Keep1 (Keep01 ξ)
  Keep01 (Drop1 ξ) = Drop1 (Keep01 ξ)

  Keep01* : ∀{Γ Δ1 Δ2} → Ren1 Γ Δ1 Δ2 → ∀ Γ' → Ren1 (Γ' ++ Γ) (renCtx1 (Drop* IdRen Γ') Δ1) (renCtx1 (Drop* IdRen Γ') Δ2)
  Keep01* {Γ} {Δ1} {Δ2} ξ [] = subst₂ (Ren1 Γ) (sym (renCtxId1 Δ1)) (sym (renCtxId1 Δ2)) ξ
  Keep01* {Γ} {Δ1} {Δ2} ξ (κ ∷ Γ') = 
    subst₂ (Ren1 (κ ∷ Γ' ++ Γ))
      (renCtx1 (Drop IdRen) (renCtx1 (Drop* IdRen Γ') Δ1)
        ≡⟨ sym (renCtx1• (Drop IdRen) (Drop* IdRen Γ') Δ1) ⟩
      renCtx1 (Drop (IdRen • Drop* IdRen Γ')) Δ1
        ≡⟨ cong (λ x → renCtx1 (Drop x) Δ1) (Id• (Drop* IdRen Γ')) ⟩
      renCtx1 (Drop (Drop* IdRen Γ')) Δ1 ∎)
      (renCtx1 (Drop IdRen) (renCtx1 (Drop* IdRen Γ') Δ2)
        ≡⟨ sym (renCtx1• (Drop IdRen) (Drop* IdRen Γ') Δ2) ⟩
      renCtx1 (Drop (IdRen • Drop* IdRen Γ')) Δ2
        ≡⟨ cong (λ x → renCtx1 (Drop x) Δ2) (Id• (Drop* IdRen Γ')) ⟩
      renCtx1 (Drop (Drop* IdRen Γ')) Δ2 ∎)
      ξ'
    where
    ξ' : Ren1 (κ ∷ Γ' ++ Γ) (renCtx1 (Drop IdRen) (renCtx1 (Drop* IdRen Γ') Δ1))
                            (renCtx1 (Drop IdRen) (renCtx1 (Drop* IdRen Γ') Δ2))     
    ξ' = Keep01 (Keep01* ξ Γ')

  -- Variable renaming
  renVar1 : ∀{Γ Δ1 Δ2 t} → Ren1 Γ Δ1 Δ2 → Var1 Γ Δ1 t → Var1 Γ Δ2 t
  renVar1 (Keep1 ξ) V0 = V0
  renVar1 (Keep1 ξ) (VS x) = VS (renVar1 ξ x)
  renVar1 (Drop1 ξ) x = VS (renVar1 ξ x)

  -- Term renaming
  ren1 : ∀{Γ Δ1 Δ2 t} → Ren1 Γ Δ1 Δ2 → Tm Γ Δ1 t → Tm Γ Δ2 t
  renVec1 : ∀{Γ Δ1 Δ2 Θ} → Ren1 Γ Δ1 Δ2 → TmVec Γ Δ1 Θ → TmVec Γ Δ2 Θ

  ren1 ξ (var1 x) = var1 (renVar1 ξ x)
  ren1 ξ (constr1 c ts es) = constr1 c ts (renVec1 ξ es)
  
  renVec1 ξ [] = [] 
  renVec1 {Γ} {Δ1} {Δ2} {(Γ' , Δ' , t) ∷ Θ} ξ (e ∷ es) =
    ren1 (Keep1* (Keep01* ξ Γ') Δ') e ∷ renVec1 ξ es

  -- Rename the types in a variable
  renVar01 : ∀{Γ1 Γ2 Δ t} (ξ : Ren Γ1 Γ2) → Var1 Γ1 Δ t → Var1 Γ2 (renCtx1 ξ Δ) (ren ξ t)
  renVar01 ξ V0 = V0 
  renVar01 ξ (VS x) = VS (renVar01 ξ x)

  -- Rename the types in a term
  ren01 : ∀{Γ1 Γ2 Δ t} (ξ : Ren Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (renCtx1 ξ Δ) (ren ξ t)
  renVec01 : ∀{Γ1 Γ2 Δ Θ} (ξ : Ren Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (renCtx1 ξ Δ) (renVecCtx ξ Θ)

  ren01 ξ (var1 x) = var1 (renVar01 ξ x)
  ren01 {Γ1} {Γ2} {Δ} ξ (constr1 c ts es) =
    subst (Tm Γ2 (renCtx1 ξ Δ)) (renVecPos₁ ξ ts)
      (constr1 c (renVec ξ ts)
      (subst (TmVec Γ2 (renCtx1 ξ Δ))
        (sym (renVecCtxPos₁ ξ ts)) (renVec01 ξ es)))
  
  renVec01 ξ [] = [] 
  renVec01 {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} ξ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (ren (Keep* ξ Γ') t)) eq (ren01 (Keep* ξ Γ') e) ∷ renVec01 ξ es
    where
    eq : renCtx1 (Keep* ξ Γ') (Δ' ++ renCtx1 (Drop* IdRen Γ') Δ) ≡
         renCtx1 (Keep* ξ Γ') Δ' ++ renCtx1 (Drop* IdRen Γ') (renCtx1 ξ Δ)
    eq =
      renCtx1 (Keep* ξ Γ') (Δ' ++ renCtx1 (Drop* IdRen Γ') Δ)
        ≡⟨ renCtx1++ Δ' (renCtx1 (Drop* IdRen Γ') Δ) ⟩
      renCtx1 (Keep* ξ Γ') Δ' ++ renCtx1 (Keep* ξ Γ') (renCtx1 (Drop* IdRen Γ') Δ)
        ≡⟨ cong (renCtx1 (Keep* ξ Γ') Δ' ++_) (
          renCtx1 (Keep* ξ Γ') (renCtx1 (Drop* IdRen Γ') Δ)
            ≡⟨ sym (renCtx1• (Keep* ξ Γ') (Drop* IdRen Γ') Δ) ⟩
          renCtx1 (Keep* ξ Γ' • Drop* IdRen Γ') Δ
            ≡⟨ cong (flip renCtx1 Δ) (sym (Keep*•Drop* Γ')) ⟩
          renCtx1 (Drop* (ξ • IdRen) Γ') Δ
            ≡⟨ cong (λ x → renCtx1 (Drop* x Γ') Δ) (•Id ξ) ⟩
          renCtx1 (Drop* ξ Γ') Δ
            ≡⟨ cong (λ x → renCtx1 (Drop* x Γ') Δ) (sym (Id• ξ)) ⟩
          renCtx1 (Drop* (IdRen • ξ) Γ') Δ
            ≡⟨ cong (flip renCtx1 Δ) (Drop*• Γ') ⟩
          renCtx1 (Drop* IdRen Γ' • ξ) Δ
            ≡⟨ renCtx1• (Drop* IdRen Γ') ξ Δ ⟩
          renCtx1 (Drop* IdRen Γ') (renCtx1 ξ Δ) ∎) ⟩
      renCtx1 (Keep* ξ Γ') Δ' ++ renCtx1 (Drop* IdRen Γ') (renCtx1 ξ Δ) ∎

  ------------------
  -- SUBSTITUTION --
  ------------------

  data Sub1 (Γ : Ctx) : (Δ1 Δ2 : Ctx1 Γ) → Set where
    ε : ∀{Δ} → Sub1 Γ [] Δ
    _▸_ : ∀{Δ1 Δ2 t} (σ : Sub1 Γ Δ1 Δ2) (e : Tm Γ Δ2 t) → Sub1 Γ (t ∷ Δ1) Δ2

  -- Weaken the kind context of a substitution
  wkSub : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : Ren Γ1 Γ2) → Sub1 Γ1 Δ1 Δ2 → Sub1 Γ2 (renCtx1 ξ Δ1) (renCtx1 ξ Δ2)
  wkSub ξ ε = ε
  wkSub ξ (σ ▸ e) = wkSub ξ σ ▸ ren01 ξ e

  infixr 9 _•◦1_ 
  _•◦1_ : ∀{Γ Δ1 Δ2 Δ3} → Ren1 Γ Δ2 Δ3 → Sub1 Γ Δ1 Δ2 → Sub1 Γ Δ1 Δ3
  ξ •◦1 ε = ε
  ξ •◦1 (σ ▸ e) = (ξ •◦1 σ) ▸ ren1 ξ e

  DropSub1 : ∀{Γ Δ1 Δ2 t} → Sub1 Γ Δ1 Δ2 → Sub1 Γ Δ1 (t ∷ Δ2)
  DropSub1 σ = Drop1 IdRen1 •◦1 σ

  DropSub1* : ∀{Γ Δ1 Δ2} → Sub1 Γ Δ1 Δ2 → ∀ Δ' → Sub1 Γ Δ1 (Δ' ++ Δ2)
  DropSub1* σ [] = σ
  DropSub1* σ (t ∷ Δ') = DropSub1 (DropSub1* σ Δ')

  KeepSub1 : ∀{Γ Δ1 Δ2 t} → Sub1 Γ Δ1 Δ2 → Sub1 Γ (t ∷ Δ1) (t ∷ Δ2)
  KeepSub1 σ = DropSub1 σ ▸ var1 V0

  KeepSub1* : ∀{Γ Δ1 Δ2} → Sub1 Γ Δ1 Δ2 → ∀ Δ' → Sub1 Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
  KeepSub1* σ [] = σ
  KeepSub1* σ (t ∷ Δ') = KeepSub1 (KeepSub1* σ Δ')

  ι1 : ∀{Γ Δ1 Δ2} → Ren1 Γ Δ1 Δ2 → Sub1 Γ Δ1 Δ2
  ι1 ε = ε
  ι1 (Keep1 ξ) = KeepSub1 (ι1 ξ)
  ι1 (Drop1 ξ) = DropSub1 (ι1 ξ)

  IdSub1 : ∀{Γ Δ} → Sub1 Γ Δ Δ
  IdSub1 = ι1 IdRen1

  -- Variable substitution
  subVar1 : ∀{Γ Δ1 Δ2 t} → Sub1 Γ Δ1 Δ2 → Var1 Γ Δ1 t → Tm Γ Δ2 t
  subVar1 (σ ▸ e) V0 = e
  subVar1 (σ ▸ e) (VS x) = subVar1 σ x
  
  -- Term substitution
  sub1 : ∀{Γ Δ1 Δ2 t} → Sub1 Γ Δ1 Δ2 → Tm Γ Δ1 t → Tm Γ Δ2 t
  subVec1 : ∀{Γ Δ1 Δ2 Θ} → Sub1 Γ Δ1 Δ2 → TmVec Γ Δ1 Θ → TmVec Γ Δ2 Θ

  sub1 σ (var1 x) = subVar1 σ x
  sub1 σ (constr1 c ts es) = constr1 c ts (subVec1 σ es)

  subVec1 σ [] = []
  subVec1 {Θ = (Γ' , Δ' , t) ∷ Θ} σ (e ∷ es) =
    sub1 (KeepSub1* (wkSub (Drop* IdRen Γ') σ) Δ') e ∷ subVec1 σ es

  -- Substitute the types in a variable
  subVar01 : ∀{Γ1 Γ2 Δ t} (σ : Sub Γ1 Γ2) → Var1 Γ1 Δ t → Var1 Γ2 (subCtx1 σ Δ) (sub σ t)
  subVar01 ξ V0 = V0
  subVar01 ξ (VS x) = VS (subVar01 ξ x)

  -- Substitute the types in a term
  sub01 : ∀{Γ1 Γ2 Δ t} (σ : Sub Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (subCtx1 σ Δ) (sub σ t)
  subVec01 : ∀{Γ1 Γ2 Δ Θ} (σ : Sub Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (subCtx1 σ Δ) (subVecCtx σ Θ)

  sub01 σ (var1 x) = var1 (subVar01 σ x)
  sub01 {Γ1} {Γ2} {Δ} {t} σ (constr1 c ts es) =
    subst (Tm Γ2 (subCtx1 σ Δ)) (subVecPos₁ σ ts)
      (constr1 c (subVec σ ts)
      (subst (TmVec Γ2 (subCtx1 σ Δ))
        (sym (subVecCtxPos₁ σ ts)) (subVec01 σ es)))

  subVec01 σ [] = [] 
  subVec01 {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} σ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (sub (KeepSub* σ Γ') t)) eq (sub01 (KeepSub* σ Γ') e) ∷ subVec01 σ es
    where
    eq : subCtx1 (KeepSub* σ Γ') (Δ' ++ renCtx1 (Drop* IdRen Γ') Δ) ≡
         subCtx1 (KeepSub* σ Γ') Δ' ++ renCtx1 (Drop* IdRen Γ') (subCtx1 σ Δ)
    eq =
      subCtx1 (KeepSub* σ Γ') (Δ' ++ renCtx1 (Drop* IdRen Γ') Δ)
        ≡⟨ subCtx1++ Δ' (renCtx1 (Drop* IdRen Γ') Δ) ⟩
      subCtx1 (KeepSub* σ Γ') Δ' ++ subCtx1 (KeepSub* σ Γ') (renCtx1 (Drop* IdRen Γ') Δ)
        ≡⟨ cong (subCtx1 (KeepSub* σ Γ') Δ' ++_) (
          subCtx1 (KeepSub* σ Γ') (renCtx1 (Drop* IdRen Γ') Δ)
            ≡⟨ cong (subCtx1 (KeepSub* σ Γ')) (sym (subCtx1ι (Drop* IdRen Γ') Δ)) ⟩
          subCtx1 (KeepSub* σ Γ') (subCtx1 (ι (Drop* IdRen Γ')) Δ)
            ≡⟨ sym (subCtx1◦ (KeepSub* σ Γ') (ι (Drop* IdRen Γ')) Δ) ⟩
          subCtx1 (KeepSub* σ Γ' ◦ ι (Drop* IdRen Γ')) Δ
            ≡⟨ cong (flip subCtx1 Δ) (
              KeepSub* σ Γ' ◦ ι (Drop* IdRen Γ')
                ≡⟨ cong (KeepSub* σ Γ' ◦_) (sym (Drop*ι IdRen Γ')) ⟩
              KeepSub* σ Γ' ◦ DropSub* IdSub Γ'
                ≡⟨ sym (Keep*◦Drop* σ IdSub Γ') ⟩
              DropSub* (σ ◦ IdSub) Γ'
                ≡⟨ cong (flip DropSub* Γ') (◦Id σ) ⟩
              DropSub* σ Γ'
                ≡⟨ cong (flip DropSub* Γ') (sym (Id◦ σ)) ⟩
              DropSub* (IdSub ◦ σ) Γ'
                ≡⟨ Drop*◦ IdSub σ Γ' ⟩
              DropSub* IdSub Γ' ◦ σ
                ≡⟨ cong (_◦ σ) (Drop*ι IdRen Γ') ⟩
              ι (Drop* IdRen Γ') ◦ σ ∎) ⟩
          subCtx1 (ι (Drop* IdRen Γ') ◦ σ) Δ
            ≡⟨ subCtx1◦ (ι (Drop* IdRen Γ')) σ Δ ⟩
          subCtx1 (ι (Drop* IdRen Γ')) (subCtx1 σ Δ)
            ≡⟨ subCtx1ι (Drop* IdRen Γ') (subCtx1 σ Δ) ⟩
          renCtx1 (Drop* IdRen Γ') (subCtx1 σ Δ) ∎) ⟩
      subCtx1 (KeepSub* σ Γ') Δ' ++ renCtx1 (Drop* IdRen Γ') (subCtx1 σ Δ) ∎
