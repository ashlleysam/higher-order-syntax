{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Product.Properties
open import Data.Fin
open import Data.List
open import Data.List.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Function.Bundles

open ≡-Reasoning

open import Common
open import KindSignatures

module TypeContexts (⅀ : KindSignature) where

open KindSignature ⅀

open import Types ⅀

---------------------
-- TYPING CONTEXTS --
---------------------

-- Types with an associated kind
Typ : Set
Typ = ⅀ .Knd × Ty

-- Renaming
renTyp : Ren → Typ → Typ
renTyp ξ (κ , t) = κ , renTy ξ t

renTyp-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renTyp ξ1 ≗ renTyp ξ2
renTyp-ext p (κ , t) = cong (κ ,_) (renTy-ext p t)

renTyp-≈Id : ∀{ξ} → ξ ≗ id → renTyp ξ ≗ id
renTyp-≈Id p (κ , t) = cong (κ ,_) (renTy-≈Id p t)

renTypId : renTyp id ≗ id
renTypId = renTyp-≈Id ≗-refl

renTyp• : (ξ1 ξ2 : Ren) → renTyp ξ1 ∘ renTyp ξ2 ≗ renTyp (ξ1 • ξ2)
renTyp• ξ1 ξ2 (κ , t) = cong (κ ,_) (renTy• ξ1 ξ2 t)

-- Substitution
subTyp : TySub → Typ → Typ
subTyp σ (κ , t) = κ , subTy σ t

subTyp-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subTyp σ1 ≗ subTyp σ2
subTyp-ext p (κ , t) = cong (κ ,_) (subTy-ext p t)

subTyp-≈Id : ∀{σ} → σ ≗ tyVar → subTyp σ ≗ id
subTyp-≈Id p (κ , t) = cong (κ ,_) (subTy-≈Id p t)

subTypId : subTyp tyVar ≗ id
subTypId = subTyp-≈Id ≗-refl

subTyp◦ₜ : (σ1 σ2 : TySub) → subTyp σ1 ∘ subTyp σ2 ≗ subTyp (σ1 ◦ₜ σ2)
subTyp◦ₜ σ1 σ2 (κ , t) = cong (κ ,_) (subTy◦ₜ σ1 σ2 t)

subTypιₜ : (ξ : Ren) → subTyp (ιₜ ξ) ≗ renTyp ξ
subTypιₜ ξ (κ , t) = cong (κ ,_) (subTyιₜ ξ t)

-- Typing contexts
Ctx : Set
Ctx = List Typ

-- Renaming
renCtx : Ren → Ctx → Ctx
renCtx ξ = map (renTyp ξ)

renCtx++ : (ξ : Ren) (Δ1 Δ2 : Ctx) →
           renCtx ξ (Δ1 ++ Δ2) ≡ renCtx ξ Δ1 ++ renCtx ξ Δ2
renCtx++ ξ = map-++-commute (renTyp ξ)

renCtx-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renCtx ξ1 ≗ renCtx ξ2
renCtx-ext p = map-cong (renTyp-ext p)

renCtx-≈Id : ∀{ξ} → ξ ≗ id → renCtx ξ ≗ id
renCtx-≈Id p Δ = map-cong (renTyp-≈Id p) Δ ∙ map-id Δ

renCtxId : renCtx id ≗ id
renCtxId = renCtx-≈Id ≗-refl

renCtx• : (ξ1 ξ2 : Ren) → renCtx ξ1 ∘ renCtx ξ2 ≗ renCtx (ξ1 • ξ2)
renCtx• ξ1 ξ2 Δ = sym (map-compose Δ) ∙ map-cong (renTyp• ξ1 ξ2) Δ

-- Substitution
subCtx : TySub → Ctx → Ctx
subCtx σ = map (subTyp σ)

subCtx++ : (σ : TySub) (Δ1 Δ2 : Ctx) →
           subCtx σ (Δ1 ++ Δ2) ≡ subCtx σ Δ1 ++ subCtx σ Δ2
subCtx++ σ = map-++-commute (subTyp σ)

subCtx-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subCtx σ1 ≗ subCtx σ2
subCtx-ext p = map-cong (subTyp-ext p)

subCtx-≈Id : ∀{σ} → σ ≗ tyVar → subCtx σ ≗ id
subCtx-≈Id {σ} p Δ = map-cong (subTyp-≈Id p) Δ ∙ map-id Δ

subCtxId : subCtx tyVar ≗ id
subCtxId = subCtx-≈Id ≗-refl

subCtx◦ₜ : (σ1 σ2 : TySub) → subCtx σ1 ∘ subCtx σ2 ≗ subCtx (σ1 ◦ₜ σ2)
subCtx◦ₜ σ1 σ2 Δ = sym (map-compose Δ) ∙ map-cong (subTyp◦ₜ σ1 σ2) Δ

subCtxιₜ : (ξ : Ren) → subCtx (ιₜ ξ) ≗ renCtx ξ
subCtxιₜ ξ Δ = map-cong (subTypιₜ ξ) Δ

-- Binders
Binder : Set
Binder = List (⅀ .Knd) × Ctx × Typ

-- Renaming
renBinder : Ren → Binder → Binder
renBinder ξ (Γ , Δ , t) =
  Γ ,
  renCtx (Keep* ξ (length Γ)) Δ ,
  renTyp (Keep* ξ (length Γ)) t

renBinder-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renBinder ξ1 ≗ renBinder ξ2
renBinder-ext p (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (renCtx-ext (Keep*-ext p (length Γ)) Δ)
    (renTyp-ext (Keep*-ext p (length Γ)) t)

renBinder-≈Id : ∀{ξ} → ξ ≗ id → renBinder ξ ≗ id
renBinder-≈Id p (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (renCtx-≈Id (λ x → Keep*-ext p (length Γ) x ∙ Keep*-id (length Γ) x) Δ)
    (renTyp-≈Id (λ x → Keep*-ext p (length Γ) x ∙ Keep*-id (length Γ) x) t)

renBinderId : renBinder id ≗ id
renBinderId = renBinder-≈Id ≗-refl

renBinder• : (ξ1 ξ2 : Ren) → renBinder ξ1 ∘ renBinder ξ2 ≗ renBinder (ξ1 • ξ2)
renBinder• ξ1 ξ2 (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (renCtx (Keep* ξ1 (length Γ)) (renCtx (Keep* ξ2 (length Γ)) Δ)
      ≡⟨ renCtx• (Keep* ξ1 (length Γ)) (Keep* ξ2 (length Γ)) Δ ⟩
    renCtx (Keep* ξ1 (length Γ) • Keep* ξ2 (length Γ)) Δ
      ≡⟨ renCtx-ext (Keep*•Keep* ξ1 ξ2 (length Γ)) Δ ⟩
    renCtx (Keep* (ξ1 • ξ2) (length Γ)) Δ ∎)
    (renTyp (Keep* ξ1 (length Γ)) (renTyp (Keep* ξ2 (length Γ)) t)
      ≡⟨ renTyp• (Keep* ξ1 (length Γ)) (Keep* ξ2 (length Γ)) t ⟩
    renTyp (Keep* ξ1 (length Γ) • Keep* ξ2 (length Γ)) t
      ≡⟨ renTyp-ext (Keep*•Keep* ξ1 ξ2 (length Γ)) t ⟩
    renTyp (Keep* (ξ1 • ξ2) (length Γ)) t ∎)

-- Substitution
subBinder : TySub → Binder → Binder
subBinder σ (Γ , Δ , t) =
  Γ ,
  subCtx (TyKeepSub* σ (length Γ)) Δ ,
  subTyp (TyKeepSub* σ (length Γ)) t

subBinder-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subBinder σ1 ≗ subBinder σ2
subBinder-ext p (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (subCtx-ext (TyKeepSub*-ext p (length Γ)) Δ)
    (subTyp-ext (TyKeepSub*-ext p (length Γ)) t)

subBinder-≈Id : ∀{σ} → σ ≗ tyVar → subBinder σ ≗ id
subBinder-≈Id p (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (subCtx-≈Id (λ x → TyKeepSub*-ext p (length Γ) x ∙ TyKeepSub*-id (length Γ) x) Δ)
    (subTyp-≈Id (λ x → TyKeepSub*-ext p (length Γ) x ∙ TyKeepSub*-id (length Γ) x) t)

subBinderId : subBinder tyVar ≗ id
subBinderId = subBinder-≈Id ≗-refl

subBinder◦ₜ : (σ1 σ2 : TySub) → subBinder σ1 ∘ subBinder σ2 ≗ subBinder (σ1 ◦ₜ σ2)
subBinder◦ₜ σ1 σ2 (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (subCtx (TyKeepSub* σ1 (length Γ)) (subCtx (TyKeepSub* σ2 (length Γ)) Δ)
      ≡⟨ subCtx◦ₜ (TyKeepSub* σ1 (length Γ)) (TyKeepSub* σ2 (length Γ)) Δ ⟩
    subCtx (TyKeepSub* σ1 (length Γ) ◦ₜ TyKeepSub* σ2 (length Γ)) Δ
      ≡⟨ subCtx-ext (Keep*◦ₜKeep* σ1 σ2 (length Γ)) Δ ⟩
    subCtx (TyKeepSub* (σ1 ◦ₜ σ2) (length Γ)) Δ ∎)
    (subTyp (TyKeepSub* σ1 (length Γ)) (subTyp (TyKeepSub* σ2 (length Γ)) t)
      ≡⟨ subTyp◦ₜ (TyKeepSub* σ1 (length Γ)) (TyKeepSub* σ2 (length Γ)) t ⟩
    subTyp (TyKeepSub* σ1 (length Γ) ◦ₜ TyKeepSub* σ2 (length Γ)) t
      ≡⟨ subTyp-ext (Keep*◦ₜKeep* σ1 σ2 (length Γ)) t ⟩
    subTyp (TyKeepSub* (σ1 ◦ₜ σ2) (length Γ)) t ∎)

subBinderιₜ : (ξ : Ren) → subBinder (ιₜ ξ) ≗ renBinder ξ
subBinderιₜ ξ (Γ , Δ , t) =
  cong₂ (λ x y → Γ , x , y)
    (subCtx (TyKeepSub* (ιₜ ξ) (length Γ)) Δ
      ≡⟨ (sym $ subCtx-ext (Keep*ιₜ ξ (length Γ)) Δ) ⟩
    subCtx (ιₜ (Keep* ξ (length Γ))) Δ
      ≡⟨ subCtxιₜ (Keep* ξ (length Γ)) Δ ⟩
    renCtx (Keep* ξ (length Γ)) Δ ∎)
    (subTyp (TyKeepSub* (ιₜ ξ) (length Γ)) t
      ≡⟨ (sym $ subTyp-ext (Keep*ιₜ ξ (length Γ)) t) ⟩
    subTyp (ιₜ (Keep* ξ (length Γ))) t
      ≡⟨ subTypιₜ (Keep* ξ (length Γ)) t ⟩
    renTyp (Keep* ξ (length Γ)) t ∎)

-- Lists of binders
Binders : Set
Binders = List Binder

-- Renaming
renBinders : Ren → Binders → Binders
renBinders ξ = map (renBinder ξ)

renBinders-++ : (ξ : Ren) (B1 B2 : Binders) →
                renBinders ξ (B1 ++ B2) ≡ renBinders ξ B1 ++ renBinders ξ B2
renBinders-++ ξ = map-++-commute (renBinder ξ)

renBinders-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renBinders ξ1 ≗ renBinders ξ2
renBinders-ext p = map-cong (renBinder-ext p)

renBinders-≈Id : ∀{ξ} → ξ ≗ id → renBinders ξ ≗ id
renBinders-≈Id p B = map-cong (renBinder-≈Id p) B ∙ map-id B

renBindersId : renBinders id ≗ id
renBindersId = renBinders-≈Id ≗-refl

renBinders• : (ξ1 ξ2 : Ren) → renBinders ξ1 ∘ renBinders ξ2 ≗ renBinders (ξ1 • ξ2)
renBinders• ξ1 ξ2 B = sym (map-compose B) ∙ map-cong (renBinder• ξ1 ξ2) B

-- Substitution
subBinders : TySub → Binders → Binders
subBinders σ = map (subBinder σ)

subBinders-++ : (σ : TySub) (B1 B2 : Binders) →
                subBinders σ (B1 ++ B2) ≡ subBinders σ B1 ++ subBinders σ B2
subBinders-++ σ = map-++-commute (subBinder σ)

subBinders-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subBinders σ1 ≗ subBinders σ2
subBinders-ext p = map-cong (subBinder-ext p)

subBinders-≈Id : ∀{σ} → σ ≗ tyVar → subBinders σ ≗ id
subBinders-≈Id p B = map-cong (subBinder-≈Id p) B ∙ map-id B

subBindersId : subBinders tyVar ≗ id
subBindersId = subBinders-≈Id ≗-refl

subBinders◦ₜ : (σ1 σ2 : TySub) → subBinders σ1 ∘ subBinders σ2 ≗ subBinders (σ1 ◦ₜ σ2)
subBinders◦ₜ σ1 σ2 B = sym (map-compose B) ∙ map-cong (subBinder◦ₜ σ1 σ2) B

subBindersιₜ : (ξ : Ren) → subBinders (ιₜ ξ) ≗ renBinders ξ
subBindersιₜ ξ B = map-cong (subBinderιₜ ξ) B
