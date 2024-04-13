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
open import SecondOrderSignatures

-- Contexts of second-order terms
module SecondOrderContexts (⅀ : SecondOrderSignature) (* : ⅀ .Knd) where

open SecondOrderSignature ⅀

{-
  We want to treat the previously defined "terms" as "types"
-}
open import SecondOrderLanguage ⅀ public
  renaming (Tm to Ty; TmVec to TyVec; Var to TyVar; var to tyVar; constr to tyConstr;
          Ren to TyRen; IdRen to TyIdRen; Keep to TyKeep; Keep* to TyKeep*; Keep*•Drop* to TyKeep*•Drop*;
          Keep*◦Drop* to TyKeep*◦Drop*; Drop to TyDrop; Drop* to TyDrop*; Drop*• to TyDrop*•;
          Drop*ι to TyDrop*ι; Drop*◦ to TyDrop*◦; renVar to tyRenVar; ren to tyRen; renVec to tyRenVec;
          Sub to TySub; _•◦_ to _•◦ₜ_; DropSub to TyDropSub; DropSub* to TyDropSub*;
          KeepSub to TyKeepSub; KeepSub* to TyKeepSub*; ι to ιₜ; IdSub to TyIdSub; subVec to tySubVec;
          subVar to tySubVar; sub to tySub; Ctx to KndCtx; MCtx to MKndCtx)

-- Types of * kind
Typ* : KndCtx → Set
Typ* Γ = Ty Γ *

-- Typing contexts and their various operations
Ctx : KndCtx → Set
Ctx Γ = List (Typ* Γ)

renCtx : ∀{Γ1 Γ2} → TyRen Γ1 Γ2 → Ctx Γ1 → Ctx Γ2
renCtx ξ [] = []
renCtx ξ (t ∷ Δ) = tyRen ξ t ∷ renCtx ξ Δ

renCtx++ : ∀{Γ1 Γ2} {ξ : TyRen Γ1 Γ2} (Δ1 Δ2 : Ctx Γ1) →
            renCtx ξ (Δ1 ++ Δ2) ≡ renCtx ξ Δ1 ++ renCtx ξ Δ2
renCtx++ [] Δ2 = refl
renCtx++ {ξ = ξ} (t ∷ Δ1) Δ2 = cong (tyRen ξ t ∷_) (renCtx++ Δ1 Δ2)

renCtxId : ∀{Γ} (Δ : Ctx Γ) → renCtx TyIdRen Δ ≡ Δ
renCtxId [] = refl
renCtxId (t ∷ Δ) = cong₂ _∷_ (renId t) (renCtxId Δ)

renCtx• : ∀{Γ1 Γ2 Γ3} (ξ1 : TyRen Γ2 Γ3) (ξ2 : TyRen Γ1 Γ2) →
          renCtx (ξ1 • ξ2) ≗ renCtx ξ1 ∘ renCtx ξ2
renCtx• ξ1 ξ2 [] = refl
renCtx• ξ1 ξ2 (t ∷ Δ) = cong₂ _∷_ (ren• ξ1 ξ2 t) (renCtx• ξ1 ξ2 Δ)

subCtx : ∀{Γ1 Γ2} → TySub Γ1 Γ2 → Ctx Γ1 → Ctx Γ2
subCtx σ [] = []
subCtx σ (t ∷ Δ) = tySub σ t ∷ subCtx σ Δ

subCtx++ : ∀{Γ1 Γ2} {σ : TySub Γ1 Γ2} (Δ1 Δ2 : Ctx Γ1) →
            subCtx σ (Δ1 ++ Δ2) ≡ subCtx σ Δ1 ++ subCtx σ Δ2
subCtx++ [] Δ2 = refl
subCtx++ {σ = σ} (t ∷ Δ1) Δ2 = cong (tySub σ t ∷_) (subCtx++ Δ1 Δ2)

subCtxId : ∀{Γ} (Δ : Ctx Γ) → subCtx TyIdSub Δ ≡ Δ
subCtxId [] = refl
subCtxId (t ∷ Δ) = cong₂ _∷_ (subId t) (subCtxId Δ)

subCtx◦ : ∀{Γ1 Γ2 Γ3} (σ1 : TySub Γ2 Γ3) (σ2 : TySub Γ1 Γ2) →
           subCtx (σ1 ◦ σ2) ≗ subCtx σ1 ∘ subCtx σ2
subCtx◦ σ1 σ2 [] = refl
subCtx◦ σ1 σ2 (t ∷ Δ) = cong₂ _∷_ (sub◦ σ1 σ2 t) (subCtx◦ σ1 σ2 Δ)

subCtxι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) →
           subCtx (ιₜ ξ) ≗ renCtx ξ
subCtxι ξ [] = refl
subCtxι ξ (t ∷ Δ) = cong₂ _∷_ (subι ξ t) (subCtxι ξ Δ)

Binder : KndCtx → Set
Binder Γ = Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ* (Γ' ++ Γ))

renBinder : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (renBinder ξ (Γ' , Δ , t)) = Γ'
fst (snd (renBinder ξ (Γ' , Δ , t))) = renCtx (TyKeep* ξ Γ') Δ
snd (snd (renBinder ξ (Γ' , Δ , t))) = tyRen (TyKeep* ξ Γ') t

renBinders : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
renBinders ξ = map (renBinder ξ)

subBinder : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (subBinder σ (Γ' , Δ , t)) = Γ'
fst (snd (subBinder σ (Γ' , Δ , t))) = subCtx (TyKeepSub* σ Γ') Δ
snd (snd (subBinder σ (Γ' , Δ , t))) = tySub (TyKeepSub* σ Γ') t

subBinderι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinder (ιₜ ξ) ≗ renBinder ξ
subBinderι ξ (Γ , Δ , t) = Σ-≡,≡↔≡ .Inverse.f (
  refl ,
  ×-≡,≡↔≡ .Inverse.f (
    (subCtx (TyKeepSub* (ιₜ ξ) Γ) Δ
      ≡⟨ cong (λ x → subCtx x Δ) (Keepι* ξ Γ) ⟩
    subCtx (ιₜ (TyKeep* ξ Γ)) Δ
      ≡⟨ subCtxι (TyKeep* ξ Γ) Δ ⟩
    renCtx (TyKeep* ξ Γ) Δ ∎) ,
    (tySub (TyKeepSub* (ιₜ ξ) Γ) t
      ≡⟨ cong (λ x → tySub x t) (Keepι* ξ Γ) ⟩
    tySub (ιₜ (TyKeep* ξ Γ)) t
      ≡⟨ subι (TyKeep* ξ Γ) t ⟩
    tyRen (TyKeep* ξ Γ) t ∎)))

subBinders : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
subBinders σ = map (subBinder σ)

subBindersι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinders (ιₜ ξ) ≗ renBinders ξ
subBindersι ξ = map-cong (subBinderι ξ)

MBinder : MKndCtx → Set
MBinder Γ = Σ[ Γ' ∈ KndCtx ] (List (MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , *)) × MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , *))

interpBinders : ∀{Σ} (Γ : KndCtx) → TyVec Γ Σ → MBinder Σ → Binder Γ
fst (interpBinders Γ η (Γ' , Δ , t)) = Γ'
fst (snd (interpBinders Γ η (Γ' , Δ , t))) = map (λ x → interpTm x (tmVec++ η Γ') TyIdSub) Δ
snd (snd (interpBinders Γ η (Γ' , Δ , t))) = interpTm t (tmVec++ η Γ') TyIdSub

map-interpTm : ∀{Γ1 Γ2 Σ} (σ : TySub Γ1 Γ2) (η : TyVec Γ1 Σ) (Γ : KndCtx) →
                (Δ : List (MTm (map (λ x → [] , x) Γ ++ Σ) ([] , *))) →
                map (λ x → interpTm x (tmVec++ (tySubVec σ η) Γ) TyIdSub) Δ ≡
                subCtx (TyKeepSub* σ Γ) (map (λ x → interpTm x (tmVec++ η Γ) TyIdSub) Δ)
map-interpTm σ η Γ [] = refl
map-interpTm σ η Γ (t ∷ Δ) = cong₂ _∷_
  (interpTm t (tmVec++ (tySubVec σ η) Γ) TyIdSub
    ≡⟨ cong (λ x → interpTm t x TyIdSub) (tmVec++∘subVec η Γ σ) ⟩
  interpTm t (tySubVec (TyKeepSub* σ Γ) (tmVec++ η Γ)) TyIdSub
    ≡⟨ interpTmSub t (tmVec++ η Γ) (TyKeepSub* σ Γ) TyIdSub TyIdSub (Id◦ _ ∙ sym (◦Id _)) ⟩
   tySub (TyKeepSub* σ Γ) (interpTm t (tmVec++ η Γ) TyIdSub) ∎)
  (map-interpTm σ η Γ Δ)

interpBinders∘subVec : ∀{Γ1 Γ2 Σ} (σ : TySub Γ1 Γ2) (η : TyVec Γ1 Σ) →
                       interpBinders Γ2 (tySubVec σ η) ≗ subBinder σ ∘ interpBinders Γ1 η
interpBinders∘subVec {Γ1} {Γ2} {Σ} σ η (Γ , Δ , t) = Σ-≡,≡↔≡ .Inverse.f (
  refl ,
  ×-≡,≡↔≡ .Inverse.f (
    map-interpTm σ η Γ Δ ,
    (interpTm t (tmVec++ (tySubVec σ η) Γ) TyIdSub
      ≡⟨ cong (λ x → interpTm t x TyIdSub) (tmVec++∘subVec η Γ σ) ⟩
    interpTm t (tySubVec (TyKeepSub* σ Γ) (tmVec++ η Γ)) TyIdSub
      ≡⟨ interpTmSub t (tmVec++ η Γ) (TyKeepSub* σ Γ) TyIdSub TyIdSub (Id◦ _ ∙ sym (◦Id _)) ⟩
    tySub (TyKeepSub* σ Γ) (interpTm t (tmVec++ η Γ) TyIdSub) ∎)))
