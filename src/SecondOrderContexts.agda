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
module SecondOrderContexts (⅀ : SecondOrderSignature) where

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
          subVar to tySubVar; sub to tySub; Ctx to KndCtx; MCtx to MKndCtx; V0 to TV0; VS to TVS;
          sub◦ to tySub◦; substV0 to substTyV0; substVS to substTyVS; substCtx-Var to substCtx-TyVar;
          substTy-Var to substKnd-TyVar; substCtx-Constr to substCtx-TyConstr;
          substTy-Constr to substKnd-TyConstr; substNil to substTyNil; substCons to substTyCons;
          substTy-ren to substKnd-tyRen; substCtx-ren to substCtx-tyRen; subCtx-Keep to subCtx-TyKeep;
          subCtx-Drop to subCtx-TyDrop; _◦_ to _◦ₜ_)

-- Types of any kind
Typ : KndCtx → Set
Typ Γ = Σ[ κ ∈ _ ] (Ty Γ κ)

-- Typing contexts and their various operations
Ctx : KndCtx → Set
Ctx Γ = List (Typ Γ)

renTyp : ∀{Γ1 Γ2} → TyRen Γ1 Γ2 → Typ Γ1 → Typ Γ2
renTyp ξ (κ , t) = κ , tyRen ξ t

renCtx : ∀{Γ1 Γ2} → TyRen Γ1 Γ2 → Ctx Γ1 → Ctx Γ2
renCtx ξ [] = []
renCtx ξ (t ∷ Δ) = renTyp ξ t ∷ renCtx ξ Δ

renCtx++ : ∀{Γ1 Γ2} {ξ : TyRen Γ1 Γ2} (Δ1 Δ2 : Ctx Γ1) →
            renCtx ξ (Δ1 ++ Δ2) ≡ renCtx ξ Δ1 ++ renCtx ξ Δ2
renCtx++ [] Δ2 = refl
renCtx++ {ξ = ξ} (t ∷ Δ1) Δ2 = cong (renTyp ξ t ∷_) (renCtx++ Δ1 Δ2)

renTypId : ∀{Γ} (t : Typ Γ) → renTyp TyIdRen t ≡ t
renTypId (κ , t) = Σ-≡,≡↔≡ .Inverse.f (refl , renId t)

renCtxId : ∀{Γ} (Δ : Ctx Γ) → renCtx TyIdRen Δ ≡ Δ
renCtxId [] = refl
renCtxId (t ∷ Δ) = cong₂ _∷_ (renTypId t) (renCtxId Δ)

renTyp• : ∀{Γ1 Γ2 Γ3} (ξ1 : TyRen Γ2 Γ3) (ξ2 : TyRen Γ1 Γ2) →
          renTyp (ξ1 • ξ2) ≗ renTyp ξ1 ∘ renTyp ξ2
renTyp• ξ1 ξ2 (κ , t) = Σ-≡,≡↔≡ .Inverse.f (refl , ren• ξ1 ξ2 t)

renCtx• : ∀{Γ1 Γ2 Γ3} (ξ1 : TyRen Γ2 Γ3) (ξ2 : TyRen Γ1 Γ2) →
          renCtx (ξ1 • ξ2) ≗ renCtx ξ1 ∘ renCtx ξ2
renCtx• ξ1 ξ2 [] = refl
renCtx• ξ1 ξ2 (t ∷ Δ) = cong₂ _∷_ (renTyp• ξ1 ξ2 t) (renCtx• ξ1 ξ2 Δ)

subTyp : ∀{Γ1 Γ2} → TySub Γ1 Γ2 → Typ Γ1 → Typ Γ2
subTyp σ (κ , t) = κ , tySub σ t

subCtx : ∀{Γ1 Γ2} → TySub Γ1 Γ2 → Ctx Γ1 → Ctx Γ2
subCtx σ [] = []
subCtx σ (t ∷ Δ) = subTyp σ t ∷ subCtx σ Δ

subCtx++ : ∀{Γ1 Γ2} {σ : TySub Γ1 Γ2} (Δ1 Δ2 : Ctx Γ1) →
            subCtx σ (Δ1 ++ Δ2) ≡ subCtx σ Δ1 ++ subCtx σ Δ2
subCtx++ [] Δ2 = refl
subCtx++ {σ = σ} (t ∷ Δ1) Δ2 = cong (subTyp σ t ∷_) (subCtx++ Δ1 Δ2)

subTypId : ∀{Γ} (t : Typ Γ) → subTyp TyIdSub t ≡ t
subTypId (κ , t) = Σ-≡,≡↔≡ .Inverse.f (refl , subId t)

subCtxId : ∀{Γ} (Δ : Ctx Γ) → subCtx TyIdSub Δ ≡ Δ
subCtxId [] = refl
subCtxId (t ∷ Δ) = cong₂ _∷_ (subTypId t) (subCtxId Δ)

subTypId◦ : ∀{Γ1 Γ2 Γ3} (σ1 : TySub Γ2 Γ3) (σ2 : TySub Γ1 Γ2) →
            subTyp (σ1 ◦ₜ σ2) ≗ subTyp σ1 ∘ subTyp σ2
subTypId◦ σ1 σ2 (κ , t) = Σ-≡,≡↔≡ .Inverse.f (refl , tySub◦ σ1 σ2 t)

subCtx◦ : ∀{Γ1 Γ2 Γ3} (σ1 : TySub Γ2 Γ3) (σ2 : TySub Γ1 Γ2) →
           subCtx (σ1 ◦ₜ σ2) ≗ subCtx σ1 ∘ subCtx σ2
subCtx◦ σ1 σ2 [] = refl
subCtx◦ σ1 σ2 (t ∷ Δ) = cong₂ _∷_ (subTypId◦ σ1 σ2 t) (subCtx◦ σ1 σ2 Δ)

subTypι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) →
          subTyp (ιₜ ξ) ≗ renTyp ξ
subTypι ξ (κ , t) = Σ-≡,≡↔≡ .Inverse.f (refl , subι ξ t)


subCtxι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) →
           subCtx (ιₜ ξ) ≗ renCtx ξ
subCtxι ξ [] = refl
subCtxι ξ (t ∷ Δ) = cong₂ _∷_ (subTypι ξ t) (subCtxι ξ Δ)

Binder : KndCtx → Set
Binder Γ = Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ (Γ' ++ Γ))

renBinder : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (renBinder ξ (Γ' , Δ , t)) = Γ'
fst (snd (renBinder ξ (Γ' , Δ , t))) = renCtx (TyKeep* ξ Γ') Δ
snd (snd (renBinder ξ (Γ' , Δ , t))) = renTyp (TyKeep* ξ Γ') t

renBinders : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
renBinders ξ = map (renBinder ξ)

subBinder : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (subBinder σ (Γ' , Δ , t)) = Γ'
fst (snd (subBinder σ (Γ' , Δ , t))) = subCtx (TyKeepSub* σ Γ') Δ
snd (snd (subBinder σ (Γ' , Δ , t))) = subTyp (TyKeepSub* σ Γ') t

subBinderι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinder (ιₜ ξ) ≗ renBinder ξ
subBinderι ξ (Γ , Δ , (κ , t)) = Σ-≡,≡↔≡ .Inverse.f (
  refl ,
  ×-≡,≡↔≡ .Inverse.f (
    (subCtx (TyKeepSub* (ιₜ ξ) Γ) Δ
      ≡⟨ cong (λ x → subCtx x Δ) (Keepι* ξ Γ) ⟩
    subCtx (ιₜ (TyKeep* ξ Γ)) Δ
      ≡⟨ subCtxι (TyKeep* ξ Γ) Δ ⟩
    renCtx (TyKeep* ξ Γ) Δ ∎) ,
    Σ-≡,≡↔≡ .Inverse.f (
      refl ,
      (tySub (TyKeepSub* (ιₜ ξ) Γ) t
        ≡⟨ cong (λ x → tySub x t) (Keepι* ξ Γ) ⟩
      tySub (ιₜ (TyKeep* ξ Γ)) t
        ≡⟨ subι (TyKeep* ξ Γ) t ⟩
      tyRen (TyKeep* ξ Γ) t ∎))))

subBinders : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
subBinders σ = map (subBinder σ)

subBindersι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinders (ιₜ ξ) ≗ renBinders ξ
subBindersι ξ = map-cong (subBinderι ξ)

MBinder : MKndCtx → Set
MBinder Γ = Σ[ Γ' ∈ KndCtx ] (List (Σ[ κ ∈ _ ] (MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , κ))) × Σ[ κ ∈ _ ] (MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , κ)))

interpBinders : ∀{Σ} (Γ : KndCtx) → TyVec Γ Σ → MBinder Σ → Binder Γ
fst (interpBinders Γ η (Γ' , Δ , t)) = Γ'
fst (snd (interpBinders Γ η (Γ' , Δ , t))) = map (λ{ (κ , x) → κ , interpTm x (tmVec++ η Γ') TyIdSub }) Δ
snd (snd (interpBinders Γ η (Γ' , Δ , (κ , t)))) = κ , interpTm t (tmVec++ η Γ') TyIdSub

map-interpTm : ∀{Γ1 Γ2 Σ} (σ : TySub Γ1 Γ2) (η : TyVec Γ1 Σ) (Γ : KndCtx) →
                (Δ : List (Σ[ κ ∈ _ ] (MTm (map (λ x → [] , x) Γ ++ Σ) ([] , κ)))) →
                map (λ{ (κ , x) → κ , interpTm x (tmVec++ (tySubVec σ η) Γ) TyIdSub }) Δ ≡
                subCtx (TyKeepSub* σ Γ) (map (λ{ (κ , x) → κ , interpTm x (tmVec++ η Γ) TyIdSub }) Δ)
map-interpTm σ η Γ [] = refl
map-interpTm σ η Γ ((κ , t) ∷ Δ) = cong₂ _∷_
  (Σ-≡,≡↔≡ .Inverse.f (refl ,
  (interpTm t (tmVec++ (tySubVec σ η) Γ) TyIdSub
    ≡⟨ cong (λ x → interpTm t x TyIdSub) (tmVec++∘subVec η Γ σ) ⟩
  interpTm t (tySubVec (TyKeepSub* σ Γ) (tmVec++ η Γ)) TyIdSub
    ≡⟨ interpTmSub t (tmVec++ η Γ) (TyKeepSub* σ Γ) TyIdSub TyIdSub (Id◦ _ ∙ sym (◦Id _)) ⟩
   tySub (TyKeepSub* σ Γ) (interpTm t (tmVec++ η Γ) TyIdSub) ∎)))
  (map-interpTm σ η Γ Δ)

interpBinders∘subVec : ∀{Γ1 Γ2 Σ} (σ : TySub Γ1 Γ2) (η : TyVec Γ1 Σ) →
                       interpBinders Γ2 (tySubVec σ η) ≗ subBinder σ ∘ interpBinders Γ1 η
interpBinders∘subVec {Γ1} {Γ2} {Σ} σ η (Γ , Δ , (κ , t)) = Σ-≡,≡↔≡ .Inverse.f (refl ,
  ×-≡,≡↔≡ .Inverse.f (
    map-interpTm σ η Γ Δ ,
    Σ-≡,≡↔≡ .Inverse.f (refl ,
    (interpTm t (tmVec++ (tySubVec σ η) Γ) TyIdSub
      ≡⟨ cong (λ x → interpTm t x TyIdSub) (tmVec++∘subVec η Γ σ) ⟩
    interpTm t (tySubVec (TyKeepSub* σ Γ) (tmVec++ η Γ)) TyIdSub
      ≡⟨ interpTmSub t (tmVec++ η Γ) (TyKeepSub* σ Γ) TyIdSub TyIdSub (Id◦ _ ∙ sym (◦Id _)) ⟩
    tySub (TyKeepSub* σ Γ) (interpTm t (tmVec++ η Γ) TyIdSub) ∎))))
