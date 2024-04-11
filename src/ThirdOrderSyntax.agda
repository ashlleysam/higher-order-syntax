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

module ThirdOrderSyntax
  -- Kinds
  (Knd : Set)
  -- Kind of types
  (* : Knd)
  -- Type constructor shape
  (TyShape : Set)
  -- Type constructor signature
  (TyPos : TyShape → List (List Knd × Knd) × Knd)
  where

-- Use lower syntax as types
open import SecondOrderSyntax Knd TyShape TyPos public
  renaming (Tm to Ty; TmVec to TyVec; Var to TyVar; var to tyVar; constr to tyConstr;
            Ren to TyRen; IdRen to TyIdRen; Keep* to TyKeep*; Keep*•Drop* to TyKeep*•Drop*;
            Keep*◦Drop* to TyKeep*◦Drop*; Drop to TyDrop; Drop* to TyDrop*; Drop*• to TyDrop*•;
            Drop*ι to TyDrop*ι; Drop*◦ to TyDrop*◦; renVar to tyRenVar; ren to tyRen; renVec to tyRenVec;
            Sub to TySub; _•◦_ to _•◦ₜ_; DropSub to TyDropSub; DropSub* to TyDropSub*;
            KeepSub to TyKeepSub; KeepSub* to TyKeepSub*; ι to ιₜ; IdSub to TyIdSub; subVec to tySubVec;
            subVar to tySubVar; sub to tySub)

-- Types of * kind
Typ : Ctx → Set
Typ Γ = Ty Γ *

-- Typing contexts and their various operations
TyCtx : Ctx → Set
TyCtx Γ = List (Typ Γ)

renTyCtx : ∀{Γ1 Γ2} → TyRen Γ1 Γ2 → TyCtx Γ1 → TyCtx Γ2
renTyCtx ξ [] = []
renTyCtx ξ (t ∷ Δ) = tyRen ξ t ∷ renTyCtx ξ Δ

renTyCtx++ : ∀{Γ1 Γ2} {ξ : TyRen Γ1 Γ2} (Δ1 Δ2 : TyCtx Γ1) →
            renTyCtx ξ (Δ1 ++ Δ2) ≡ renTyCtx ξ Δ1 ++ renTyCtx ξ Δ2
renTyCtx++ [] Δ2 = refl
renTyCtx++ {ξ = ξ} (t ∷ Δ1) Δ2 = cong (tyRen ξ t ∷_) (renTyCtx++ Δ1 Δ2)

renTyCtxId : ∀{Γ} (Δ : TyCtx Γ) → renTyCtx TyIdRen Δ ≡ Δ
renTyCtxId [] = refl
renTyCtxId (t ∷ Δ) = cong₂ _∷_ (renId t) (renTyCtxId Δ)

renTyCtx• : ∀{Γ1 Γ2 Γ3} (ξ1 : TyRen Γ2 Γ3) (ξ2 : TyRen Γ1 Γ2) →
          renTyCtx (ξ1 • ξ2) ≈ renTyCtx ξ1 ∘ renTyCtx ξ2
renTyCtx• ξ1 ξ2 [] = refl
renTyCtx• ξ1 ξ2 (t ∷ Δ) = cong₂ _∷_ (ren• ξ1 ξ2 t) (renTyCtx• ξ1 ξ2 Δ)

subTyCtx : ∀{Γ1 Γ2} → TySub Γ1 Γ2 → TyCtx Γ1 → TyCtx Γ2
subTyCtx σ [] = []
subTyCtx σ (t ∷ Δ) = tySub σ t ∷ subTyCtx σ Δ

subTyCtx++ : ∀{Γ1 Γ2} {σ : TySub Γ1 Γ2} (Δ1 Δ2 : TyCtx Γ1) →
            subTyCtx σ (Δ1 ++ Δ2) ≡ subTyCtx σ Δ1 ++ subTyCtx σ Δ2
subTyCtx++ [] Δ2 = refl
subTyCtx++ {σ = σ} (t ∷ Δ1) Δ2 = cong (tySub σ t ∷_) (subTyCtx++ Δ1 Δ2)

subTyCtxId : ∀{Γ} (Δ : TyCtx Γ) → subTyCtx TyIdSub Δ ≡ Δ
subTyCtxId [] = refl
subTyCtxId (t ∷ Δ) = cong₂ _∷_ (subId t) (subTyCtxId Δ)

subTyCtx◦ : ∀{Γ1 Γ2 Γ3} (σ1 : TySub Γ2 Γ3) (σ2 : TySub Γ1 Γ2) →
           subTyCtx (σ1 ◦ σ2) ≈ subTyCtx σ1 ∘ subTyCtx σ2
subTyCtx◦ σ1 σ2 [] = refl
subTyCtx◦ σ1 σ2 (t ∷ Δ) = cong₂ _∷_ (sub◦ σ1 σ2 t) (subTyCtx◦ σ1 σ2 Δ)

subTyCtxι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) →
           subTyCtx (ιₜ ξ) ≈ renTyCtx ξ
subTyCtxι ξ [] = refl
subTyCtxι ξ (t ∷ Δ) = cong₂ _∷_ (subι ξ t) (subTyCtxι ξ Δ)

Binder : Ctx → Set
Binder Γ = Σ[ Γ' ∈ Ctx ] (TyCtx (Γ' ++ Γ) × Typ (Γ' ++ Γ))

renBinder : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (renBinder ξ (Γ' , Δ , t)) = Γ'
fst (snd (renBinder ξ (Γ' , Δ , t))) = renTyCtx (TyKeep* ξ Γ') Δ
snd (snd (renBinder ξ (Γ' , Δ , t))) = tyRen (TyKeep* ξ Γ') t

renBinders : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
renBinders ξ = map (renBinder ξ)

subBinder : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → Binder Γ1 → Binder Γ2
fst (subBinder σ (Γ' , Δ , t)) = Γ'
fst (snd (subBinder σ (Γ' , Δ , t))) = subTyCtx (TyKeepSub* σ Γ') Δ
snd (snd (subBinder σ (Γ' , Δ , t))) = tySub (TyKeepSub* σ Γ') t

subBinderι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinder (ιₜ ξ) ≗ renBinder ξ
subBinderι ξ (Γ , Δ , t) = Σ-≡,≡↔≡ .Inverse.f (
  refl ,
  ×-≡,≡↔≡ .Inverse.f (
    (subTyCtx (TyKeepSub* (ιₜ ξ) Γ) Δ
      ≡⟨ cong (λ x → subTyCtx x Δ) (Keepι* ξ Γ) ⟩
    subTyCtx (ιₜ (TyKeep* ξ Γ)) Δ
      ≡⟨ subTyCtxι (TyKeep* ξ Γ) Δ ⟩
    renTyCtx (TyKeep* ξ Γ) Δ ∎) ,
    (tySub (TyKeepSub* (ιₜ ξ) Γ) t
      ≡⟨ cong (λ x → tySub x t) (Keepι* ξ Γ) ⟩
    tySub (ιₜ (TyKeep* ξ Γ)) t
      ≡⟨ subι (TyKeep* ξ Γ) t ⟩
    tyRen (TyKeep* ξ Γ) t ∎)))

subBinders : ∀{Γ1 Γ2} (σ : TySub Γ1 Γ2) → List (Binder Γ1) → List (Binder Γ2)
subBinders σ = map (subBinder σ)

subBindersι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) → subBinders (ιₜ ξ) ≗ renBinders ξ
subBindersι ξ = map-cong (subBinderι ξ)

MBinder : MCtx → Set
MBinder Γ = Σ[ Γ' ∈ Ctx ] (List (MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , *)) × MTm (map (λ x → [] , x) Γ' ++ Γ) ([] , *))

interpBinders : ∀{Σ} (Γ : Ctx) → TyVec Γ Σ → MBinder Σ → Binder Γ
fst (interpBinders Γ η (Γ' , Δ , t)) = Γ'
fst (snd (interpBinders Γ η (Γ' , Δ , t))) = map (λ x → interpTm x (tmVec++ η Γ') TyIdSub) Δ
snd (snd (interpBinders Γ η (Γ' , Δ , t))) = interpTm t (tmVec++ η Γ') TyIdSub

map-interpTm : ∀{Γ1 Γ2 Σ} (σ : TySub Γ1 Γ2) (η : TyVec Γ1 Σ) (Γ : Ctx) →
                (Δ : List (MTm (map (λ x → [] , x) Γ ++ Σ) ([] , *))) →
                map (λ x → interpTm x (tmVec++ (tySubVec σ η) Γ) TyIdSub) Δ ≡
                subTyCtx (TyKeepSub* σ Γ) (map (λ x → interpTm x (tmVec++ η Γ) TyIdSub) Δ)
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

module Syntax1
  -- Term constructor shape
  (Shape : Set)
  -- Type part of constructor signature
  (TmTyPos : Shape → List (Ctx × Knd))
  -- Term part of constructor signature, which depends on the type part
  (TmPos : (s : Shape) (Γ : Ctx) → TyVec Γ (TmTyPos s) → List (Σ[ Γ' ∈ Ctx ] (TyCtx (Γ' ++ Γ) × Typ (Γ' ++ Γ))) × Typ Γ)
  -- Coherence requirements
  (subVecTmPos : ∀{Γ1 Γ2 c} (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos c)) →
                TmPos c Γ2 (tySubVec σ ts) .snd ≡ tySub σ (TmPos c Γ1 ts .snd))
  (subVecCtxTmPos : ∀{Γ1 Γ2 c} (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos c)) →
                  TmPos c Γ2 (tySubVec σ ts) .fst ≡ subBinders σ (TmPos c Γ1 ts .fst))
  where

  renVecTmPos : ∀{Γ1 Γ2 c} (ξ : TyRen Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos c)) →
                TmPos c Γ2 (tyRenVec ξ ts) .snd ≡ tyRen ξ (TmPos c Γ1 ts .snd)
  renVecTmPos {Γ1} {Γ2} {s} ξ ts =
    TmPos s Γ2 (tyRenVec ξ ts) .snd
      ≡⟨ sym (cong (λ x → TmPos s Γ2 x .snd) (subVecι ξ ts)) ⟩
    TmPos s Γ2 (tySubVec (ιₜ ξ) ts) .snd
      ≡⟨ subVecTmPos (ιₜ ξ) ts ⟩
    tySub (ιₜ ξ) (TmPos s Γ1 ts .snd)
      ≡⟨ subι ξ  (TmPos s Γ1 ts .snd) ⟩
    tyRen ξ (TmPos s Γ1 ts .snd) ∎

  renVecCtxTmPos : ∀{Γ1 Γ2 s} (ξ : TyRen Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos s)) →
                  TmPos s Γ2 (tyRenVec ξ ts) .fst ≡ renBinders ξ (TmPos s Γ1 ts .fst)
  renVecCtxTmPos {Γ1} {Γ2} {s} ξ ts =
    TmPos s Γ2 (tyRenVec ξ ts) .fst
      ≡⟨ cong (λ x → TmPos s Γ2 x .fst) (sym (subVecι ξ ts)) ⟩
    TmPos s Γ2 (tySubVec (ιₜ ξ) ts) .fst
      ≡⟨ subVecCtxTmPos (ιₜ ξ) ts ⟩
    subBinders (ιₜ ξ) (TmPos s Γ1 ts .fst)
      ≡⟨ subBindersι ξ (TmPos s Γ1 ts .fst) ⟩
    renBinders ξ (TmPos s Γ1 ts .fst) ∎

  -- In-context variables
  data Var : (Γ : Ctx) (Δ : TyCtx Γ) → Typ Γ → Set where
    V0 : ∀{Γ Δ} {t : Typ Γ} → Var Γ (t ∷ Δ) t
    VS : ∀{Γ Δ} {t s : Typ Γ} → Var Γ Δ t → Var Γ (s ∷ Δ) t

  data Tm (Γ : Ctx) (Δ : TyCtx Γ) : Typ Γ → Set
  data TmVec (Γ : Ctx) (Δ : TyCtx Γ) : List (Σ[ Γ' ∈ Ctx ] (TyCtx (Γ' ++ Γ) × Typ (Γ' ++ Γ))) → Set

  -- Well-typed terms
  data Tm Γ Δ where
    var : ∀{t} → Var Γ Δ t → Tm Γ Δ t
    constr : (c : Shape) →
             (ts : TyVec Γ (TmTyPos c)) →
             (es : TmVec Γ Δ (TmPos c Γ ts .fst)) →
             Tm Γ Δ (TmPos c Γ ts .snd)

  -- Well-typed lists of terms
  -- infixr 5 _∷_
  data TmVec Γ Δ where
    [] : TmVec Γ Δ []
    _∷_ : ∀{Γ' t Θ} {Δ' : TyCtx (Γ' ++ Γ)} →
          (e : Tm (Γ' ++ Γ) (Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') Δ) t) →
          (es : TmVec Γ Δ Θ) →
          TmVec Γ Δ (((Γ' , Δ' , t)) ∷ Θ)

  --------------
  -- RENAMING --
  --------------

  data Ren (Γ : Ctx) : (Δ1 Δ2 : TyCtx Γ) → Set where
    ε : Ren Γ [] []
    Keep : ∀{Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Ren Γ (t ∷ Δ1) (t ∷ Δ2)
    Drop : ∀{Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Ren Γ Δ1 (t ∷ Δ2)

  -- Rename the kind context of a renaming
  wkRen : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : TyRen Γ1 Γ2) → Ren Γ1 Δ1 Δ2 → Ren Γ2 (renTyCtx ξ Δ1) (renTyCtx ξ Δ2)
  wkRen ξ1 ε = ε
  wkRen ξ1 (Keep ξ2) = Keep (wkRen ξ1 ξ2)
  wkRen ξ1 (Drop ξ2) = Drop (wkRen ξ1 ξ2)

  IdRen : ∀{Γ Δ} → Ren Γ Δ Δ
  IdRen {Δ = []} = ε 
  IdRen {Δ = t ∷ Δ} = Keep IdRen

  Keep* : ∀{Γ Δ1 Δ2} → Ren Γ Δ1 Δ2 → ∀ Δ' → Ren Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
  Keep* ξ [] = ξ
  Keep* ξ (t ∷ Δ') = Keep (Keep* ξ Δ')

  KeepTy : ∀{Γ Δ1 Δ2 κ} → Ren Γ Δ1 Δ2 → Ren (κ ∷ Γ) (renTyCtx (TyDrop TyIdRen) Δ1) (renTyCtx (TyDrop TyIdRen) Δ2)
  KeepTy ε = ε
  KeepTy (Keep ξ) = Keep (KeepTy ξ)
  KeepTy (Drop ξ) = Drop (KeepTy ξ)

  KeepTy* : ∀{Γ Δ1 Δ2} → Ren Γ Δ1 Δ2 → ∀ Γ' → Ren (Γ' ++ Γ) (renTyCtx (TyDrop* TyIdRen Γ') Δ1) (renTyCtx (TyDrop* TyIdRen Γ') Δ2)
  KeepTy* {Γ} {Δ1} {Δ2} ξ [] = subst₂ (Ren Γ) (sym (renTyCtxId Δ1)) (sym (renTyCtxId Δ2)) ξ
  KeepTy* {Γ} {Δ1} {Δ2} ξ (κ ∷ Γ') = 
    subst₂ (Ren (κ ∷ Γ' ++ Γ))
      (renTyCtx (TyDrop TyIdRen) (renTyCtx (TyDrop* TyIdRen Γ') Δ1)
        ≡⟨ sym (renTyCtx• (TyDrop TyIdRen) (TyDrop* TyIdRen Γ') Δ1) ⟩
      renTyCtx (TyDrop (TyIdRen • TyDrop* TyIdRen Γ')) Δ1
        ≡⟨ cong (λ x → renTyCtx (TyDrop x) Δ1) (Id• (TyDrop* TyIdRen Γ')) ⟩
      renTyCtx (TyDrop (TyDrop* TyIdRen Γ')) Δ1 ∎)
      (renTyCtx (TyDrop TyIdRen) (renTyCtx (TyDrop* TyIdRen Γ') Δ2)
        ≡⟨ sym (renTyCtx• (TyDrop TyIdRen) (TyDrop* TyIdRen Γ') Δ2) ⟩
      renTyCtx (TyDrop (TyIdRen • TyDrop* TyIdRen Γ')) Δ2
        ≡⟨ cong (λ x → renTyCtx (TyDrop x) Δ2) (Id• (TyDrop* TyIdRen Γ')) ⟩
      renTyCtx (TyDrop (TyDrop* TyIdRen Γ')) Δ2 ∎)
      ξ'
    where
    ξ' : Ren (κ ∷ Γ' ++ Γ) (renTyCtx (TyDrop TyIdRen) (renTyCtx (TyDrop* TyIdRen Γ') Δ1))
                            (renTyCtx (TyDrop TyIdRen) (renTyCtx (TyDrop* TyIdRen Γ') Δ2))     
    ξ' = KeepTy (KeepTy* ξ Γ')

  -- Variable renaming
  renVar : ∀{Γ Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Var Γ Δ1 t → Var Γ Δ2 t
  renVar (Keep ξ) V0 = V0
  renVar (Keep ξ) (VS x) = VS (renVar ξ x)
  renVar (Drop ξ) x = VS (renVar ξ x)

  -- Term renaming
  ren : ∀{Γ Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Tm Γ Δ1 t → Tm Γ Δ2 t
  renVec : ∀{Γ Δ1 Δ2 Θ} → Ren Γ Δ1 Δ2 → TmVec Γ Δ1 Θ → TmVec Γ Δ2 Θ

  ren ξ (var x) = var (renVar ξ x)
  ren ξ (constr c ts es) = constr c ts (renVec ξ es)
  
  renVec ξ [] = [] 
  renVec {Γ} {Δ1} {Δ2} {(Γ' , Δ' , t) ∷ Θ} ξ (e ∷ es) =
    ren (Keep* (KeepTy* ξ Γ') Δ') e ∷ renVec ξ es

  -- Rename the types in a variable
  renVarTy : ∀{Γ1 Γ2 Δ t} (ξ : TyRen Γ1 Γ2) → Var Γ1 Δ t → Var Γ2 (renTyCtx ξ Δ) (tyRen ξ t)
  renVarTy ξ V0 = V0 
  renVarTy ξ (VS x) = VS (renVarTy ξ x)

  -- Rename the types in a term
  renTy : ∀{Γ1 Γ2 Δ t} (ξ : TyRen Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (renTyCtx ξ Δ) (tyRen ξ t)
  renVecTy : ∀{Γ1 Γ2 Δ Θ} (ξ : TyRen Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (renTyCtx ξ Δ) (renBinders ξ Θ)

  renTy ξ (var x) = var (renVarTy ξ x)
  renTy {Γ1} {Γ2} {Δ} ξ (constr c ts es) =
    subst (Tm Γ2 (renTyCtx ξ Δ)) (renVecTmPos ξ ts)
      (constr c (tyRenVec ξ ts)
      (subst (TmVec Γ2 (renTyCtx ξ Δ))
        (sym (renVecCtxTmPos ξ ts)) (renVecTy ξ es)))
  
  renVecTy ξ [] = [] 
  renVecTy {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} ξ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (tyRen (TyKeep* ξ Γ') t)) eq (renTy (TyKeep* ξ Γ') e) ∷ renVecTy ξ es
    where
    eq : renTyCtx (TyKeep* ξ Γ') (Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') Δ) ≡
         renTyCtx (TyKeep* ξ Γ') Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') (renTyCtx ξ Δ)
    eq =
      renTyCtx (TyKeep* ξ Γ') (Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ renTyCtx++ Δ' (renTyCtx (TyDrop* TyIdRen Γ') Δ) ⟩
      renTyCtx (TyKeep* ξ Γ') Δ' ++ renTyCtx (TyKeep* ξ Γ') (renTyCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ cong (renTyCtx (TyKeep* ξ Γ') Δ' ++_) (
          renTyCtx (TyKeep* ξ Γ') (renTyCtx (TyDrop* TyIdRen Γ') Δ)
            ≡⟨ sym (renTyCtx• (TyKeep* ξ Γ') (TyDrop* TyIdRen Γ') Δ) ⟩
          renTyCtx (TyKeep* ξ Γ' • TyDrop* TyIdRen Γ') Δ
            ≡⟨ cong (flip renTyCtx Δ) (sym (TyKeep*•Drop* Γ')) ⟩
          renTyCtx (TyDrop* (ξ • TyIdRen) Γ') Δ
            ≡⟨ cong (λ x → renTyCtx (TyDrop* x Γ') Δ) (•Id ξ) ⟩
          renTyCtx (TyDrop* ξ Γ') Δ
            ≡⟨ cong (λ x → renTyCtx (TyDrop* x Γ') Δ) (sym (Id• ξ)) ⟩
          renTyCtx (TyDrop* (TyIdRen • ξ) Γ') Δ
            ≡⟨ cong (flip renTyCtx Δ) (TyDrop*• Γ') ⟩
          renTyCtx (TyDrop* TyIdRen Γ' • ξ) Δ
            ≡⟨ renTyCtx• (TyDrop* TyIdRen Γ') ξ Δ ⟩
          renTyCtx (TyDrop* TyIdRen Γ') (renTyCtx ξ Δ) ∎) ⟩
      renTyCtx (TyKeep* ξ Γ') Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') (renTyCtx ξ Δ) ∎

  ------------------
  -- SUBSTITUTION --
  ------------------

  data Sub (Γ : Ctx) : (Δ1 Δ2 : TyCtx Γ) → Set where
    ε : ∀{Δ} → Sub Γ [] Δ
    _▸_ : ∀{Δ1 Δ2 t} (σ : Sub Γ Δ1 Δ2) (e : Tm Γ Δ2 t) → Sub Γ (t ∷ Δ1) Δ2

  -- Rename the kind context of a substitution
  wkSub : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : TyRen Γ1 Γ2) → Sub Γ1 Δ1 Δ2 → Sub Γ2 (renTyCtx ξ Δ1) (renTyCtx ξ Δ2)
  wkSub ξ ε = ε
  wkSub ξ (σ ▸ e) = wkSub ξ σ ▸ renTy ξ e

  infixr 9 _•◦_ 
  _•◦_ : ∀{Γ Δ1 Δ2 Δ3} → Ren Γ Δ2 Δ3 → Sub Γ Δ1 Δ2 → Sub Γ Δ1 Δ3
  ξ •◦ ε = ε
  ξ •◦ (σ ▸ e) = (ξ •◦ σ) ▸ ren ξ e

  DropSub : ∀{Γ Δ1 Δ2 t} → Sub Γ Δ1 Δ2 → Sub Γ Δ1 (t ∷ Δ2)
  DropSub σ = Drop IdRen •◦ σ

  DropSub* : ∀{Γ Δ1 Δ2} → Sub Γ Δ1 Δ2 → ∀ Δ' → Sub Γ Δ1 (Δ' ++ Δ2)
  DropSub* σ [] = σ
  DropSub* σ (t ∷ Δ') = DropSub (DropSub* σ Δ')

  KeepSub : ∀{Γ Δ1 Δ2 t} → Sub Γ Δ1 Δ2 → Sub Γ (t ∷ Δ1) (t ∷ Δ2)
  KeepSub σ = DropSub σ ▸ var V0

  KeepSub* : ∀{Γ Δ1 Δ2} → Sub Γ Δ1 Δ2 → ∀ Δ' → Sub Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
  KeepSub* σ [] = σ
  KeepSub* σ (t ∷ Δ') = KeepSub (KeepSub* σ Δ')

  ι : ∀{Γ Δ1 Δ2} → Ren Γ Δ1 Δ2 → Sub Γ Δ1 Δ2
  ι ε = ε
  ι (Keep ξ) = KeepSub (ι ξ)
  ι (Drop ξ) = DropSub (ι ξ)

  IdSub : ∀{Γ Δ} → Sub Γ Δ Δ
  IdSub = ι IdRen

  -- Variable substitution
  subVar : ∀{Γ Δ1 Δ2 t} → Sub Γ Δ1 Δ2 → Var Γ Δ1 t → Tm Γ Δ2 t
  subVar (σ ▸ e) V0 = e
  subVar (σ ▸ e) (VS x) = subVar σ x
  
  -- Term substitution
  sub : ∀{Γ Δ1 Δ2 t} → Sub Γ Δ1 Δ2 → Tm Γ Δ1 t → Tm Γ Δ2 t
  subVec : ∀{Γ Δ1 Δ2 Θ} → Sub Γ Δ1 Δ2 → TmVec Γ Δ1 Θ → TmVec Γ Δ2 Θ

  sub σ (var x) = subVar σ x
  sub σ (constr c ts es) = constr c ts (subVec σ es)

  subVec σ [] = []
  subVec {Θ = (Γ' , Δ' , t) ∷ Θ} σ (e ∷ es) =
    sub (KeepSub* (wkSub (TyDrop* TyIdRen Γ') σ) Δ') e ∷ subVec σ es

  -- Substitute the types in a variable
  subVarTy : ∀{Γ1 Γ2 Δ t} (σ : TySub Γ1 Γ2) → Var Γ1 Δ t → Var Γ2 (subTyCtx σ Δ) (tySub σ t)
  subVarTy ξ V0 = V0
  subVarTy ξ (VS x) = VS (subVarTy ξ x)

  -- Substitute the types in a term
  subTy : ∀{Γ1 Γ2 Δ t} (σ : TySub Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (subTyCtx σ Δ) (tySub σ t)
  subVecTy : ∀{Γ1 Γ2 Δ Θ} (σ : TySub Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (subTyCtx σ Δ) (subBinders σ Θ)

  subTy σ (var x) = var (subVarTy σ x)
  subTy {Γ1} {Γ2} {Δ} {t} σ (constr c ts es) =
    subst (Tm Γ2 (subTyCtx σ Δ)) (subVecTmPos σ ts)
      (constr c (tySubVec σ ts)
      (subst (TmVec Γ2 (subTyCtx σ Δ))
        (sym (subVecCtxTmPos σ ts)) (subVecTy σ es)))

  subVecTy σ [] = [] 
  subVecTy {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} σ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (tySub (TyKeepSub* σ Γ') t)) eq (subTy (TyKeepSub* σ Γ') e) ∷ subVecTy σ es
    where
    eq : subTyCtx (TyKeepSub* σ Γ') (Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') Δ) ≡
         subTyCtx (TyKeepSub* σ Γ') Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') (subTyCtx σ Δ)
    eq =
      subTyCtx (TyKeepSub* σ Γ') (Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ subTyCtx++ Δ' (renTyCtx (TyDrop* TyIdRen Γ') Δ) ⟩
      subTyCtx (TyKeepSub* σ Γ') Δ' ++ subTyCtx (TyKeepSub* σ Γ') (renTyCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ cong (subTyCtx (TyKeepSub* σ Γ') Δ' ++_) (
          subTyCtx (TyKeepSub* σ Γ') (renTyCtx (TyDrop* TyIdRen Γ') Δ)
            ≡⟨ cong (subTyCtx (TyKeepSub* σ Γ')) (sym (subTyCtxι (TyDrop* TyIdRen Γ') Δ)) ⟩
          subTyCtx (TyKeepSub* σ Γ') (subTyCtx (ιₜ (TyDrop* TyIdRen Γ')) Δ)
            ≡⟨ sym (subTyCtx◦ (TyKeepSub* σ Γ') (ιₜ (TyDrop* TyIdRen Γ')) Δ) ⟩
          subTyCtx (TyKeepSub* σ Γ' ◦ ιₜ (TyDrop* TyIdRen Γ')) Δ
            ≡⟨ cong (flip subTyCtx Δ) (
              TyKeepSub* σ Γ' ◦ ιₜ (TyDrop* TyIdRen Γ')
                ≡⟨ cong (TyKeepSub* σ Γ' ◦_) (sym (TyDrop*ι TyIdRen Γ')) ⟩
              TyKeepSub* σ Γ' ◦ TyDropSub* TyIdSub Γ'
                ≡⟨ sym (TyKeep*◦Drop* σ TyIdSub Γ') ⟩
              TyDropSub* (σ ◦ TyIdSub) Γ'
                ≡⟨ cong (flip TyDropSub* Γ') (◦Id σ) ⟩
              TyDropSub* σ Γ'
                ≡⟨ cong (flip TyDropSub* Γ') (sym (Id◦ σ)) ⟩
              TyDropSub* (TyIdSub ◦ σ) Γ'
                ≡⟨ TyDrop*◦ TyIdSub σ Γ' ⟩
              TyDropSub* TyIdSub Γ' ◦ σ
                ≡⟨ cong (_◦ σ) (TyDrop*ι TyIdRen Γ') ⟩
              ιₜ (TyDrop* TyIdRen Γ') ◦ σ ∎) ⟩
          subTyCtx (ιₜ (TyDrop* TyIdRen Γ') ◦ σ) Δ
            ≡⟨ subTyCtx◦ (ιₜ (TyDrop* TyIdRen Γ')) σ Δ ⟩
          subTyCtx (ιₜ (TyDrop* TyIdRen Γ')) (subTyCtx σ Δ)
            ≡⟨ subTyCtxι (TyDrop* TyIdRen Γ') (subTyCtx σ Δ) ⟩
          renTyCtx (TyDrop* TyIdRen Γ') (subTyCtx σ Δ) ∎) ⟩
      subTyCtx (TyKeepSub* σ Γ') Δ' ++ renTyCtx (TyDrop* TyIdRen Γ') (subTyCtx σ Δ) ∎
 