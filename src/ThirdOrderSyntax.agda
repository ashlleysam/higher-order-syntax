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
            subVar to tySubVar; sub to tySub; Ctx to KndCtx; MCtx to MKndCtx)

-- Types of * kind
Typ : KndCtx → Set
Typ Γ = Ty Γ *

-- Typing contexts and their various operations
Ctx : KndCtx → Set
Ctx Γ = List (Typ Γ)

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
          renCtx (ξ1 • ξ2) ≈ renCtx ξ1 ∘ renCtx ξ2
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
           subCtx (σ1 ◦ σ2) ≈ subCtx σ1 ∘ subCtx σ2
subCtx◦ σ1 σ2 [] = refl
subCtx◦ σ1 σ2 (t ∷ Δ) = cong₂ _∷_ (sub◦ σ1 σ2 t) (subCtx◦ σ1 σ2 Δ)

subCtxι : ∀{Γ1 Γ2} (ξ : TyRen Γ1 Γ2) →
           subCtx (ιₜ ξ) ≈ renCtx ξ
subCtxι ξ [] = refl
subCtxι ξ (t ∷ Δ) = cong₂ _∷_ (subι ξ t) (subCtxι ξ Δ)

Binder : KndCtx → Set
Binder Γ = Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ (Γ' ++ Γ))

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

module Syntax1
  -- Term constructor shape
  (Shape : Set)
  -- Type part of constructor signature
  (TmTyPos : Shape → List (KndCtx × Knd))
  -- Term part of constructor signature, which depends on the type part
  (TmPos : (s : Shape) (Γ : KndCtx) → TyVec Γ (TmTyPos s) → List (Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ (Γ' ++ Γ))) × Typ Γ)
  -- Coherence requirements
  (subVecTmPos : ∀{Γ1 Γ2 c} (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos c)) →
                TmPos c Γ2 (tySubVec σ ts) .snd ≡ tySub σ (TmPos c Γ1 ts .snd))
  (subVecKndCtxTmPos : ∀{Γ1 Γ2 c} (σ : TySub Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos c)) →
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

  renVecKndCtxTmPos : ∀{Γ1 Γ2 s} (ξ : TyRen Γ1 Γ2) (ts : TyVec Γ1 (TmTyPos s)) →
                  TmPos s Γ2 (tyRenVec ξ ts) .fst ≡ renBinders ξ (TmPos s Γ1 ts .fst)
  renVecKndCtxTmPos {Γ1} {Γ2} {s} ξ ts =
    TmPos s Γ2 (tyRenVec ξ ts) .fst
      ≡⟨ cong (λ x → TmPos s Γ2 x .fst) (sym (subVecι ξ ts)) ⟩
    TmPos s Γ2 (tySubVec (ιₜ ξ) ts) .fst
      ≡⟨ subVecKndCtxTmPos (ιₜ ξ) ts ⟩
    subBinders (ιₜ ξ) (TmPos s Γ1 ts .fst)
      ≡⟨ subBindersι ξ (TmPos s Γ1 ts .fst) ⟩
    renBinders ξ (TmPos s Γ1 ts .fst) ∎

  -- In-context variables
  data Var : (Γ : KndCtx) (Δ : Ctx Γ) → Typ Γ → Set where
    V0 : ∀{Γ Δ} {t : Typ Γ} → Var Γ (t ∷ Δ) t
    VS : ∀{Γ Δ} {t s : Typ Γ} → Var Γ Δ t → Var Γ (s ∷ Δ) t

  data Tm (Γ : KndCtx) (Δ : Ctx Γ) : Typ Γ → Set
  data TmVec (Γ : KndCtx) (Δ : Ctx Γ) : List (Σ[ Γ' ∈ KndCtx ] (Ctx (Γ' ++ Γ) × Typ (Γ' ++ Γ))) → Set

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
    _∷_ : ∀{Γ' t Θ} {Δ' : Ctx (Γ' ++ Γ)} →
          (e : Tm (Γ' ++ Γ) (Δ' ++ renCtx (TyDrop* TyIdRen Γ') Δ) t) →
          (es : TmVec Γ Δ Θ) →
          TmVec Γ Δ (((Γ' , Δ' , t)) ∷ Θ)

  --------------
  -- RENAMING --
  --------------

  data Ren (Γ : KndCtx) : (Δ1 Δ2 : Ctx Γ) → Set where
    ε : Ren Γ [] []
    Keep : ∀{Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Ren Γ (t ∷ Δ1) (t ∷ Δ2)
    Drop : ∀{Δ1 Δ2 t} → Ren Γ Δ1 Δ2 → Ren Γ Δ1 (t ∷ Δ2)

  -- Rename the kind context of a renaming
  wkRen : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : TyRen Γ1 Γ2) → Ren Γ1 Δ1 Δ2 → Ren Γ2 (renCtx ξ Δ1) (renCtx ξ Δ2)
  wkRen ξ1 ε = ε
  wkRen ξ1 (Keep ξ2) = Keep (wkRen ξ1 ξ2)
  wkRen ξ1 (Drop ξ2) = Drop (wkRen ξ1 ξ2)

  IdRen : ∀{Γ Δ} → Ren Γ Δ Δ
  IdRen {Δ = []} = ε 
  IdRen {Δ = t ∷ Δ} = Keep IdRen

  Keep* : ∀{Γ Δ1 Δ2} → Ren Γ Δ1 Δ2 → ∀ Δ' → Ren Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
  Keep* ξ [] = ξ
  Keep* ξ (t ∷ Δ') = Keep (Keep* ξ Δ')

  KeepTy : ∀{Γ Δ1 Δ2 κ} → Ren Γ Δ1 Δ2 → Ren (κ ∷ Γ) (renCtx (TyDrop TyIdRen) Δ1) (renCtx (TyDrop TyIdRen) Δ2)
  KeepTy ε = ε
  KeepTy (Keep ξ) = Keep (KeepTy ξ)
  KeepTy (Drop ξ) = Drop (KeepTy ξ)

  KeepTy* : ∀{Γ Δ1 Δ2} → Ren Γ Δ1 Δ2 → ∀ Γ' → Ren (Γ' ++ Γ) (renCtx (TyDrop* TyIdRen Γ') Δ1) (renCtx (TyDrop* TyIdRen Γ') Δ2)
  KeepTy* {Γ} {Δ1} {Δ2} ξ [] = subst₂ (Ren Γ) (sym (renCtxId Δ1)) (sym (renCtxId Δ2)) ξ
  KeepTy* {Γ} {Δ1} {Δ2} ξ (κ ∷ Γ') = 
    subst₂ (Ren (κ ∷ Γ' ++ Γ))
      (renCtx (TyDrop TyIdRen) (renCtx (TyDrop* TyIdRen Γ') Δ1)
        ≡⟨ sym (renCtx• (TyDrop TyIdRen) (TyDrop* TyIdRen Γ') Δ1) ⟩
      renCtx (TyDrop (TyIdRen • TyDrop* TyIdRen Γ')) Δ1
        ≡⟨ cong (λ x → renCtx (TyDrop x) Δ1) (Id• (TyDrop* TyIdRen Γ')) ⟩
      renCtx (TyDrop (TyDrop* TyIdRen Γ')) Δ1 ∎)
      (renCtx (TyDrop TyIdRen) (renCtx (TyDrop* TyIdRen Γ') Δ2)
        ≡⟨ sym (renCtx• (TyDrop TyIdRen) (TyDrop* TyIdRen Γ') Δ2) ⟩
      renCtx (TyDrop (TyIdRen • TyDrop* TyIdRen Γ')) Δ2
        ≡⟨ cong (λ x → renCtx (TyDrop x) Δ2) (Id• (TyDrop* TyIdRen Γ')) ⟩
      renCtx (TyDrop (TyDrop* TyIdRen Γ')) Δ2 ∎)
      ξ'
    where
    ξ' : Ren (κ ∷ Γ' ++ Γ) (renCtx (TyDrop TyIdRen) (renCtx (TyDrop* TyIdRen Γ') Δ1))
                            (renCtx (TyDrop TyIdRen) (renCtx (TyDrop* TyIdRen Γ') Δ2))     
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
  renVarTy : ∀{Γ1 Γ2 Δ t} (ξ : TyRen Γ1 Γ2) → Var Γ1 Δ t → Var Γ2 (renCtx ξ Δ) (tyRen ξ t)
  renVarTy ξ V0 = V0 
  renVarTy ξ (VS x) = VS (renVarTy ξ x)

  -- Rename the types in a term
  renTy : ∀{Γ1 Γ2 Δ t} (ξ : TyRen Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (renCtx ξ Δ) (tyRen ξ t)
  renVecTy : ∀{Γ1 Γ2 Δ Θ} (ξ : TyRen Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (renCtx ξ Δ) (renBinders ξ Θ)

  renTy ξ (var x) = var (renVarTy ξ x)
  renTy {Γ1} {Γ2} {Δ} ξ (constr c ts es) =
    subst (Tm Γ2 (renCtx ξ Δ)) (renVecTmPos ξ ts)
      (constr c (tyRenVec ξ ts)
      (subst (TmVec Γ2 (renCtx ξ Δ))
        (sym (renVecKndCtxTmPos ξ ts)) (renVecTy ξ es)))
  
  renVecTy ξ [] = [] 
  renVecTy {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} ξ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (tyRen (TyKeep* ξ Γ') t)) eq (renTy (TyKeep* ξ Γ') e) ∷ renVecTy ξ es
    where
    eq : renCtx (TyKeep* ξ Γ') (Δ' ++ renCtx (TyDrop* TyIdRen Γ') Δ) ≡
         renCtx (TyKeep* ξ Γ') Δ' ++ renCtx (TyDrop* TyIdRen Γ') (renCtx ξ Δ)
    eq =
      renCtx (TyKeep* ξ Γ') (Δ' ++ renCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ renCtx++ Δ' (renCtx (TyDrop* TyIdRen Γ') Δ) ⟩
      renCtx (TyKeep* ξ Γ') Δ' ++ renCtx (TyKeep* ξ Γ') (renCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ cong (renCtx (TyKeep* ξ Γ') Δ' ++_) (
          renCtx (TyKeep* ξ Γ') (renCtx (TyDrop* TyIdRen Γ') Δ)
            ≡⟨ sym (renCtx• (TyKeep* ξ Γ') (TyDrop* TyIdRen Γ') Δ) ⟩
          renCtx (TyKeep* ξ Γ' • TyDrop* TyIdRen Γ') Δ
            ≡⟨ cong (flip renCtx Δ) (sym (TyKeep*•Drop* Γ')) ⟩
          renCtx (TyDrop* (ξ • TyIdRen) Γ') Δ
            ≡⟨ cong (λ x → renCtx (TyDrop* x Γ') Δ) (•Id ξ) ⟩
          renCtx (TyDrop* ξ Γ') Δ
            ≡⟨ cong (λ x → renCtx (TyDrop* x Γ') Δ) (sym (Id• ξ)) ⟩
          renCtx (TyDrop* (TyIdRen • ξ) Γ') Δ
            ≡⟨ cong (flip renCtx Δ) (TyDrop*• Γ') ⟩
          renCtx (TyDrop* TyIdRen Γ' • ξ) Δ
            ≡⟨ renCtx• (TyDrop* TyIdRen Γ') ξ Δ ⟩
          renCtx (TyDrop* TyIdRen Γ') (renCtx ξ Δ) ∎) ⟩
      renCtx (TyKeep* ξ Γ') Δ' ++ renCtx (TyDrop* TyIdRen Γ') (renCtx ξ Δ) ∎

  ------------------
  -- SUBSTITUTION --
  ------------------

  data Sub (Γ : KndCtx) : (Δ1 Δ2 : Ctx Γ) → Set where
    ε : ∀{Δ} → Sub Γ [] Δ
    _▸_ : ∀{Δ1 Δ2 t} (σ : Sub Γ Δ1 Δ2) (e : Tm Γ Δ2 t) → Sub Γ (t ∷ Δ1) Δ2

  -- Rename the kind context of a substitution
  wkSub : ∀{Γ1 Γ2 Δ1 Δ2} (ξ : TyRen Γ1 Γ2) → Sub Γ1 Δ1 Δ2 → Sub Γ2 (renCtx ξ Δ1) (renCtx ξ Δ2)
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
  subVarTy : ∀{Γ1 Γ2 Δ t} (σ : TySub Γ1 Γ2) → Var Γ1 Δ t → Var Γ2 (subCtx σ Δ) (tySub σ t)
  subVarTy ξ V0 = V0
  subVarTy ξ (VS x) = VS (subVarTy ξ x)

  -- Substitute the types in a term
  subTy : ∀{Γ1 Γ2 Δ t} (σ : TySub Γ1 Γ2) → Tm Γ1 Δ t → Tm Γ2 (subCtx σ Δ) (tySub σ t)
  subVecTy : ∀{Γ1 Γ2 Δ Θ} (σ : TySub Γ1 Γ2) → TmVec Γ1 Δ Θ → TmVec Γ2 (subCtx σ Δ) (subBinders σ Θ)

  subTy σ (var x) = var (subVarTy σ x)
  subTy {Γ1} {Γ2} {Δ} {t} σ (constr c ts es) =
    subst (Tm Γ2 (subCtx σ Δ)) (subVecTmPos σ ts)
      (constr c (tySubVec σ ts)
      (subst (TmVec Γ2 (subCtx σ Δ))
        (sym (subVecKndCtxTmPos σ ts)) (subVecTy σ es)))

  subVecTy σ [] = [] 
  subVecTy {Γ1} {Γ2} {Δ} {(Γ' , Δ' , t) ∷ Θ} σ (e ∷ es) =
    subst (λ x → Tm (Γ' ++ Γ2) x (tySub (TyKeepSub* σ Γ') t)) eq (subTy (TyKeepSub* σ Γ') e) ∷ subVecTy σ es
    where
    eq : subCtx (TyKeepSub* σ Γ') (Δ' ++ renCtx (TyDrop* TyIdRen Γ') Δ) ≡
         subCtx (TyKeepSub* σ Γ') Δ' ++ renCtx (TyDrop* TyIdRen Γ') (subCtx σ Δ)
    eq =
      subCtx (TyKeepSub* σ Γ') (Δ' ++ renCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ subCtx++ Δ' (renCtx (TyDrop* TyIdRen Γ') Δ) ⟩
      subCtx (TyKeepSub* σ Γ') Δ' ++ subCtx (TyKeepSub* σ Γ') (renCtx (TyDrop* TyIdRen Γ') Δ)
        ≡⟨ cong (subCtx (TyKeepSub* σ Γ') Δ' ++_) (
          subCtx (TyKeepSub* σ Γ') (renCtx (TyDrop* TyIdRen Γ') Δ)
            ≡⟨ cong (subCtx (TyKeepSub* σ Γ')) (sym (subCtxι (TyDrop* TyIdRen Γ') Δ)) ⟩
          subCtx (TyKeepSub* σ Γ') (subCtx (ιₜ (TyDrop* TyIdRen Γ')) Δ)
            ≡⟨ sym (subCtx◦ (TyKeepSub* σ Γ') (ιₜ (TyDrop* TyIdRen Γ')) Δ) ⟩
          subCtx (TyKeepSub* σ Γ' ◦ ιₜ (TyDrop* TyIdRen Γ')) Δ
            ≡⟨ cong (flip subCtx Δ) (
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
          subCtx (ιₜ (TyDrop* TyIdRen Γ') ◦ σ) Δ
            ≡⟨ subCtx◦ (ιₜ (TyDrop* TyIdRen Γ')) σ Δ ⟩
          subCtx (ιₜ (TyDrop* TyIdRen Γ')) (subCtx σ Δ)
            ≡⟨ subCtxι (TyDrop* TyIdRen Γ') (subCtx σ Δ) ⟩
          renCtx (TyDrop* TyIdRen Γ') (subCtx σ Δ) ∎) ⟩
      subCtx (TyKeepSub* σ Γ') Δ' ++ renCtx (TyDrop* TyIdRen Γ') (subCtx σ Δ) ∎
 