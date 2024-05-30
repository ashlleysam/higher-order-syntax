{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import SecondOrderContexts

module ThirdOrderSignatures where

-- A third-order binding signature
record ThirdOrderSignature : Set₁ where
  field
    
    -- Second order signature that this signature depends on
    {{⅀₂}} : SecondOrderSignature

  -- Aliasing definitions that depend on ⅀₂
  KndCtx'      = SecondOrderContexts.KndCtx      ⅀₂
  Ctx'         = SecondOrderContexts.Ctx         ⅀₂
  TyVec'       = SecondOrderContexts.TyVec       ⅀₂
  Typ'         = SecondOrderContexts.Typ         ⅀₂
  TyRen'       = SecondOrderContexts.TyRen       ⅀₂
  tyRen'       = SecondOrderContexts.tyRen       ⅀₂
  tyRenVec'    = SecondOrderContexts.tyRenVec    ⅀₂
  renBinders'  = SecondOrderContexts.renBinders  ⅀₂
  TySub'       = SecondOrderContexts.TySub       ⅀₂
  tySub'       = SecondOrderContexts.tySub       ⅀₂
  subTyp'      = SecondOrderContexts.subTyp      ⅀₂
  renTyp'      = SecondOrderContexts.renTyp      ⅀₂
  subTypι'     = SecondOrderContexts.subTypι     ⅀₂
  tySubVec'    = SecondOrderContexts.tySubVec    ⅀₂
  subBinders'  = SecondOrderContexts.subBinders  ⅀₂
  ιₜ'          = SecondOrderContexts.ιₜ          ⅀₂
  subι'        = SecondOrderContexts.subι        ⅀₂
  subVecι'     = SecondOrderContexts.subVecι     ⅀₂
  subBindersι' = SecondOrderContexts.subBindersι ⅀₂


  field
    
    -- Term constructor shape
    Shape : Set

    -- Type part of constructor signature
    TmTyPos : Shape → List (List (⅀₂ .Knd) × ⅀₂ .Knd)

    -- Term part of constructor signature, which depends on the type part
    TmPos : (s : Shape) (Γ : KndCtx') (ts : TyVec' Γ (TmTyPos s)) → List (Binder ⅀₂ Γ) × Typ' Γ

    {-
    Coherence requirements

    Essentially guarantees that the arguments Γ and ts in the
    term part of the constructor signature is used uniformly
    -}
    subVecTmPos : ∀{Γ1 Γ2} (s : Shape) (σ : TySub' Γ1 Γ2) (ts : TyVec' Γ1 (TmTyPos s)) →
                  TmPos s Γ2 (tySubVec' σ ts) .snd ≡ subTyp' σ (TmPos s Γ1 ts .snd)

    subVecKndCtxTmPos : ∀{Γ1 Γ2} (s : Shape) (σ : TySub' Γ1 Γ2) (ts : TyVec' Γ1 (TmTyPos s)) →
                        TmPos s Γ2 (tySubVec' σ ts) .fst ≡ subBinders' σ (TmPos s Γ1 ts .fst)

  -- Derived coherence requirements for renaming
  renVecTmPos : ∀{Γ1 Γ2 s} (ξ : TyRen' Γ1 Γ2) (ts : TyVec' Γ1 (TmTyPos s)) →
                TmPos s Γ2 (tyRenVec' ξ ts) .snd ≡ renTyp' ξ (TmPos s Γ1 ts .snd)
  renVecTmPos {Γ1} {Γ2} {s} ξ ts =
    TmPos s Γ2 (tyRenVec' ξ ts) .snd
      ≡⟨ sym (cong (λ x → TmPos s Γ2 x .snd) (subVecι' ξ ts)) ⟩
    TmPos s Γ2 (tySubVec' (ιₜ' ξ) ts) .snd
      ≡⟨ subVecTmPos s (ιₜ' ξ) ts ⟩
    subTyp' (ιₜ' ξ) (TmPos s Γ1 ts .snd)
      ≡⟨ subTypι' ξ  (TmPos s Γ1 ts .snd) ⟩
    renTyp' ξ (TmPos s Γ1 ts .snd) ∎

  renVecKndCtxTmPos : ∀{Γ1 Γ2 s} (ξ : TyRen' Γ1 Γ2) (ts : TyVec' Γ1 (TmTyPos s)) →
                  TmPos s Γ2 (tyRenVec' ξ ts) .fst ≡ renBinders' ξ (TmPos s Γ1 ts .fst)
  renVecKndCtxTmPos {Γ1} {Γ2} {s} ξ ts =
    TmPos s Γ2 (tyRenVec' ξ ts) .fst
      ≡⟨ cong (λ x → TmPos s Γ2 x .fst) (sym (subVecι' ξ ts)) ⟩
    TmPos s Γ2 (tySubVec' (ιₜ' ξ) ts) .fst
      ≡⟨ subVecKndCtxTmPos s (ιₜ' ξ) ts ⟩
    subBinders' (ιₜ' ξ) (TmPos s Γ1 ts .fst)
      ≡⟨ subBindersι' ξ (TmPos s Γ1 ts .fst) ⟩
    renBinders' ξ (TmPos s Γ1 ts .fst) ∎

open ThirdOrderSignature public