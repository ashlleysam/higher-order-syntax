{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import SecondOrderContexts
open import ThirdOrderSignatures

module ThirdOrderSignaturesMetavars where

-- A third-order binding signature using metavariables
record MThirdOrderSignature : Set₁ where
  field
    -- Second order signature that this signature depends on
    M⅀₂ : SecondOrderSignature
  
    -- Term constructor shape
    MShape : Set

    -- Type part of constructor signature
    MTmTyPos : MShape → List (List (M⅀₂ .Knd) × M⅀₂ .Knd)

    -- Term part of constructor signature, which depends on the type part
    -- MTmPos : (s : MShape) →
    --           List (MBinder M⅀₂ (MTmTyPos s))
    --           × (Σ[ κ ∈ M⅀₂ .Knd ] MTm M⅀₂ (MTmTyPos s) ([] , κ))
    MTmPos : (s : MShape) →
              List (Binder M⅀₂ {! Binder  !})
              × (Σ[ κ ∈ M⅀₂ .Knd ] Ty M⅀₂ {!   !} κ)

{-
* : Knd

∀ [*]* : *
_⇒_ * * : *

λ (s t : *) [s]t : s ⇒ t
app (s t : *) (s ⇒ t) s : t
Λ (t : [*]*) [*]t : ∀ t
App (t : [*]*) (∀ t) (s : *) : t⟨s⟩

List (List (M⅀₂ .Knd) × M⅀₂ .Knd) → List (M⅀₂ .Knd)

  -- Derived typing function for a standard signature
  ⟦TmPos⟧ : (s : MShape) (Γ : KndCtx M⅀₂) (ts : TyVec M⅀₂ Γ (MTmTyPos s)) →
              List (Binder M⅀₂ Γ) × Typ M⅀₂ Γ
  ⟦TmPos⟧ s Γ ts =
    map (interpBinders M⅀₂ Γ ts) (MTmPos s .fst) ,
    MTmPos s .snd .fst ,
    interpTm M⅀₂ (MTmPos s .snd .snd) ts (TyIdSub M⅀₂)

  -- Derived coherence conditions for a standard signature
  ⟦subVecPos⟧ : ∀{Γ1 Γ2} (s : MShape) (σ : TySub M⅀₂ Γ1 Γ2) (ts : TyVec M⅀₂ Γ1 (MTmTyPos s)) →
                ⟦TmPos⟧ s Γ2 (tySubVec M⅀₂ σ ts) .snd ≡ subTyp M⅀₂ σ (⟦TmPos⟧ s Γ1 ts .snd)
  ⟦subVecPos⟧ {Γ1} {Γ2} s σ ts =
    Σ-≡-→-≡-Σ
      refl
      (interpTmSub M⅀₂ (MTmPos s .snd .snd) ts σ
        (TyIdSub M⅀₂) (TyIdSub M⅀₂)
        (Id◦ M⅀₂ σ ∙ sym (◦Id M⅀₂ σ)))

  ⟦subVecKndCtxTmPos⟧ : ∀{Γ1 Γ2} (s : MShape) (σ : TySub M⅀₂ Γ1 Γ2) (ts : TyVec M⅀₂ Γ1 (MTmTyPos s)) →
                        ⟦TmPos⟧ s Γ2 (tySubVec M⅀₂ σ ts) .fst ≡ subBinders M⅀₂ σ (⟦TmPos⟧ s Γ1 ts .fst)
  ⟦subVecKndCtxTmPos⟧ {Γ1} {Γ2} s σ ts =
    map (interpBinders M⅀₂ Γ2 (tySubVec M⅀₂ σ ts)) (MTmPos s .fst)
      ≡⟨ map-cong (interpBinders∘subVec M⅀₂ σ ts) (MTmPos s .fst) ⟩
    map (subBinder M⅀₂ σ ∘ interpBinders M⅀₂ Γ1 ts) (MTmPos s .fst)
      ≡⟨ map-compose (MTmPos s .fst) ⟩
    map (subBinder M⅀₂ σ) (map (interpBinders M⅀₂ Γ1 ts) (MTmPos s .fst)) ∎

  -- The resultant third order signature
  toSig : ThirdOrderSignature
  ⅀₂ toSig = M⅀₂ 
  Shape toSig = MShape
  TmTyPos toSig = MTmTyPos
  TmPos toSig = ⟦TmPos⟧
  subVecTmPos toSig = ⟦subVecPos⟧
  subVecKndCtxTmPos toSig = ⟦subVecKndCtxTmPos⟧

open MThirdOrderSignature public
-}