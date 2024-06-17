{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import KindSignatures
open import Types
open import TypeContexts
open import Kinding

module TypeSignatures where

-- A typing signature
record TypeSignature : Set₁ where
  field
    -- Kinding order signature that this signature depends on
    ⅀ₖ : KindSignature

    -- Term constructor symbols
    TmSymb : Set

    -- Type part of constructor signature
    TmTySig : (s : TmSymb) → List (List (⅀ₖ .Knd) × ⅀ₖ .Knd)

    -- Term part of constructor signature, which depends on the type part
    TmSig : (s : TmSymb) (Γ : List (⅀ₖ .Knd)) (ts : TyVec ⅀ₖ) → Binders ⅀ₖ × Typ ⅀ₖ
    ⊢TmSig-fst : ∀{Γ ts} (s : TmSymb) →
                  vecKinded ⅀ₖ Γ ts (TmTySig s) →
                  wfBinders ⅀ₖ Γ (TmSig s Γ ts .fst)
    ⊢TmSig-snd : ∀{Γ ts} (s : TmSymb) →
                  vecKinded ⅀ₖ Γ ts (TmTySig s) →
                  wfTyp ⅀ₖ Γ (TmSig s Γ ts .snd)
  
    {-
    Coherence requirements

    Essentially guarantees that the arguments Γ and ts in the
    term part of the constructor signature are used uniformly, i.e.
    so that no exotic terms are used
    -}
    sub-comm-TmSig-snd : ∀{Γ1 Γ2 σ ts} (s : TmSymb) →
                         TYSUB ⅀ₖ σ Γ1 Γ2 →
                         vecKinded ⅀ₖ Γ1 ts (TmTySig s) →
                         TmSig s Γ2 (subTyVec ⅀ₖ σ ts) .snd ≡
                         subTyp ⅀ₖ σ (TmSig s Γ1 ts .snd)

    sub-comm-TmSig-fst : ∀{Γ1 Γ2 σ ts} (s : TmSymb) →
                         TYSUB ⅀ₖ σ Γ1 Γ2 →
                         vecKinded ⅀ₖ Γ1 ts (TmTySig s) →
                         TmSig s Γ2 (subTyVec ⅀ₖ σ ts) .fst ≡
                         subBinders ⅀ₖ σ (TmSig s Γ1 ts .fst)

   -- Derived coherence requirements for renaming
  ren-comm-TmSig-snd : ∀{Γ1 Γ2 ξ ts} (s : TmSymb) →
                        TYREN ⅀ₖ ξ Γ1 Γ2 →
                        vecKinded ⅀ₖ Γ1 ts (TmTySig s) →
                        TmSig s Γ2 (renTyVec ⅀ₖ ξ ts) .snd ≡
                        renTyp ⅀ₖ ξ (TmSig s Γ1 ts .snd)
  ren-comm-TmSig-snd {Γ1} {Γ2} {ξ} {ts} s ⊢ξ ⊢ts =
    TmSig s Γ2 (renTyVec ⅀ₖ ξ ts) .snd
      ≡⟨ cong (λ x → TmSig s Γ2 x .snd) (sym $ subTyVecιₜ ⅀ₖ ξ ts) ⟩
    TmSig s Γ2 (subTyVec ⅀ₖ (ιₜ ⅀ₖ ξ) ts) .snd
      ≡⟨ sub-comm-TmSig-snd s (⊢ιₜ ⅀ₖ ⊢ξ) ⊢ts ⟩
    subTyp ⅀ₖ (ιₜ ⅀ₖ ξ) (TmSig s Γ1 ts .snd)
      ≡⟨ subTypιₜ ⅀ₖ ξ (TmSig s Γ1 ts .snd) ⟩
    renTyp ⅀ₖ ξ (TmSig s Γ1 ts .snd) ∎

  ren-comm-TmSig-fst : ∀{Γ1 Γ2 ξ ts} (s : TmSymb) →
                        TYREN ⅀ₖ ξ Γ1 Γ2 →
                        vecKinded ⅀ₖ Γ1 ts (TmTySig s) →
                        TmSig s Γ2 (renTyVec ⅀ₖ ξ ts) .fst ≡
                        renBinders ⅀ₖ ξ (TmSig s Γ1 ts .fst)
  ren-comm-TmSig-fst {Γ1} {Γ2} {ξ} {ts} s ⊢ξ ⊢ts =
    TmSig s Γ2 (renTyVec ⅀ₖ ξ ts) .fst
      ≡⟨ (cong (λ x → TmSig s Γ2 x .fst) $ sym $ subTyVecιₜ ⅀ₖ ξ ts) ⟩
    TmSig s Γ2 (subTyVec ⅀ₖ (ιₜ ⅀ₖ ξ) ts) .fst
      ≡⟨ sub-comm-TmSig-fst s (⊢ιₜ ⅀ₖ ⊢ξ) ⊢ts ⟩
    subBinders ⅀ₖ (ιₜ ⅀ₖ ξ) (TmSig s Γ1 ts .fst)
      ≡⟨ subBindersιₜ ⅀ₖ ξ (TmSig s Γ1 ts .fst) ⟩
    renBinders ⅀ₖ ξ (TmSig s Γ1 ts .fst) ∎

open TypeSignature public 