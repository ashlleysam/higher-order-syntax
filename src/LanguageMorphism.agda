{-# OPTIONS --safe #-}

open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import SecondOrderSignatures
open import SecondOrderLanguage
open import SecondOrderLanguageUntyped

module LanguageMorphism where

-- Morphisms between contexts and kinds
record CtxMor (⅀1 ⅀2 : SecondOrderSignature) : Set where
  field
    -- How contexts are mapped under the morphism
    α : List (⅀1 .Knd) → List (⅀2 .Knd)
    -- How kinds are mapped under the morphism
    β : ⅀1 .Knd → ⅀2 .Knd
    -- The context mapping respects concatenation
    α-++ : ∀ Γ1 Γ2 → α (Γ1 ++ Γ2) ≡ α Γ1 ++ α Γ2
  
open CtxMor public

-- Morphisms between the languages of signatures
record LangMor (⅀1 ⅀2 : SecondOrderSignature) (M : CtxMor ⅀1 ⅀2) : Set where
  field
    -- How constructors are mapped under the morphism
    γ : ⅀1 .TyShape → ⅀2 .TyShape
    -- Constructor types are respected
    Pos∘γ≗β∘Pos : snd ∘ ⅀2 .TyPos ∘ γ ≗ M .β ∘ snd ∘ ⅀1 .TyPos
    -- Constructor argument types are respected
    ⟨α,β⟩∘Pos≗Pos∘γ : map (λ { (Δ , κ) → M .α Δ , M .β κ }) ∘ (fst ∘ ⅀1 .TyPos) ≗ fst ∘ ⅀2 .TyPos ∘ γ
    -- How the morphism acts on variables
    mor-var : ∀{Γ κ} → Var ⅀1 Γ κ → Tm ⅀2 (M .α Γ) (M .β κ)

  -- The definition of the morphism
  mor : ∀{Γ κ} → Tm ⅀1 Γ κ → Tm ⅀2 (M .α Γ) (M .β κ)
  mor-vec : ∀{Γ Σ} → TmVec ⅀1 Γ Σ → TmVec ⅀2 (M .α Γ) (map (λ{ (Δ , κ) → M .α Δ , M .β κ }) Σ)

  -- Variables act as specified
  mor (var x) = mor-var x
  -- Use γ to replace the constructor
  mor {Γ} (constr s ts) =
    subst (Tm ⅀2 (M .α Γ)) (Pos∘γ≗β∘Pos s) (
      constr (γ s) (
        subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ s) (
          mor-vec ts)))

  -- The morphism acts homomorphically on lists
  mor-vec [] = []
  mor-vec {Γ} {(Δ , κ) ∷ Σ} (t ∷ ts) =
    subst (flip (Tm ⅀2) (M .β κ)) (M .α-++ Δ Γ) (mor t)
    ∷ mor-vec ts

open LangMor public

-- To prove two morphisms over the same context and kind
-- morphism are equivalent, it suffices to prove that
-- they are equivalent on variables and constructors
LangMor≡ : {⅀1 ⅀2 : SecondOrderSignature} {M : CtxMor ⅀1 ⅀2}
           (𝕄1 𝕄2 : LangMor ⅀1 ⅀2 M) →
           𝕄1 .γ ≗ 𝕄2 .γ →
           (∀{Γ κ} (x : Var ⅀1 Γ κ) → 𝕄1 .mor-var x ≡ 𝕄2 .mor-var x) →
           ∀{Γ κ} (e : Tm ⅀1 Γ κ) → mor 𝕄1 e ≡ mor 𝕄2 e
LangMorVec≡ : {⅀1 ⅀2 : SecondOrderSignature} {M : CtxMor ⅀1 ⅀2}
              (𝕄1 𝕄2 : LangMor ⅀1 ⅀2 M) →
              𝕄1 .γ ≗ 𝕄2 .γ →
              (∀{Γ κ} (x : Var ⅀1 Γ κ) → 𝕄1 .mor-var x ≡ 𝕄2 .mor-var x) →
              ∀{Γ Σ} (es : TmVec ⅀1 Γ Σ) → mor-vec 𝕄1 es ≡ mor-vec 𝕄2 es

LangMor≡ 𝕄1 𝕄2 p q (var x) = q x
LangMor≡ {⅀1} {⅀2} {M} 𝕄1 𝕄2 p q {Γ} {κ} (constr s es) = erase-inj ⅀2 (
  erase ⅀2
    (subst (Tm ⅀2 (M .α Γ)) (Pos∘γ≗β∘Pos 𝕄1 s)
      (constr (γ 𝕄1 s)
        (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄1 s)
          (mor-vec 𝕄1 es))))
    ≡⟨ sym (substTy-erase ⅀2 (Pos∘γ≗β∘Pos 𝕄1 s)
        (constr (γ 𝕄1 s)
          (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄1 s)
            (mor-vec 𝕄1 es)))) ⟩
  constr (γ 𝕄1 s)
    (eraseVec ⅀2
      (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄1 s)
        (mor-vec 𝕄1 es)))
    ≡⟨ cong (constr (γ 𝕄1 s)) (sym (substTy-eraseVec ⅀2 (⟨α,β⟩∘Pos≗Pos∘γ 𝕄1 s) (mor-vec 𝕄1 es))) ⟩
  constr (γ 𝕄1 s) (eraseVec ⅀2 (mor-vec 𝕄1 es))
    ≡⟨ cong (λ x → constr (γ 𝕄1 s) (eraseVec ⅀2 x)) (LangMorVec≡ 𝕄1 𝕄2 p q es) ⟩
  constr (γ 𝕄1 s) (eraseVec ⅀2 (mor-vec 𝕄2 es))
    ≡⟨ cong (λ x → constr x (eraseVec ⅀2 (mor-vec 𝕄2 es))) (p s) ⟩
  constr (γ 𝕄2 s) (eraseVec ⅀2 (mor-vec 𝕄2 es))
    ≡⟨ cong (constr (γ 𝕄2 s)) (substTy-eraseVec ⅀2 (⟨α,β⟩∘Pos≗Pos∘γ 𝕄2 s) (mor-vec 𝕄2 es)) ⟩
  constr (γ 𝕄2 s)
    (eraseVec ⅀2
      (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄2 s)
        (mor-vec 𝕄2 es)))
    ≡⟨ substTy-erase ⅀2 (Pos∘γ≗β∘Pos 𝕄2 s) 
        (constr (γ 𝕄2 s)
          (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄2 s)
            (mor-vec 𝕄2 es))) ⟩
  erase ⅀2
    (subst (Tm ⅀2 (M .α Γ)) (Pos∘γ≗β∘Pos 𝕄2 s)
      (constr (γ 𝕄2 s)
        (subst (TmVec ⅀2 (M .α Γ)) (⟨α,β⟩∘Pos≗Pos∘γ 𝕄2 s)
          (mor-vec 𝕄2 es)))) ∎)

LangMorVec≡ 𝕄1 𝕄2 p q [] = refl 
LangMorVec≡ {⅀1} {⅀2} {M} 𝕄1 𝕄2 p q {Γ} {(Δ , κ) ∷ Σ} (e ∷ es) = cong₂ _∷_ (erase-inj ⅀2 (
  erase ⅀2 (subst (flip (Tm ⅀2) (M .β κ)) (M .α-++ Δ Γ) (mor 𝕄1 e))
    ≡⟨ sym (substCtx-erase ⅀2 (M .α-++ Δ Γ) (mor 𝕄1 e)) ⟩
  erase ⅀2 (mor 𝕄1 e)
    ≡⟨ cong (erase ⅀2) (LangMor≡ 𝕄1 𝕄2 p q e) ⟩
  erase ⅀2 (mor 𝕄2 e)
    ≡⟨ substCtx-erase ⅀2 (M .α-++ Δ Γ) (mor 𝕄2 e) ⟩
  erase ⅀2 (subst (flip (Tm ⅀2) (M .β κ)) (M .α-++ Δ Γ) (mor 𝕄2 e)) ∎))
  (LangMorVec≡ 𝕄1 𝕄2 p q es)