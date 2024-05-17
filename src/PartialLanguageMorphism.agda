{-# OPTIONS --safe #-}

open import Level
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import SecondOrderLanguage
open import SecondOrderLanguageUntyped

module PartialLanguageMorphism where

-- Extend a relation to lists of matching length
List-rel : ∀{a b} {A : Set a} {B : Set b} →
          (A → B → Set) →
          List A → List B → Set
List-rel R [] [] = ⊤
List-rel R [] (x ∷ ys) = ⊥
List-rel R (x ∷ xs) [] = ⊥
List-rel R (x ∷ xs) (y ∷ ys) = R x y × List-rel R xs ys

-- Combine two relations into a relation on a product
×-rel : ∀{a1 a2 b1 b2 ℓ1 ℓ2}
        {A1 : Set a1} {A2 : Set a2}
        {B1 : Set b1} {B2 : Set b2} →
        (A1 → A2 → Set ℓ1) →
        (B1 → B2 → Set ℓ2) →
        A1 × B1 → A2 × B2 → Set (ℓ1 ⊔ ℓ2)
×-rel R S (x1 , y1) (x2 , y2) = R x1 x2 × S y1 y2        

-- Coherent relations between contexts and kinds
record CtxKndRel (⅀1 ⅀2 : SecondOrderSignature) : Set₁ where
  field
    -- Relation on contexts
    α : List (⅀1 .Knd) → List (⅀2 .Knd) → Set
    -- Relation on kinds
    β : ⅀1 .Knd → ⅀2 .Knd → Set
    -- α respects context concatenation
    α-++ : ∀{Γ1 Γ2 Γ1' Γ2'} → α Γ1 Γ1' → α Γ2 Γ2' → α (Γ1 ++ Γ2) (Γ1' ++ Γ2')

open CtxKndRel public

-- Partial language morphisms over a given context and kind relation
record ParLangMor (⅀1 ⅀2 : SecondOrderSignature) (R : CtxKndRel ⅀1 ⅀2) : Set where
  field
    -- How the morphism acts on variables
    mor-var : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
              Var ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
    -- How constructors are mapped under the morphism
    γ : ⅀1 .TyShape → ⅀2 .TyShape
    -- γ respects constructor types
    γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                ⅀2 .TyPos (γ s) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                 List-rel (×-rel (R .α) (R .β))
                  (⅀1 .TyPos s .fst)
                  (⅀2 .TyPos (γ s) .fst)

  -- The definition of the morphism
  mor : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
        Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
  mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → List-rel (×-rel (R .α) (R .β)) Σ1 Σ2 →
            TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2

  -- Variables act as specified
  mor αΓ βκ (var x) = mor-var αΓ βκ x
  -- Use γ to replace the constructor
  mor {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) =
    subst (Tm ⅀2 Γ2) (γ-ty-≡ s βκ) (
      constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es))

  -- The morphism acts identically on subterms
  mor-vec {Σ1 = []} {[]} p q [] = []
  mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    mor (R .α-++ αΔ αΓ) βκ e ∷ mor-vec αΓ αβ*Σ es

  -- Explicitly erased version of the morphism
  erase-mor : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
              Tm ⅀1 Γ1 κ1 → UTm ⅀2
  erase-mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → List-rel (×-rel (R .α) (R .β)) Σ1 Σ2 →
                  TmVec ⅀1 Γ1 Σ1 → UTmVec ⅀2

  erase-mor αΓ βκ (var x) = erase ⅀2 (mor-var αΓ βκ x)
  erase-mor αΓ βκ (constr s es) =
    constr (γ s) (erase-mor-vec αΓ (γ-resp-arg s βκ) es)

  erase-mor-vec {Σ1 = []} {[]} αΓ tt [] = []
  erase-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    (erase-mor (R .α-++ αΔ αΓ) βκ e , length Δ2) ∷ erase-mor-vec αΓ αβ*Σ es

  -- The explicitly erased morphism acts the same as
  -- applying the morphism and then erasing
  erase-mor-≡ : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) →
                (e : Tm ⅀1 Γ1 κ1) → erase ⅀2 (mor αΓ βκ e) ≡ erase-mor αΓ βκ e
  erase-mor-vec-≡ : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : List-rel (×-rel (R .α) (R .β)) Σ1 Σ2) →
                    (es : TmVec ⅀1 Γ1 Σ1) → eraseVec ⅀2 (mor-vec αΓ αβ*Σ es) ≡ erase-mor-vec αΓ αβ*Σ es

  erase-mor-≡ αΓ βκ (var x) = refl
  erase-mor-≡ {Γ1} {Γ2} αΓ βκ (constr s es) =
    erase ⅀2 (
      subst (Tm ⅀2 Γ2) (γ-ty-≡ s βκ) (
        constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ s βκ) (
          constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es))) ⟩
    constr (γ s) (eraseVec ⅀2 (mor-vec αΓ (γ-resp-arg s βκ) es))
      ≡⟨ cong (constr (γ s)) (erase-mor-vec-≡ αΓ (γ-resp-arg s βκ) es) ⟩
    constr (γ s) (erase-mor-vec αΓ (γ-resp-arg s βκ) es) ∎

  erase-mor-vec-≡ {Σ1 = []} {[]} αΓ tt [] = refl
  erase-mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    cong₃ (eraseCons ⅀2)
      (erase-mor-≡ (R .α-++ αΔ αΓ) βκ e)
      refl
      (erase-mor-vec-≡ αΓ αβ*Σ es)
  
  erase-mor-vec-subst-≡ : ∀{Γ1 Γ2 Σ1 Σ2 Σ2'} (αΓ : R .α Γ1 Γ2) (αβ*Σ : List-rel (×-rel (R .α) (R .β)) Σ1 Σ2)
                          (p : Σ2 ≡ Σ2') (es : TmVec ⅀1 Γ1 Σ1) →
                          erase-mor-vec αΓ (subst (List-rel (×-rel (R .α) (R .β)) Σ1) p αβ*Σ) es
                          ≡ erase-mor-vec αΓ αβ*Σ es
  erase-mor-vec-subst-≡ αΓ αβ*Σ refl es = refl

open ParLangMor public

-- To prove two language morphisms over the same context and kind
-- relation are equivalent, it suffices to prove that
-- they are equivalent on variables and constructors
record ParLangMor≡ {⅀1 ⅀2 : SecondOrderSignature} {R : CtxKndRel ⅀1 ⅀2}
  (𝕄1 𝕄2 : ParLangMor ⅀1 ⅀2 R) : Set where
  field
    -- The modified constructors will be identical
    γ1≗γ2 : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ) →
            γ 𝕄1 s ≡ γ 𝕄2 s
    -- The proofs that constructors preserve relatedness are equivalent
    γ-resp-arg-≡ : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ)
                   (p : ⅀2 .TyPos (γ 𝕄1 s) .fst ≡ ⅀2 .TyPos (γ 𝕄2 s) .fst) →
                   subst (List-rel (×-rel (R .α) (R .β)) (⅀1 .TyPos s .fst)) p (γ-resp-arg 𝕄1 s βκ)
                   ≡ γ-resp-arg 𝕄2 s βκ
    -- The morphisms are identical on variables
    var1≗var2 : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (x : Var ⅀1 Γ1 κ1) →
                mor-var 𝕄1 αΓ βκ x ≡ mor-var 𝕄2 αΓ βκ x

  -- The morphisms are identical on all terms
  mor-≡ : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
          mor 𝕄1 αΓ βκ e ≡ mor 𝕄2 αΓ βκ e
  mor-vec-≡ : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : List-rel (×-rel (R .α) (R .β)) Σ1 Σ2) (es : TmVec ⅀1 Γ1 Σ1) →
              mor-vec 𝕄1 αΓ αβ*Σ es ≡ mor-vec 𝕄2 αΓ αβ*Σ es

  mor-≡ αΓ βκ (var x) = var1≗var2 αΓ βκ x
  mor-≡ {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) = erase-inj ⅀2 (
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄1 s βκ)
        (constr (γ 𝕄1 s) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ 𝕄1 s βκ)
          (constr (γ 𝕄1 s) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))) ⟩
    constr (γ 𝕄1 s) (eraseVec ⅀2 (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (λ x → constr (γ 𝕄1 s) (eraseVec ⅀2 x)) (
          mor-vec-≡ αΓ (γ-resp-arg 𝕄1 s βκ) es) ⟩
    constr (γ 𝕄1 s) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (λ x → constr x (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))) 
          (γ1≗γ2 s βκ) ⟩
    constr (γ 𝕄2 s) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (constr (γ 𝕄2 s)) (erase-mor-vec-≡ 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es) ⟩
    constr (γ 𝕄2 s) (erase-mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es)
      ≡⟨ cong (constr (γ 𝕄2 s)) (sym (
          erase-mor-vec-subst-≡ 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) (
            cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ))
          es)) ⟩
    constr (γ 𝕄2 s) (erase-mor-vec 𝕄2 αΓ (
      subst (List-rel (×-rel (R .α) (R .β)) (⅀1 .TyPos s .fst)) (
        cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ)) (γ-resp-arg 𝕄1 s βκ))
      es)
      ≡⟨ cong (λ x → constr (γ 𝕄2 s) (erase-mor-vec 𝕄2 αΓ x es))
          (γ-resp-arg-≡ s βκ (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ))) ⟩
    constr (γ 𝕄2 s) (erase-mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)
      ≡⟨ sym (cong (constr (γ 𝕄2 s)) (erase-mor-vec-≡ 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)) ⟩
    constr (γ 𝕄2 s) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es))
      ≡⟨ substTy-erase ⅀2 (γ-ty-≡ 𝕄2 s βκ)
          (constr (γ 𝕄2 s) (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)) ⟩
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s βκ)
        (constr (γ 𝕄2 s) (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es))) ∎)

  mor-vec-≡ {Σ1 = []} {[]} αΓ αβ*Σ [] = refl
  mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    cong₂ _∷_
      (mor-≡ (R .α-++ αΔ αΓ) βκ e)
      (mor-vec-≡ αΓ αβ*Σ es)
