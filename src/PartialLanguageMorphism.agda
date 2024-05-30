{-# OPTIONS --safe #-}

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Sum  renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Data.List
open import Data.List.Properties
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Product.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import SecondOrderLanguage
open import SecondOrderLanguageUntyped

module PartialLanguageMorphism where

-- Coherent relations between contexts and kinds
record CtxKndRel (⅀1 ⅀2 : SecondOrderSignature) : Set₁ where
  field
    -- Relation on contexts
    α : List (⅀1 .Knd) → List (⅀2 .Knd) → Set
    -- Relation on kinds
    β : ⅀1 .Knd → ⅀2 .Knd → Set
    -- Relation on context extensions
    δ : List (⅀1 .Knd) → List (⅀2 .Knd) → Set
    -- Relation on binders
    μ : List (List (⅀1 .Knd) × ⅀1 .Knd) → List (List (⅀2 .Knd) × ⅀2 .Knd) → Set
    -- α respects context extension by δ
    δ-++-α : ∀{Δ1 Δ2 Γ1 Γ2} → δ Δ1 Δ2 → α Γ1 Γ2 → α (Δ1 ++ Γ1) (Δ2 ++ Γ2)
    -- Empty binders are related
    μ-nil : μ [] []
    -- If non-empty binders are related then their heads are related
    μ-head-δ : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2) → δ Δ1 Δ2
    μ-head-β : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2) → β κ1 κ2
    -- If non-empty binders are related then their tails are related
    μ-tail : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2) → μ Σ1 Σ2
    -- Lists of unequal lengths are unrelated
    μ-cons-nil : ∀{Δ1 κ1 Σ1} → μ ((Δ1 , κ1) ∷ Σ1) [] → ⊥
    μ-nil-cons : ∀{Δ2 κ2 Σ2} → μ [] ((Δ2 , κ2) ∷ Σ2) → ⊥

open CtxKndRel public

record CtxKndRel≅ {⅀1 ⅀2} (R S : CtxKndRel ⅀1 ⅀2) : Set₁ where
  field
    α≅ : R .α ≅ᵣ S .α
    β≅ : R .β ≅ᵣ S .β
    δ≅ : R .δ ≅ᵣ S .δ
    μ≅ : R .μ ≅ᵣ S .μ

open CtxKndRel≅ public

record CtxKndRel⇒ {⅀1 ⅀2} (R S : CtxKndRel ⅀1 ⅀2) : Set₁ where
  field
    α⇒ : R .α ⇒ S .α
    β⇒ : R .β ⇒ S .β
    δ⇒ : R .δ ⇒ S .δ
    μ⇒ : R .μ ⇒ S .μ
    μ-tail-≡ : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → 
               (μΣ : R .μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2)) →
               μ⇒ (R .μ-tail μΣ) ≡ S .μ-tail (μ⇒ μΣ)
    μ-head-δ-≡ : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → 
                 (μΣ : R .μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2)) →
                 δ⇒ (R .μ-head-δ μΣ) ≡ S .μ-head-δ (μ⇒ μΣ)
    μ-head-β-≡ : ∀{Δ1 κ1 Σ1 Δ2 κ2 Σ2} → 
                  (μΣ : R .μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2)) →
                  β⇒ (R .μ-head-β μΣ) ≡ S .μ-head-β (μ⇒ μΣ)

open CtxKndRel⇒ public

CtxKndRel⇒-refl : ∀{⅀1 ⅀2} (R : CtxKndRel ⅀1 ⅀2) → CtxKndRel⇒ R R
α⇒ (CtxKndRel⇒-refl R) p = p
β⇒ (CtxKndRel⇒-refl R) p = p
δ⇒ (CtxKndRel⇒-refl R) p = p
μ⇒ (CtxKndRel⇒-refl R) p = p
μ-tail-≡ (CtxKndRel⇒-refl R) p = refl
μ-head-δ-≡ (CtxKndRel⇒-refl R) p = refl
μ-head-β-≡ (CtxKndRel⇒-refl R) p = refl

⋆CtxKndRel : ∀{⅀1 ⅀2} → CtxKndRel ⅀1 ⅀2 → CtxKndRel ⅀1 ⅀2
α (⋆CtxKndRel R) = R .α
β (⋆CtxKndRel R) = R .β
δ (⋆CtxKndRel R) = R .δ
μ (⋆CtxKndRel R) = ⋆ (R .δ ×ᵣ R .β)
δ-++-α (⋆CtxKndRel R) = R .δ-++-α
μ-nil (⋆CtxKndRel R) = lift tt
μ-head-δ (⋆CtxKndRel R) ((δΔ , βκ) , *δβΣ) = δΔ
μ-head-β (⋆CtxKndRel R) ((δΔ , βκ) , *δβΣ) = βκ
μ-tail (⋆CtxKndRel R) ((δΔ , βκ) , *δβΣ) = *δβΣ
μ-cons-nil (⋆CtxKndRel R) ()
μ-nil-cons (⋆CtxKndRel R) ()

{-
CtxKndRel-≅-to-⇒ : ∀{⅀1 ⅀2} {R S : CtxKndRel ⅀1 ⅀2} →
                    CtxKndRel≅ R S → CtxKndRel⇒ R S
α⇒ (CtxKndRel-≅-to-⇒ R≅S) = R≅S .α≅ _ _ .forward
β⇒ (CtxKndRel-≅-to-⇒ R≅S) = R≅S .β≅ _ _ .forward
δ⇒ (CtxKndRel-≅-to-⇒ R≅S) = R≅S .δ≅ _ _ .forward
μ⇒ (CtxKndRel-≅-to-⇒ R≅S) = R≅S .μ≅ _ _ .forward
μ-tail-≡ (CtxKndRel-≅-to-⇒ {R = R} {S} R≅S) {Δ1} {κ1} {Σ1} {Δ2} {κ2} {Σ2} μΣ = {! 
  R≅S .μ≅ Σ1 Σ2 .forward (R .μ-tail μΣ) ≡
  S .μ-tail (R≅S .μ≅ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2) .forward μΣ)
  !}
μ-head-δ-≡ (CtxKndRel-≅-to-⇒ R≅S) = {!   !}
μ-head-β-≡ (CtxKndRel-≅-to-⇒ R≅S) = {!   !}
-}

{-
CtxKndRel-≅-to-⇒ : ∀{⅀1 ⅀2} {R S : CtxKndRel ⅀1 ⅀2} →
                    CtxKndRel≅ R S → CtxKndRel⇒ R S
α⇒ (CtxKndRel-≅-to-⇒ p) = p .α≅ _ _ .forward
β⇒ (CtxKndRel-≅-to-⇒ p) = p .β≅ _ _ .forward
δ⇒ (CtxKndRel-≅-to-⇒ p) = p .δ≅ _ _ .forward
μ⇒ (CtxKndRel-≅-to-⇒ p) = p .μ≅ _ _ .forward
μ-tail-≡ (CtxKndRel-≅-to-⇒ {R = R} {S} p) {Δ1} {κ1} {Σ1} {Δ2} {κ2} {Σ2} μΣ =
  p .μ≅ Σ1 Σ2 .forward (R .μ-tail μΣ)
    ≡⟨ {!  !} ⟩
  S .μ-tail (p .μ≅ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2) .forward μΣ) ∎
-}

-- Identity relation
id-rel : ∀{⅀} → CtxKndRel ⅀ ⅀
α id-rel Γ1 Γ2 = Γ1 ≡ Γ2
β id-rel κ1 κ2 = κ1 ≡ κ2
δ id-rel Δ1 Δ2 = Δ1 ≡ Δ2
μ id-rel Σ1 Σ2 = Σ1 ≡ Σ2
δ-++-α id-rel p q = cong₂ _++_ p q
μ-nil id-rel = refl
μ-head-δ id-rel p = ,-injective (∷-injective p .fst) .fst
μ-head-β id-rel p = ,-injective (∷-injective p .fst) .snd
μ-tail id-rel p = ∷-injective p .snd
μ-nil-cons id-rel p = nil≢cons p
μ-cons-nil id-rel p = cons≢nil p

-- Composition of context and kind relations
infixr 9 _∘ᵣₖ_
_∘ᵣₖ_ : ∀{⅀1 ⅀2 ⅀3} → CtxKndRel ⅀2 ⅀3 → CtxKndRel ⅀1 ⅀2 → CtxKndRel ⅀1 ⅀3
α (R ∘ᵣₖ S) = R .α ∘ᵣ S .α
β (R ∘ᵣₖ S) = R .β ∘ᵣ S .β
δ (R ∘ᵣₖ S) = R .δ ∘ᵣ S .δ
μ (R ∘ᵣₖ S) = R .μ ∘ᵣ S .μ
δ-++-α (R ∘ᵣₖ S) (Δ2 , δ32 , δ12) (Γ2 , α32 , α12) = 
  Δ2 ++ Γ2 , R .δ-++-α δ32 α32 , S .δ-++-α δ12 α12
μ-nil (R ∘ᵣₖ S) = [] , R .μ-nil , S .μ-nil
μ-head-δ (R ∘ᵣₖ S) ([] , p , q) = ⊥-elim (R .μ-nil-cons p)
μ-head-δ (R ∘ᵣₖ S) ((Δ2 , κ2) ∷ Σ2 , p , q) = Δ2 , R .μ-head-δ p , S .μ-head-δ q
μ-head-β (R ∘ᵣₖ S) ([] , p , q) = ⊥-elim (R .μ-nil-cons p)
μ-head-β (R ∘ᵣₖ S) ((Δ2 , κ2) ∷ Σ2 , p , q) = κ2 , R .μ-head-β p , S .μ-head-β q
μ-tail (R ∘ᵣₖ S) ([] , p , q) = ⊥-elim (R .μ-nil-cons p)
μ-tail (R ∘ᵣₖ S) ((Δ2 , κ2) ∷ Σ2 , p , q) = Σ2 , R .μ-tail p , S .μ-tail q
μ-nil-cons (R ∘ᵣₖ S) ([] , p , q) = R .μ-nil-cons p
μ-nil-cons (R ∘ᵣₖ S) ((Δ2 , κ2) ∷ Σ2 , p , q) = S .μ-nil-cons q
μ-cons-nil (R ∘ᵣₖ S) ([] , p , q) = S .μ-cons-nil q
μ-cons-nil (R ∘ᵣₖ S) ((Δ2 , κ2) ∷ Σ2 , p , q) = R .μ-cons-nil p

-- Partial language morphisms over a given context and kind relation
record ParLangMor (⅀1 ⅀2 : SecondOrderSignature) : Set₁ where
  field
    -- The relation the morphism is over
    mor-rel : CtxKndRel ⅀1 ⅀2

    -- How the morphism acts on variables
    mor-var : ∀{Γ1 Γ2 κ1 κ2} → mor-rel .α Γ1 Γ2 → mor-rel .β κ1 κ2 →
              Var ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
    -- How constructors are mapped under the morphism
    γ : ∀{κ} (s : ⅀1 .TyShape) → mor-rel .β (⅀1 .TyPos s .snd) κ →  ⅀2 .TyShape
    -- γ respects constructor types
    γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) →
              (p : mor-rel .β (⅀1 .TyPos s .snd) κ) →
              ⅀2 .TyPos (γ s p) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) →
                 (p : mor-rel .β (⅀1 .TyPos s .snd) κ) →
                 mor-rel .μ (⅀1 .TyPos s .fst) (⅀2 .TyPos (γ s p) .fst)

  -- The definition of the morphism
  mor : ∀{Γ1 Γ2 κ1 κ2} → mor-rel .α Γ1 Γ2 → mor-rel .β κ1 κ2 →
        Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
  mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → mor-rel .α Γ1 Γ2 → mor-rel .μ Σ1 Σ2 →
            TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2

  -- Variables act as specified
  mor αΓ βκ (var x) = mor-var αΓ βκ x
  -- Use γ to replace the constructor
  mor {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) =
    subst (Tm ⅀2 Γ2) (γ-ty-≡ s βκ)
      (constr (γ s βκ) (mor-vec αΓ (γ-resp-arg s βκ) es))

  -- The morphism acts identically on subterms
  mor-vec {Σ1 = []} {[]} αΓ μΣ [] = []
  mor-vec {Σ1 = []} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ [] = ⊥-elim $ mor-rel .μ-nil-cons μΣ
  mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {[]} αΓ μΣ (e ∷ es) = ⊥-elim $ mor-rel .μ-cons-nil μΣ
  mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ (e ∷ es) =
    mor (mor-rel .δ-++-α (mor-rel .μ-head-δ μΣ) αΓ) (mor-rel .μ-head-β μΣ) e
    ∷ mor-vec αΓ (mor-rel .μ-tail μΣ) es

  -- Explicitly erased version of the morphism
  erase-mor : ∀{Γ1 Γ2 κ1 κ2} → mor-rel .α Γ1 Γ2 → mor-rel .β κ1 κ2 →
              Tm ⅀1 Γ1 κ1 → UTm ⅀2
  erase-mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → mor-rel .α Γ1 Γ2 → mor-rel .μ Σ1 Σ2 →
                  TmVec ⅀1 Γ1 Σ1 → UTmVec ⅀2

  erase-mor αΓ βκ (var x) = erase ⅀2 (mor-var αΓ βκ x)
  erase-mor αΓ βκ (constr s es) =
    constr (γ s βκ) (erase-mor-vec αΓ (γ-resp-arg s βκ) es)

  erase-mor-vec {Σ1 = []} {[]} αΓ μΣ [] = []
  erase-mor-vec {Σ1 = []} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ [] = ⊥-elim $ mor-rel .μ-nil-cons μΣ
  erase-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {[]} αΓ μΣ (e ∷ es) = ⊥-elim $ mor-rel .μ-cons-nil μΣ
  erase-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ (e ∷ es) =
    (erase-mor (mor-rel .δ-++-α (mor-rel .μ-head-δ μΣ) αΓ) (mor-rel .μ-head-β μΣ) e , length Δ2)
    ∷ erase-mor-vec αΓ (mor-rel .μ-tail μΣ) es

  -- The explicitly erased morphism acts the same as
  -- applying the morphism and then erasing
  erase-mor-≡ : ∀{Γ1 Γ2 κ1 κ2} (αΓ : mor-rel .α Γ1 Γ2) (βκ : mor-rel .β κ1 κ2) →
                (e : Tm ⅀1 Γ1 κ1) → erase ⅀2 (mor αΓ βκ e) ≡ erase-mor αΓ βκ e
  erase-mor-vec-≡ : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : mor-rel .α Γ1 Γ2) (μΣ : mor-rel .μ Σ1 Σ2) →
                    (es : TmVec ⅀1 Γ1 Σ1) →
                    eraseVec ⅀2 (mor-vec αΓ μΣ es) ≡ erase-mor-vec αΓ μΣ es

  erase-mor-≡ αΓ βκ (var x) = refl
  erase-mor-≡ {Γ1} {Γ2} αΓ βκ (constr s es) =
    erase ⅀2 (
      subst (Tm ⅀2 Γ2) (γ-ty-≡ s βκ) (
        constr (γ s βκ) (mor-vec αΓ (γ-resp-arg s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ s βκ) (
          constr (γ s βκ) (mor-vec αΓ (γ-resp-arg s βκ) es))) ⟩
    constr (γ s βκ) (eraseVec ⅀2 (mor-vec αΓ (γ-resp-arg s βκ) es))
      ≡⟨ cong (constr (γ s βκ)) (erase-mor-vec-≡ αΓ (γ-resp-arg s βκ) es) ⟩
    constr (γ s βκ) (erase-mor-vec αΓ (γ-resp-arg s βκ) es) ∎

  erase-mor-vec-≡ {Σ1 = []} {[]} αΓ μΣ [] = refl
  erase-mor-vec-≡ {Σ1 = []} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ [] = ⊥-elim (mor-rel .μ-nil-cons μΣ)
  erase-mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {[]} αΓ μΣ (e ∷ es) = ⊥-elim (mor-rel .μ-cons-nil μΣ)
  erase-mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ (e ∷ es) =
    cong₃ (eraseCons ⅀2)
      (erase-mor-≡ (mor-rel .δ-++-α (mor-rel .μ-head-δ μΣ) αΓ) (mor-rel .μ-head-β μΣ) e)
      refl
      (erase-mor-vec-≡ αΓ (mor-rel .μ-tail μΣ) es)

  -- Substituting the proof of relatedness has no effect on the erased morphism
  erase-mor-vec-subst-≡ : ∀{Γ1 Γ2 Σ1 Σ2 Σ2'} (αΓ : mor-rel .α Γ1 Γ2) (μΣ : mor-rel .μ Σ1 Σ2)
                          (p : Σ2 ≡ Σ2') (es : TmVec ⅀1 Γ1 Σ1) →
                          erase-mor-vec αΓ (subst (mor-rel .μ Σ1) p μΣ) es
                          ≡ erase-mor-vec αΓ μΣ es
  erase-mor-vec-subst-≡ αΓ μΣ refl es = refl

  erase-mor-substTy-≡ : ∀{Γ1 Γ2 κ1 κ1' κ2} (αΓ : mor-rel .α Γ1 Γ2) (βκ : mor-rel .β κ1' κ2)
                        (p : κ1 ≡ κ1') (q : κ1' ≡ κ1) (e : Tm ⅀1 Γ1 κ1) →
                        erase-mor αΓ βκ (subst (Tm ⅀1 Γ1) p e)
                        ≡ erase-mor αΓ (subst (flip (mor-rel .β) κ2) q βκ) e
  erase-mor-substTy-≡ αΓ βκ refl refl e = refl

open ParLangMor public

{-
To prove two language morphisms are extensionally equivalent,
it suffices to prove that they are equivalent on variables
and constructors, where the relational arguments are mediated
by an implication between the relations of the morphisms
-}
record ParLangMorPath {⅀1 ⅀2 : SecondOrderSignature}
  (𝕄1 : ParLangMor ⅀1 ⅀2) (𝕄2 : ParLangMor ⅀1 ⅀2) : Set₁ where
  field
    -- The relation of the first morphism implies the relation of the second morphism
    mor-rel-⇒ : CtxKndRel⇒ (𝕄1 .mor-rel) (𝕄2 .mor-rel)

    -- The modified constructors will be identical
    γ1≗γ2-Path : ∀{κ} (s : ⅀1 .TyShape) (βκ : 𝕄1 .mor-rel .β (⅀1 .TyPos s .snd) κ) →
                 γ 𝕄1 s βκ ≡ γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ)

    -- The proofs that constructors preserve relatedness are equivalent
    γ-resp-arg-≡-Path : ∀{κ} (s : ⅀1 .TyShape) (βκ : 𝕄1 .mor-rel .β (⅀1 .TyPos s .snd) κ)
                        (p : ⅀2 .TyPos (γ 𝕄1 s βκ) .fst ≡ ⅀2 .TyPos (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ)) .fst) →
                        subst (𝕄2 .mor-rel .μ (⅀1 .TyPos s .fst)) p (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
                        ≡ γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ)

    -- The morphisms are identical on variables
    var1≗var2-Path : ∀{Γ1 Γ2 κ1 κ2} (αΓ : 𝕄1 .mor-rel .α Γ1 Γ2) (βκ : 𝕄1 .mor-rel .β κ1 κ2) (x : Var ⅀1 Γ1 κ1) →
                     mor-var 𝕄1 αΓ βκ x ≡
                     mor-var 𝕄2 (mor-rel-⇒ .α⇒ αΓ) (mor-rel-⇒ .β⇒ βκ) x

    δ-++-α-Path : ∀{Δ1 Δ2 Γ1 Γ2} (δΔ : 𝕄1 .mor-rel .δ Δ1 Δ2) (αΓ : 𝕄1 .mor-rel .α Γ1 Γ2) →
      mor-rel-⇒ .α⇒ (𝕄1 .mor-rel .δ-++-α δΔ αΓ) ≡
      𝕄2 .mor-rel .δ-++-α (mor-rel-⇒ .δ⇒ δΔ) (mor-rel-⇒ .α⇒ αΓ)

  -- The morphisms are identical on all terms
  mor-≡-Path : ∀{Γ1 Γ2 κ1 κ2} (αΓ : 𝕄1 .mor-rel .α Γ1 Γ2) (βκ : 𝕄1 .mor-rel .β κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
              mor 𝕄1 αΓ βκ e ≡
              mor 𝕄2 (mor-rel-⇒ .α⇒ αΓ) (mor-rel-⇒ .β⇒ βκ) e
  mor-vec-≡-Path : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : 𝕄1 .mor-rel .α Γ1 Γ2) (μΣ : 𝕄1 .mor-rel .μ Σ1 Σ2) (es : TmVec ⅀1 Γ1 Σ1) →
                   mor-vec 𝕄1 αΓ μΣ es ≡
                   mor-vec 𝕄2
                    (mor-rel-⇒ .α⇒ αΓ)
                    (mor-rel-⇒ .μ⇒ μΣ)
                    es

  mor-≡-Path αΓ βκ (var x) = var1≗var2-Path αΓ βκ x
  mor-≡-Path {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) = erase-inj ⅀2 $
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄1 s βκ)
        (constr (γ 𝕄1 s βκ) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ 𝕄1 s βκ)
          (constr (γ 𝕄1 s βκ) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))) ⟩
    constr (γ 𝕄1 s βκ)
      (eraseVec ⅀2 (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (λ x → constr (γ 𝕄1 s βκ) (eraseVec ⅀2 x)) $
          mor-vec-≡-Path αΓ (γ-resp-arg 𝕄1 s βκ) es ⟩
    constr (γ 𝕄1 s βκ)
      (eraseVec ⅀2
        (mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
          (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
          es))
      ≡⟨ cong (λ x → constr x (eraseVec ⅀2
          (mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
            (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
            es))) 
          (γ1≗γ2-Path s βκ) ⟩
    constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (eraseVec ⅀2
        (mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
          (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
          es))
      ≡⟨ (cong (constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))) $
          erase-mor-vec-≡ 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
          (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
          es) ⟩
    constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (erase-mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
        es)
      ≡⟨ (cong (constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))) $
          sym $ erase-mor-vec-subst-≡ 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
            (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ))
            (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))
            es) ⟩
    constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (erase-mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (subst (mor-rel 𝕄2 .μ (⅀1 .TyPos s .fst))
          (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))
          (mor-rel-⇒ .μ⇒ (γ-resp-arg 𝕄1 s βκ)))
        es)
      ≡⟨ (cong (λ x → constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
            (erase-mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ) x es)) $
            γ-resp-arg-≡-Path s βκ (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))) ⟩
    constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (erase-mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
        es)
      ≡⟨ (cong (constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))) $
          sym $ erase-mor-vec-≡ 𝕄2 
            (mor-rel-⇒ .α⇒ αΓ)
            (γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
            es) ⟩
    constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (eraseVec ⅀2 (mor-vec 𝕄2
        (mor-rel-⇒ .α⇒ αΓ)
        (γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ)) es))
      ≡⟨ substTy-erase ⅀2 (γ-ty-≡ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
          (constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
            (mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
              (γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ)) es)) ⟩
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
      (constr (γ 𝕄2 s (mor-rel-⇒ .β⇒ βκ))
        (mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (γ-resp-arg 𝕄2 s (mor-rel-⇒ .β⇒ βκ)) es))) ∎

  mor-vec-≡-Path {Σ1 = []} {[]} αΓ μΣ [] = refl
  mor-vec-≡-Path {Γ1} {Γ2} {Σ1 = []} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ [] = ⊥-elim $ 𝕄1 .mor-rel .μ-nil-cons μΣ
  mor-vec-≡-Path {Γ1} {Γ2} {Σ1 = (Δ1 , κ1) ∷ Σ1} {[]} αΓ μΣ (e ∷ es) = ⊥-elim $ 𝕄1 .mor-rel .μ-cons-nil μΣ
  mor-vec-≡-Path {Γ1} {Γ2} {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ (e ∷ es) =
    cong₂ _∷_
      (mor 𝕄1
        (mor-rel 𝕄1 .δ-++-α (mor-rel 𝕄1 .μ-head-δ μΣ) αΓ)
        (mor-rel 𝕄1 .μ-head-β μΣ) e
          ≡⟨ mor-≡-Path
              (mor-rel 𝕄1 .δ-++-α (mor-rel 𝕄1 .μ-head-δ μΣ) αΓ)
              (mor-rel 𝕄1 .μ-head-β μΣ)
              e ⟩
      mor 𝕄2
        (mor-rel-⇒ .α⇒ (mor-rel 𝕄1 .δ-++-α (mor-rel 𝕄1 .μ-head-δ μΣ) αΓ))
        (mor-rel-⇒ .β⇒ (mor-rel 𝕄1 .μ-head-β μΣ))
        e
          ≡⟨ (cong (λ x → mor 𝕄2 x (mor-rel-⇒ .β⇒ (mor-rel 𝕄1 .μ-head-β μΣ)) e) $
                δ-++-α-Path (mor-rel 𝕄1 .μ-head-δ μΣ) αΓ) ⟩
      mor 𝕄2
        (𝕄2 .mor-rel .δ-++-α
          (mor-rel-⇒ .δ⇒ (mor-rel 𝕄1 .μ-head-δ μΣ))
          (mor-rel-⇒ .α⇒ αΓ))
        (mor-rel-⇒ .β⇒ (mor-rel 𝕄1 .μ-head-β μΣ))
        e
          ≡⟨ cong₂ (λ x y →
                mor 𝕄2
                (𝕄2 .mor-rel .δ-++-α x (mor-rel-⇒ .α⇒ αΓ))
                y e)
                (mor-rel-⇒ .μ-head-δ-≡ μΣ)
                (mor-rel-⇒ .μ-head-β-≡ μΣ) ⟩
      mor 𝕄2
        (mor-rel 𝕄2 .δ-++-α
          (mor-rel 𝕄2 .μ-head-δ (mor-rel-⇒ .μ⇒ μΣ))
          (mor-rel-⇒ .α⇒ αΓ))
        (mor-rel 𝕄2 .μ-head-β (mor-rel-⇒ .μ⇒ μΣ))
        e ∎)
      (mor-vec 𝕄1 αΓ (mor-rel 𝕄1 .μ-tail μΣ) es
        ≡⟨ mor-vec-≡-Path αΓ (mor-rel 𝕄1 .μ-tail μΣ) es ⟩
      mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (mor-rel-⇒ .μ⇒ (mor-rel 𝕄1 .μ-tail μΣ))
        es
        ≡⟨ (cong (λ x → mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ) x es) $
            mor-rel-⇒ .μ-tail-≡ μΣ) ⟩
      mor-vec 𝕄2 (mor-rel-⇒ .α⇒ αΓ)
        (mor-rel 𝕄2 .μ-tail (mor-rel-⇒ .μ⇒ μΣ))
        es ∎)

open ParLangMorPath public

-- Functions which behave as a morphism
record IsParLangMor (⅀1 ⅀2 : SecondOrderSignature) (R : CtxKndRel ⅀1 ⅀2)
  (f : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 → Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2)
  (f-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → R .μ Σ1 Σ2 → TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2)
  : Set where
  field
    -- How constructors are mapped under the morphism
    is-γ : ∀{κ} (s : ⅀1 .TyShape) → R .β (⅀1 .TyPos s .snd) κ →  ⅀2 .TyShape
    -- γ respects constructor types
    is-γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) →
                (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                ⅀2 .TyPos (is-γ s βκ) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    is-γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) →
                    (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                    R .μ (⅀1 .TyPos s .fst) (⅀2 .TyPos (is-γ s βκ) .fst)

    -- Use γ to replace the constructor
    f-constr : ∀{Γ1 Γ2 κ} (s : ⅀1 .TyShape) (αΓ : R .α Γ1 Γ2) (βκ : R .β (⅀1 .TyPos s .snd) κ)
               (es : TmVec ⅀1 Γ1 (⅀1 .TyPos s .fst)) →
               f αΓ βκ (constr s es) ≡
               subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ) (
                 constr (is-γ s βκ) (f-vec αΓ (is-γ-resp-arg s βκ) es))
    -- The morphism acts identically on subterms
    f-vec-nil : ∀{Γ1 Γ2} (αΓ : R .α Γ1 Γ2) (μΣ : R .μ [] []) → f-vec αΓ μΣ [] ≡ []
    f-vec-cons : ∀{Γ1 Γ2 Δ1 Δ2 κ1 κ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2)
                  (μΣ : R .μ ((Δ1 , κ1) ∷ Σ1) ((Δ2 , κ2) ∷ Σ2))
                  (e : Tm ⅀1 (Δ1 ++ Γ1) κ1) (es : TmVec ⅀1 Γ1 Σ1) →
                  f-vec αΓ μΣ (e ∷ es) ≡
                  f (R .δ-++-α (R .μ-head-δ μΣ) αΓ) (R .μ-head-β μΣ) e ∷ f-vec αΓ (R .μ-tail μΣ) es

  -- The morphism that f is equivalent to
  f-mor : ParLangMor ⅀1 ⅀2
  mor-rel f-mor = R
  mor-var f-mor αΓ βκ x = f αΓ βκ (var x)
  γ f-mor = is-γ
  γ-ty-≡ f-mor s βκ = is-γ-ty-≡ s βκ
  γ-resp-arg f-mor s βκ = is-γ-resp-arg s βκ

  -- f is extensionally equivalent to this morphism
  f-≗-f-mor : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2)
              (e : Tm ⅀1 Γ1 κ1) →
              f αΓ βκ e ≡ mor f-mor αΓ βκ e
  f-vec-≗-f-mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (μΣ : R .μ Σ1 Σ2)
                      (es : TmVec ⅀1 Γ1 Σ1) →
                      f-vec αΓ μΣ es ≡ mor-vec f-mor αΓ μΣ es

  f-≗-f-mor αΓ βκ (var x) = refl
  f-≗-f-mor {Γ1} {Γ2} αΓ βκ (constr s es) =
    f αΓ βκ (constr s es)
      ≡⟨ f-constr s αΓ βκ es ⟩
    subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ)
      (constr (is-γ s βκ) (f-vec αΓ (is-γ-resp-arg s βκ) es))
      ≡⟨ cong (λ x → subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ) (constr (is-γ s βκ) x))
          (f-vec-≗-f-mor-vec αΓ (is-γ-resp-arg s βκ) es) ⟩
    subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ)
      (constr (is-γ s βκ) (mor-vec f-mor αΓ (is-γ-resp-arg s βκ) es)) ∎

  f-vec-≗-f-mor-vec {Σ1 = []} {[]} αΓ μΣ [] = f-vec-nil αΓ μΣ
  f-vec-≗-f-mor-vec {Σ1 = []} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ [] = ⊥-elim $ R .μ-nil-cons μΣ
  f-vec-≗-f-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {[]} αΓ μΣ (e ∷ es) = ⊥-elim $ R .μ-cons-nil μΣ
  f-vec-≗-f-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ μΣ (e ∷ es) =
    f-vec αΓ μΣ (e ∷ es)
      ≡⟨ f-vec-cons αΓ μΣ e es ⟩
    f (R .δ-++-α (R .μ-head-δ μΣ) αΓ) (R .μ-head-β μΣ) e ∷
    f-vec αΓ (R .μ-tail μΣ) es
      ≡⟨ cong₂ _∷_
          (f-≗-f-mor (R .δ-++-α (R .μ-head-δ μΣ) αΓ) (R .μ-head-β μΣ) e)
          (f-vec-≗-f-mor-vec αΓ (R .μ-tail μΣ) es) ⟩
    mor f-mor (R .δ-++-α (R .μ-head-δ μΣ) αΓ) (R .μ-head-β μΣ) e ∷
    mor-vec f-mor αΓ (R .μ-tail μΣ) es ∎

open IsParLangMor public

-- Restrict a morphism to a sub-relation
restr-mor : ∀{⅀1 ⅀2} (R : CtxKndRel ⅀1 ⅀2) →
            (𝕄 : ParLangMor ⅀1 ⅀2) →
            (R⇒𝕄 : CtxKndRel⇒ R (𝕄 .mor-rel)) →
            (∀{κ} (s : ⅀1 .TyShape) →
                 (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                 R .μ (⅀1 .TyPos s .fst)
                   (⅀2 .TyPos (𝕄 .γ s (R⇒𝕄 .β⇒ βκ)) .fst)) →
            ParLangMor ⅀1 ⅀2
mor-rel (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') = R
mor-var (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') αΓ βκ x = 𝕄 .mor-var (R⇒𝕄 .α⇒ αΓ) (R⇒𝕄 .β⇒ βκ) x
γ (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') s βκ = 𝕄 .γ s (R⇒𝕄 .β⇒ βκ)
γ-ty-≡ (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') s βκ = 𝕄 .γ-ty-≡ s (R⇒𝕄 .β⇒ βκ)
γ-resp-arg (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') = γ-resp-arg'

-- Restricting the morphism doesn't change anything
restr-mor-path : ∀{⅀1 ⅀2} {R : CtxKndRel ⅀1 ⅀2} →
                (𝕄 : ParLangMor ⅀1 ⅀2) →
                (R⇒𝕄 : CtxKndRel⇒ R (𝕄 .mor-rel)) →
                (γ-resp-arg' : ∀{κ} (s : ⅀1 .TyShape) →
                 (βκ : R .β (⅀1 .TyPos s .snd) κ) →
                 R .μ (⅀1 .TyPos s .fst)
                   (⅀2 .TyPos (𝕄 .γ s (R⇒𝕄 .β⇒ βκ)) .fst)) →
                (∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ)
                (p
                : ⅀2 .TyPos (𝕄 .γ s (R⇒𝕄 .β⇒ βκ)) .fst ≡
                  ⅀2 .TyPos (γ 𝕄 s (R⇒𝕄 .β⇒ βκ)) .fst) →
                subst (𝕄 .mor-rel .μ (⅀1 .TyPos s .fst)) p (R⇒𝕄 .μ⇒ (γ-resp-arg' s βκ))
                ≡ γ-resp-arg 𝕄 s (R⇒𝕄 .β⇒ βκ)) →
                (∀{Δ1 Δ2 Γ1 Γ2} (δΔ : R .δ Δ1 Δ2) (αΓ : R .α Γ1 Γ2) →
                  R⇒𝕄 .α⇒ (R .δ-++-α δΔ αΓ) ≡
                  𝕄 .mor-rel .δ-++-α (R⇒𝕄 .δ⇒ δΔ) (R⇒𝕄 .α⇒ αΓ)) →
                ParLangMorPath (restr-mor R 𝕄 R⇒𝕄 γ-resp-arg') 𝕄
mor-rel-⇒ (restr-mor-path 𝕄 R⇒𝕄 γ-resp-arg' γ-resp-arg-≡-Path' δ-++-α-Path') = R⇒𝕄
γ1≗γ2-Path (restr-mor-path 𝕄 R⇒𝕄 γ-resp-arg' γ-resp-arg-≡-Path' δ-++-α-Path') s βκ = refl
γ-resp-arg-≡-Path (restr-mor-path 𝕄 R⇒𝕄 γ-resp-arg' γ-resp-arg-≡-Path' δ-++-α-Path') = γ-resp-arg-≡-Path'
var1≗var2-Path (restr-mor-path 𝕄 R⇒𝕄 γ-resp-arg' γ-resp-arg-≡-Path' δ-++-α-Path') αΓ βκ x = refl
δ-++-α-Path (restr-mor-path 𝕄 R⇒𝕄 γ-resp-arg' γ-resp-arg-≡-Path' δ-++-α-Path') = δ-++-α-Path'

-- Composition of morphisms
infixr 9 _∘ₘ_
_∘ₘ_ : ∀{⅀1 ⅀2 ⅀3} → ParLangMor ⅀2 ⅀3 → ParLangMor ⅀1 ⅀2 → ParLangMor ⅀1 ⅀3
mor-rel (𝕄1 ∘ₘ 𝕄2) = 𝕄1 .mor-rel ∘ᵣₖ 𝕄2 .mor-rel
mor-var (𝕄1 ∘ₘ 𝕄2) (Γ2 , α23 , α12) (κ2 , β23 , β12) x =
  mor 𝕄1 α23 β23 (𝕄2 .mor-var α12 β12 x)
γ (𝕄1 ∘ₘ 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ (𝕄2 .γ s1 β12)
    (subst (flip (𝕄1 .mor-rel .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
γ-ty-≡ (𝕄1 ∘ₘ 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12)
    (subst (flip (𝕄1 .mor-rel .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
γ-resp-arg (_∘ₘ_ {⅀1} {⅀2} {⅀3} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  let
  βs3 : 𝕄1 .mor-rel .β (⅀2 .TyPos (γ 𝕄2 s1 β12) .snd) κ3
  βs3 = subst (flip (𝕄1 .mor-rel .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23
  in
  ⅀2 .TyPos (γ 𝕄2 s1 β12) .fst ,
  𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) βs3 ,
  𝕄2 .γ-resp-arg s1 β12

-- Identity morphism
id-mor : ∀{⅀} → ParLangMor ⅀ ⅀
mor-rel id-mor = id-rel
mor-var (id-mor {⅀}) p q x = var (subst₂ (Var ⅀) p q x)
γ id-mor s p = s
γ-ty-≡ id-mor s p = p
γ-resp-arg id-mor s p = refl

id-is-id : ∀{⅀} → IsParLangMor ⅀ ⅀ id-rel (subst₂ (Tm ⅀)) (subst₂ (TmVec ⅀))
is-γ (id-is-id {⅀}) = id-mor {⅀} .γ
is-γ-ty-≡ (id-is-id {⅀}) = id-mor {⅀} .γ-ty-≡
is-γ-resp-arg id-is-id = id-mor .γ-resp-arg
f-constr id-is-id s refl refl es = refl
f-vec-nil id-is-id refl refl = refl
f-vec-cons (id-is-id {⅀}) {Γ1} {.Γ1} {Δ1} {.Δ1} {κ1} {.κ1} {Σ1} {.Σ1} refl refl e es = refl

id-mor-≡-f-mor-id-is-id : ∀{⅀} → ParLangMorPath {⅀} id-mor (f-mor id-is-id)
mor-rel-⇒ id-mor-≡-f-mor-id-is-id = CtxKndRel⇒-refl id-rel
γ1≗γ2-Path id-mor-≡-f-mor-id-is-id s βκ = refl
γ-resp-arg-≡-Path id-mor-≡-f-mor-id-is-id s βκ refl = refl
var1≗var2-Path id-mor-≡-f-mor-id-is-id refl refl x = refl
δ-++-α-Path id-mor-≡-f-mor-id-is-id δΔ αΓ = refl

id-mor≗id : ∀{⅀ Γ1 Γ2 κ1 κ2} (αΓ : Γ1 ≡ Γ2) (βκ : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
            mor id-mor αΓ βκ e ≡ subst₂ (Tm ⅀) αΓ βκ e
id-mor≗id {⅀} αΓ βκ e =
  mor id-mor αΓ βκ e
    ≡⟨ mor-≡-Path id-mor-≡-f-mor-id-is-id αΓ βκ e ⟩
  mor (f-mor id-is-id) αΓ βκ e
    ≡⟨ (sym $ f-≗-f-mor id-is-id αΓ βκ e) ⟩
  subst₂ (Tm ⅀) αΓ βκ e ∎

erase-id-mor≗id : ∀{⅀ Γ1 Γ2 κ1 κ2} (αΓ : Γ1 ≡ Γ2) (βκ : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
                  erase ⅀ (mor id-mor αΓ βκ e) ≡ erase ⅀ e
erase-id-mor≗id {⅀} αΓ βκ e =
  erase ⅀ (mor id-mor αΓ βκ e)
    ≡⟨ (cong (erase ⅀) $ id-mor≗id αΓ βκ e) ⟩
  erase ⅀ (subst₂ (Tm ⅀) αΓ βκ e)
    ≡⟨ (sym $ subst₂-erase ⅀ αΓ βκ e) ⟩
  erase ⅀ e ∎

-- Composing two morphisms behaves as the composition of morphisms
∘ₘ-is-∘ : ∀{⅀1 ⅀2 ⅀3} (𝕄1 : ParLangMor ⅀2 ⅀3) (𝕄2 : ParLangMor ⅀1 ⅀2) →
          IsParLangMor ⅀1 ⅀3 (𝕄1 .mor-rel ∘ᵣₖ 𝕄2 .mor-rel)
            (λ αΓ βκ e → mor 𝕄1 (αΓ .snd .fst) (βκ .snd .fst) (mor 𝕄2 (αΓ .snd .snd) (βκ .snd .snd) e))
            λ αΓ μΣ es → mor-vec 𝕄1 (αΓ .snd .fst) (μΣ .snd .fst) (mor-vec 𝕄2 (αΓ .snd .snd) (μΣ .snd .snd) es)
is-γ (∘ₘ-is-∘ 𝕄1 𝕄2) = (𝕄1 ∘ₘ 𝕄2) .γ
is-γ-ty-≡ (∘ₘ-is-∘ 𝕄1 𝕄2) = (𝕄1 ∘ₘ 𝕄2) .γ-ty-≡
is-γ-resp-arg (∘ₘ-is-∘ 𝕄1 𝕄2) = (𝕄1 ∘ₘ 𝕄2) .γ-resp-arg
f-constr (∘ₘ-is-∘ {⅀1} {⅀2} {⅀3} 𝕄1 𝕄2) {Γ1} {Γ3} {κ3} s1 (Γ2 , α23 , α12) (κ2 , β23 , β12) es = erase-inj ⅀3 $
  erase ⅀3 (mor 𝕄1 α23 β23
    (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
      (constr (γ 𝕄2 s1 β12)
        (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es))))
    ≡⟨ erase-mor-≡ 𝕄1 α23 β23
        (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
        (constr (γ 𝕄2 s1 β12)
          (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es))) ⟩
  erase-mor 𝕄1 α23 β23
    (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
      (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es)))
    ≡⟨ erase-mor-substTy-≡ 𝕄1 α23 β23
          (γ-ty-≡ 𝕄2 s1 β12)
          (sym (γ-ty-≡ 𝕄2 s1 β12))
          (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es)) ⟩
  constr (𝕄1 .γ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
    (erase-mor-vec 𝕄1 α23
      (𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
      (mor-vec 𝕄2 α12 (𝕄2 .γ-resp-arg s1 β12) es))
    ≡⟨ (cong (constr (𝕄1 .γ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))) $
          sym $ erase-mor-vec-≡ 𝕄1 α23 
            (𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
            (mor-vec 𝕄2 α12 (𝕄2 .γ-resp-arg s1 β12) es)) ⟩
  constr (𝕄1 .γ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
    (eraseVec ⅀3 (mor-vec 𝕄1 α23
      (𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
      (mor-vec 𝕄2 α12 (𝕄2 .γ-resp-arg s1 β12) es)))
    ≡⟨ substTy-erase ⅀3
        (𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
        (constr (𝕄1 .γ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
          (mor-vec 𝕄1 α23
            (𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12)
              (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
            (mor-vec 𝕄2 α12 (𝕄2 .γ-resp-arg s1 β12) es))) ⟩
  erase ⅀3 (subst (Tm ⅀3 Γ3)
    (𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
    (constr (𝕄1 .γ (𝕄2 .γ s1 β12) (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
      (mor-vec 𝕄1 α23
        (𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12)
          (subst (λ x → 𝕄1 .mor-rel .β x κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23))
        (mor-vec 𝕄2 α12 (𝕄2 .γ-resp-arg s1 β12) es)))) ∎
f-vec-nil (∘ₘ-is-∘ 𝕄1 𝕄2) (Γ2 , α23 , α12) ([] , μ23 , μ12) = refl
f-vec-nil (∘ₘ-is-∘ 𝕄1 𝕄2) (Γ2 , α23 , α12) ((Δ2 , κ2) ∷ Σ2 , μ23 , μ12) = ⊥-elim $ 𝕄1 .mor-rel .μ-cons-nil μ23
f-vec-cons (∘ₘ-is-∘ 𝕄1 𝕄2) (Γ2 , α23 , α12) ([] , μ23 , μ12) = ⊥-elim $ 𝕄1 .mor-rel .μ-nil-cons μ23
f-vec-cons (∘ₘ-is-∘ 𝕄1 𝕄2) (Γ2 , α23 , α12) ((Δ2 , κ2) ∷ Σ2 , μ23 , μ12) e es = refl

-- The morphism of the composition is equivalent to the composition of the morphisms
∘ₘ≗∘ : ∀{⅀1 ⅀2 ⅀3} (𝕄1 : ParLangMor ⅀2 ⅀3) (𝕄2 : ParLangMor ⅀1 ⅀2)
       {Γ1 Γ2 κ1 κ2}
       (p : (𝕄1 .mor-rel .α ∘ᵣ 𝕄2 .mor-rel .α) Γ1 Γ2)
       (q : (𝕄1 .mor-rel .β ∘ᵣ 𝕄2 .mor-rel .β) κ1 κ2)
       (e : Tm ⅀1 Γ1 κ1) →
       mor 𝕄1 (p .snd .fst) (q .snd .fst) (mor 𝕄2 (p .snd .snd) (q .snd .snd) e)
       ≡ mor (𝕄1 ∘ₘ 𝕄2) p q e
∘ₘ≗∘ 𝕄1 𝕄2 p q e = f-≗-f-mor (∘ₘ-is-∘ 𝕄1 𝕄2) p q e

∘ₘ-vec≗∘-vec : ∀{⅀1 ⅀2 ⅀3} (𝕄1 : ParLangMor ⅀2 ⅀3) (𝕄2 : ParLangMor ⅀1 ⅀2)
              {Γ1 Γ2 Σ1 Σ2} (p : (𝕄1 .mor-rel .α ∘ᵣ 𝕄2 .mor-rel .α) Γ1 Γ2)
              (q : (𝕄1 .mor-rel .μ ∘ᵣ 𝕄2 .mor-rel .μ) Σ1 Σ2)
              (es : TmVec ⅀1 Γ1 Σ1) →
              mor-vec 𝕄1 (p .snd .fst) (q .snd .fst)
                (mor-vec 𝕄2 (p .snd .snd) (q .snd .snd) es)
              ≡ mor-vec (𝕄1 ∘ₘ 𝕄2) p q es
∘ₘ-vec≗∘-vec 𝕄1 𝕄2 p q es = f-vec-≗-f-mor-vec (∘ₘ-is-∘ 𝕄1 𝕄2) p q es

-- Renaming morphism
ren-rel : ∀{⅀} → CtxKndRel ⅀ ⅀
α (ren-rel {⅀}) = Ren ⅀
β (ren-rel {⅀}) = _≡_
δ (ren-rel {⅀}) = _≡_
μ (ren-rel {⅀}) = _≡_
δ-++-α (ren-rel {⅀}) {Δ1} {.Δ1} {Γ1} {Γ2} refl ξ = Keep* ⅀ ξ Δ1
μ-nil (ren-rel {⅀}) = refl
μ-head-δ (ren-rel {⅀}) p = ,-injective (∷-injective p .fst) .fst
μ-head-β (ren-rel {⅀}) p = ,-injective (∷-injective p .fst) .snd
μ-tail (ren-rel {⅀}) p = ∷-injective p .snd
μ-cons-nil (ren-rel {⅀}) = cons≢nil
μ-nil-cons (ren-rel {⅀}) = nil≢cons

ren-mor : ∀{⅀} → ParLangMor ⅀ ⅀
mor-rel (ren-mor {⅀}) = ren-rel
mor-var (ren-mor {⅀}) ξ p x = subst (Tm ⅀ _) p (var (renVar ⅀ ξ x))
γ (ren-mor {⅀}) s p = s
γ-ty-≡ (ren-mor {⅀}) s p = p
γ-resp-arg (ren-mor {⅀}) s p = refl

ren-is-ren : ∀{⅀} → IsParLangMor ⅀ ⅀ ren-rel
                      (λ {Γ1} {Γ2} ξ p e → subst (Tm ⅀ Γ2) p (ren ⅀ ξ e))
                      λ {Γ1} {Γ2} ξ p es → subst (TmVec ⅀ Γ2) p (renVec ⅀ ξ es)
is-γ (ren-is-ren {⅀}) = ren-mor {⅀} .γ
is-γ-ty-≡ (ren-is-ren {⅀}) = ren-mor {⅀} .γ-ty-≡
is-γ-resp-arg (ren-is-ren {⅀}) = ren-mor {⅀} .γ-resp-arg
f-constr (ren-is-ren {⅀}) s ξ refl es = refl
f-vec-nil (ren-is-ren {⅀}) ξ refl = refl
f-vec-cons (ren-is-ren {⅀}) ξ refl e es = refl

ren-mor-≡-f-mor-ren-is-ren : ∀{⅀} → ParLangMorPath {⅀} ren-mor (f-mor ren-is-ren)
mor-rel-⇒ ren-mor-≡-f-mor-ren-is-ren = CtxKndRel⇒-refl ren-rel
γ1≗γ2-Path ren-mor-≡-f-mor-ren-is-ren s refl = refl
γ-resp-arg-≡-Path ren-mor-≡-f-mor-ren-is-ren s refl refl = refl
var1≗var2-Path ren-mor-≡-f-mor-ren-is-ren ξ refl x = refl
δ-++-α-Path ren-mor-≡-f-mor-ren-is-ren p ξ = refl

ren-mor≗ren : ∀{⅀ Γ1 Γ2 κ1 κ2} (ξ : Ren ⅀ Γ1 Γ2) (p : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
              mor ren-mor ξ p e ≡ subst (Tm ⅀ Γ2) p (ren ⅀ ξ e)
ren-mor≗ren {⅀} {Γ1} {Γ2} {κ1} {κ2} ξ p e =
  mor ren-mor ξ p e
    ≡⟨ mor-≡-Path ren-mor-≡-f-mor-ren-is-ren ξ p e ⟩
  mor (f-mor ren-is-ren) ξ p e
    ≡⟨ (sym $ f-≗-f-mor ren-is-ren ξ p e) ⟩
  subst (Tm ⅀ Γ2) p (ren ⅀ ξ e) ∎

erase-ren-mor≗ren : ∀{⅀ Γ1 Γ2 κ1 κ2} (ξ : Ren ⅀ Γ1 Γ2) (p : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
                    erase-mor ren-mor ξ p e ≡ erase ⅀ (ren ⅀ ξ e)
erase-ren-mor≗ren {⅀} {Γ1} {Γ2} {κ1} {κ2} ξ p e =
  erase-mor ren-mor ξ p e
    ≡⟨ (sym $ erase-mor-≡ ren-mor ξ p e) ⟩
  erase ⅀ (mor ren-mor ξ p e)
    ≡⟨ (cong (erase ⅀) $ ren-mor≗ren ξ p e) ⟩
  erase ⅀ (subst (Tm ⅀ Γ2) p (ren ⅀ ξ e))
    ≡⟨ (sym $ substTy-erase ⅀ p (ren ⅀ ξ e)) ⟩
  erase ⅀ (ren ⅀ ξ e) ∎

-- Substitution morphism
sub-rel : ∀{⅀} → CtxKndRel ⅀ ⅀
α (sub-rel {⅀}) = Sub ⅀
β sub-rel = _≡_
δ sub-rel = _≡_
μ sub-rel = _≡_
δ-++-α (sub-rel {⅀}) {Δ1 = Δ1} refl σ = KeepSub* ⅀ σ Δ1
μ-nil sub-rel = refl
μ-head-δ sub-rel refl = refl
μ-head-β sub-rel refl = refl
μ-tail sub-rel refl = refl
μ-cons-nil sub-rel = cons≢nil
μ-nil-cons sub-rel = nil≢cons

sub-mor : ∀{⅀} → ParLangMor ⅀ ⅀
mor-rel (sub-mor {⅀}) = sub-rel {⅀}
mor-var (sub-mor {⅀}) σ p x = subst (Tm ⅀ _) p (subVar ⅀ σ x)
γ sub-mor s p = s
γ-ty-≡ sub-mor s p = p
γ-resp-arg sub-mor s p = refl

sub-is-sub : ∀{⅀} → IsParLangMor ⅀ ⅀ sub-rel
                    (λ {Γ1} {Γ2} σ p e → subst (Tm ⅀ Γ2) p (sub ⅀ σ e))
                    (λ {Γ1} {Γ2} σ p es → subst (TmVec ⅀ Γ2) p (subVec ⅀ σ es))
is-γ (sub-is-sub {⅀}) = sub-mor {⅀} .γ
is-γ-ty-≡ (sub-is-sub {⅀}) = sub-mor {⅀} .γ-ty-≡
is-γ-resp-arg (sub-is-sub {⅀}) = sub-mor {⅀} .γ-resp-arg
f-constr sub-is-sub s σ p es = refl
f-vec-nil sub-is-sub σ refl = refl
f-vec-cons sub-is-sub σ refl e es = refl

sub-mor-≡-f-mor-sub-is-sub : ∀{⅀} → ParLangMorPath {⅀} sub-mor (f-mor sub-is-sub)
mor-rel-⇒ sub-mor-≡-f-mor-sub-is-sub = CtxKndRel⇒-refl sub-rel
γ1≗γ2-Path sub-mor-≡-f-mor-sub-is-sub s p = refl
γ-resp-arg-≡-Path sub-mor-≡-f-mor-sub-is-sub s refl refl = refl
var1≗var2-Path sub-mor-≡-f-mor-sub-is-sub σ p x = refl
δ-++-α-Path sub-mor-≡-f-mor-sub-is-sub p σ = refl

sub-mor≗sub : ∀{⅀ Γ1 Γ2 κ1 κ2} (σ : Sub ⅀ Γ1 Γ2) (p : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
              mor sub-mor σ p e ≡ subst (Tm ⅀ Γ2) p (sub ⅀ σ e)
sub-mor≗sub {⅀} {Γ1} {Γ2} {κ1} {κ2} σ p e =
  mor sub-mor σ p e
    ≡⟨ mor-≡-Path sub-mor-≡-f-mor-sub-is-sub σ p e ⟩
  mor (f-mor sub-is-sub) σ p e
    ≡⟨ (sym $ f-≗-f-mor sub-is-sub σ p e) ⟩
  subst (Tm ⅀ Γ2) p (sub ⅀ σ e) ∎

sub-mor-vec≗sub-vec : ∀{⅀ Γ1 Γ2 Σ1 Σ2} (σ : Sub ⅀ Γ1 Γ2) (p : Σ1 ≡ Σ2)
                      (es : TmVec ⅀ Γ1 Σ1) →
                      mor-vec sub-mor σ p es ≡
                      subst (TmVec ⅀ Γ2) p (subVec ⅀ σ es)
sub-mor-vec≗sub-vec {⅀} {Γ1} {Γ2} {Σ1} {Σ2} σ p es =
  mor-vec sub-mor σ p es
    ≡⟨ mor-vec-≡-Path sub-mor-≡-f-mor-sub-is-sub σ p es ⟩
  mor-vec (f-mor sub-is-sub) σ p es
    ≡⟨ (sym $ f-vec-≗-f-mor-vec sub-is-sub σ p es) ⟩
  subst (TmVec ⅀ Γ2) p (subVec ⅀ σ es) ∎

erase-sub-mor≗sub : ∀{⅀ Γ1 Γ2 κ1 κ2} (σ : Sub ⅀ Γ1 Γ2) (p : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
                    erase-mor sub-mor σ p e ≡ erase ⅀ (sub ⅀ σ e)
erase-sub-mor≗sub {⅀} {Γ1} {Γ2} {κ1} {κ2} σ p e =
  erase-mor sub-mor σ p e
    ≡⟨ (sym $ erase-mor-≡ sub-mor σ p e) ⟩
  erase ⅀ (mor sub-mor σ p e)
    ≡⟨ (cong (erase ⅀) $ sub-mor≗sub σ p e) ⟩
  erase ⅀ (subst (Tm ⅀ Γ2) p (sub ⅀ σ e))
    ≡⟨ (sym $ substTy-erase ⅀ p (sub ⅀ σ e)) ⟩
  erase ⅀ (sub ⅀ σ e) ∎
