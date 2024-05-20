{-# OPTIONS --safe #-}

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Sum  renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Data.List
open import Data.List.Properties
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
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
    -- α respects context concatenation
    α-++ : ∀{Γ1 Γ2 Γ1' Γ2'} → α Γ1 Γ1' → α Γ2 Γ2' → α (Γ1 ++ Γ2) (Γ1' ++ Γ2')

open CtxKndRel public

record CtxKndRel≡ {⅀1 ⅀2} (R S : CtxKndRel ⅀1 ⅀2) : Set₁ where
  field
    α≅ : R .α ≅ᵣ S .α
    β≅ : R .β ≅ᵣ S .β

open CtxKndRel≡ public

-- Identity relation
id-rel : ∀{⅀} → CtxKndRel ⅀ ⅀
α id-rel Γ1 Γ2 = Γ1 ≡ Γ2
β id-rel κ1 κ2 = κ1 ≡ κ2
α-++ id-rel refl refl = refl

-- Composition of context and kind relations
_∘ᵣₖ_ : ∀{⅀1 ⅀2 ⅀3} → CtxKndRel ⅀2 ⅀3 → CtxKndRel ⅀1 ⅀2 → CtxKndRel ⅀1 ⅀3
α (R ∘ᵣₖ S) = R .α ∘ᵣ S .α
β (R ∘ᵣₖ S) = R .β ∘ᵣ S .β
α-++ (R ∘ᵣₖ S) (Γ3 , α31' , α13) (Γ4 , α42' , α24) =
  Γ3 ++ Γ4 , R .α-++ α31' α42' , S .α-++ α13 α24

-- Partial language morphisms over a given context and kind relation
record ParLangMor (⅀1 ⅀2 : SecondOrderSignature) (R : CtxKndRel ⅀1 ⅀2) : Set where
  field
    -- How the morphism acts on variables
    mor-var : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
              Var ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
    -- How constructors are mapped under the morphism
    γ : ∀{κ} (s : ⅀1 .TyShape) → R .β (⅀1 .TyPos s .snd) κ →  ⅀2 .TyShape
    -- γ respects constructor types
    γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) →
              (p : R .β (⅀1 .TyPos s .snd) κ) →
              ⅀2 .TyPos (γ s p) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) →
                 (p : R .β (⅀1 .TyPos s .snd) κ) →
                 ⋆ (R .α ×ᵣ R .β)
                  (⅀1 .TyPos s .fst)
                  (⅀2 .TyPos (γ s p) .fst)

  -- The definition of the morphism
  mor : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
        Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2
  mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → ⋆ (R .α ×ᵣ R .β) Σ1 Σ2 →
            TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2

  -- Variables act as specified
  mor αΓ βκ (var x) = mor-var αΓ βκ x
  -- Use γ to replace the constructor
  mor {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) =
    subst (Tm ⅀2 Γ2) (γ-ty-≡ s βκ) (
      constr (γ s βκ) (mor-vec αΓ (γ-resp-arg s βκ) es))

  -- The morphism acts identically on subterms
  mor-vec {Σ1 = []} {[]} p q [] = []
  mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    mor (R .α-++ αΔ αΓ) βκ e ∷ mor-vec αΓ αβ*Σ es

  -- Explicitly erased version of the morphism
  erase-mor : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 →
              Tm ⅀1 Γ1 κ1 → UTm ⅀2
  erase-mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → ⋆ (R .α ×ᵣ R .β) Σ1 Σ2 →
                  TmVec ⅀1 Γ1 Σ1 → UTmVec ⅀2

  erase-mor αΓ βκ (var x) = erase ⅀2 (mor-var αΓ βκ x)
  erase-mor αΓ βκ (constr s es) =
    constr (γ s βκ) (erase-mor-vec αΓ (γ-resp-arg s βκ) es)

  erase-mor-vec {Σ1 = []} {[]} αΓ (lift tt) [] = []
  erase-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    (erase-mor (R .α-++ αΔ αΓ) βκ e , length Δ2) ∷ erase-mor-vec αΓ αβ*Σ es

  -- The explicitly erased morphism acts the same as
  -- applying the morphism and then erasing
  erase-mor-≡ : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) →
                (e : Tm ⅀1 Γ1 κ1) → erase ⅀2 (mor αΓ βκ e) ≡ erase-mor αΓ βκ e
  erase-mor-vec-≡ : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2) →
                    (es : TmVec ⅀1 Γ1 Σ1) → eraseVec ⅀2 (mor-vec αΓ αβ*Σ es) ≡ erase-mor-vec αΓ αβ*Σ es

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

  erase-mor-vec-≡ {Σ1 = []} {[]} αΓ (lift tt) [] = refl
  erase-mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    cong₃ (eraseCons ⅀2)
      (erase-mor-≡ (R .α-++ αΔ αΓ) βκ e)
      refl
      (erase-mor-vec-≡ αΓ αβ*Σ es)
  
  -- Substituting the proof of relatedness has no effect on the erased morphism
  erase-mor-vec-subst-≡ : ∀{Γ1 Γ2 Σ1 Σ2 Σ2'} (αΓ : R .α Γ1 Γ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2)
                          (p : Σ2 ≡ Σ2') (es : TmVec ⅀1 Γ1 Σ1) →
                          erase-mor-vec αΓ (subst (⋆ (R .α ×ᵣ R .β) Σ1) p αβ*Σ) es
                          ≡ erase-mor-vec αΓ αβ*Σ es
  erase-mor-vec-subst-≡ αΓ αβ*Σ refl es = refl

  erase-mor-substTy-≡ : ∀{Γ1 Γ2 κ1 κ1' κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1' κ2)
                        (p : κ1 ≡ κ1') (q : κ1' ≡ κ1) (e : Tm ⅀1 Γ1 κ1) →
                        erase-mor αΓ βκ (subst (Tm ⅀1 Γ1) p e)
                        ≡ erase-mor αΓ (subst (flip (R .β) κ2) q βκ) e
  erase-mor-substTy-≡ αΓ βκ refl refl e = refl

open ParLangMor public

{-
To prove two language morphisms over isomorphic context and kind
relation are equivalent, it suffices to prove that they are
equivalent on variables and constructors with the
explicit isomorphism between the relations being applied
-}
record ParLangMor≡ {⅀1 ⅀2 : SecondOrderSignature} {R : CtxKndRel ⅀1 ⅀2}
  (𝕄1 𝕄2 : ParLangMor ⅀1 ⅀2 R) : Set where
  field
    -- The modified constructors will be identical
    γ1≗γ2 : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ) →
            γ 𝕄1 s βκ ≡ γ 𝕄2 s βκ
    -- The proofs that constructors preserve relatedness are equivalent
    γ-resp-arg-≡ : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ)
                   (p : ⅀2 .TyPos (γ 𝕄1 s βκ) .fst ≡ ⅀2 .TyPos (γ 𝕄2 s βκ) .fst) →
                   subst (⋆ (R .α ×ᵣ R .β) (⅀1 .TyPos s .fst)) p (γ-resp-arg 𝕄1 s βκ)
                   ≡ γ-resp-arg 𝕄2 s βκ
    -- The morphisms are identical on variables
    var1≗var2 : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (x : Var ⅀1 Γ1 κ1) →
                mor-var 𝕄1 αΓ βκ x ≡ mor-var 𝕄2 αΓ βκ x

  -- The morphisms are identical on all terms
  mor-≡ : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
          mor 𝕄1 αΓ βκ e ≡ mor 𝕄2 αΓ βκ e
  mor-vec-≡ : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2) (es : TmVec ⅀1 Γ1 Σ1) →
              mor-vec 𝕄1 αΓ αβ*Σ es ≡ mor-vec 𝕄2 αΓ αβ*Σ es

  mor-≡ αΓ βκ (var x) = var1≗var2 αΓ βκ x
  mor-≡ {Γ1} {Γ2} {.(⅀1 .TyPos s .snd)} {κ2} αΓ βκ (constr s es) = erase-inj ⅀2 $
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄1 s βκ)
        (constr (γ 𝕄1 s βκ) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ 𝕄1 s βκ)
          (constr (γ 𝕄1 s βκ) (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))) ⟩
    constr (γ 𝕄1 s βκ) (eraseVec ⅀2 (mor-vec 𝕄1 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (λ x → constr (γ 𝕄1 s βκ) (eraseVec ⅀2 x)) (
          mor-vec-≡ αΓ (γ-resp-arg 𝕄1 s βκ) es) ⟩
    constr (γ 𝕄1 s βκ) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (λ x → constr x (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))) 
          (γ1≗γ2 s βκ) ⟩
    constr (γ 𝕄2 s βκ) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es))
      ≡⟨ cong (constr (γ 𝕄2 s βκ)) (erase-mor-vec-≡ 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es) ⟩
    constr (γ 𝕄2 s βκ) (erase-mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) es)
      ≡⟨ cong (constr (γ 𝕄2 s βκ)) (sym (
          erase-mor-vec-subst-≡ 𝕄2 αΓ (γ-resp-arg 𝕄1 s βκ) (
            cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ))
          es)) ⟩
    constr (γ 𝕄2 s βκ) (erase-mor-vec 𝕄2 αΓ (
      subst (⋆ (R .α ×ᵣ R .β) (⅀1 .TyPos s .fst)) (
        cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ)) (γ-resp-arg 𝕄1 s βκ))
      es)
      ≡⟨ cong (λ x → constr (γ 𝕄2 s βκ) (erase-mor-vec 𝕄2 αΓ x es))
          (γ-resp-arg-≡ s βκ (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2 s βκ))) ⟩
    constr (γ 𝕄2 s βκ) (erase-mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)
      ≡⟨ sym (cong (constr (γ 𝕄2 s βκ)) (erase-mor-vec-≡ 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)) ⟩
    constr (γ 𝕄2 s βκ) (eraseVec ⅀2 (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es))
      ≡⟨ substTy-erase ⅀2 (γ-ty-≡ 𝕄2 s βκ)
          (constr (γ 𝕄2 s βκ) (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es)) ⟩
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s βκ)
        (constr (γ 𝕄2 s βκ) (mor-vec 𝕄2 αΓ (γ-resp-arg 𝕄2 s βκ) es))) ∎

  mor-vec-≡ {Σ1 = []} {[]} αΓ αβ*Σ [] = refl
  mor-vec-≡ {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    cong₂ _∷_
      (mor-≡ (R .α-++ αΔ αΓ) βκ e)
      (mor-vec-≡ αΓ αβ*Σ es)

open ParLangMor≡ public

record ParLangMorPath {⅀1 ⅀2 : SecondOrderSignature} {R S : CtxKndRel ⅀1 ⅀2}
  (R≅S : CtxKndRel≡ R S)
  (𝕄1 : ParLangMor ⅀1 ⅀2 R) (𝕄2 : ParLangMor ⅀1 ⅀2 S) : Set where
  field
    -- The modified constructors will be identical
    γ1≗γ2-Path : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ) →
                 γ 𝕄1 s βκ ≡ γ 𝕄2 s (R≅S .β≅ _ _ .forward βκ)
    -- The proofs that constructors preserve relatedness are equivalent
    γ-resp-arg-≡-Path : ∀{Σ} (s : ⅀1 .TyShape) (βκ : R .β (⅀1 .TyPos s .snd) Σ)
                        (p : ⅀2 .TyPos (γ 𝕄1 s βκ) .fst ≡ ⅀2 .TyPos (γ 𝕄2 s (R≅S .β≅ _ _ .forward βκ)) .fst) →
                        subst (⋆ (S .α ×ᵣ S .β) (⅀1 .TyPos s .fst)) p
                          (⋆-pres-⇒
                            (×ᵣ-pres-⇒
                              (λ {x} {y} → R≅S .α≅ x y .forward)
                              (λ {x} {y} → R≅S .β≅ x y .forward))
                            (γ-resp-arg 𝕄1 s βκ))
                        ≡ γ-resp-arg 𝕄2 s (R≅S .β≅ _ _ .forward βκ)

    -- The morphisms are identical on variables
    var1≗var2-Path : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (x : Var ⅀1 Γ1 κ1) →
                     mor-var 𝕄1 αΓ βκ x ≡
                     mor-var 𝕄2 (R≅S .α≅ _ _ .forward αΓ) (R≅S .β≅ _ _ .forward βκ) x

    α-++-Path : ∀{Δ1 Δ2 Γ1 Γ2} (αΔ : R .α Δ1 Δ2) (αΓ : R .α Γ1 Γ2) →
      R≅S .α≅ (Δ1 ++ Γ1) (Δ2 ++ Γ2) .forward (R .α-++ αΔ αΓ) ≡
      S .α-++
        (R≅S .α≅ Δ1 Δ2 .forward αΔ)
        (R≅S .α≅ Γ1 Γ2 .forward αΓ)

  -- The morphisms are identical on all terms
  mor-≡-Path : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
              mor 𝕄1 αΓ βκ e ≡
              mor 𝕄2 (R≅S .α≅ _ _ .forward αΓ) (R≅S .β≅ _ _ .forward βκ) e
  mor-vec-≡-Path : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2) (es : TmVec ⅀1 Γ1 Σ1) →
                   mor-vec 𝕄1 αΓ αβ*Σ es ≡
                   mor-vec 𝕄2
                    (R≅S .α≅ _ _ .forward αΓ)
                    (⋆-pres-⇒ (×ᵣ-pres-⇒ (λ {x} {y} → R≅S .α≅ x y .forward) λ {x} {y} → R≅S .β≅ x y .forward) αβ*Σ)
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
        (mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
          (⋆-pres-⇒
            (×ᵣ-pres-⇒
              (λ {x} {y} → R≅S .α≅ x y .forward)
              (λ {x} {y} → R≅S .β≅ x y .forward))
            (γ-resp-arg 𝕄1 s βκ))
          es))
      ≡⟨ cong (λ x → constr x (eraseVec ⅀2
          (mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
            (⋆-pres-⇒
              (×ᵣ-pres-⇒
                (λ {x} {y} → R≅S .α≅ x y .forward)
                (λ {x} {y} → R≅S .β≅ x y .forward))
              (γ-resp-arg 𝕄1 s βκ))
            es))) 
          (γ1≗γ2-Path s βκ) ⟩
    constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (eraseVec ⅀2
        (mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
          (⋆-pres-⇒
            (×ᵣ-pres-⇒
              (λ {x} {y} → R≅S .α≅ x y .forward)
              (λ {x} {y} → R≅S .β≅ x y .forward))
            (γ-resp-arg 𝕄1 s βκ))
          es))
      ≡⟨ (cong (constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))) $
          erase-mor-vec-≡ 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
          (⋆-pres-⇒
            (×ᵣ-pres-⇒
              (λ {x} {y} → R≅S .α≅ x y .forward)
              (λ {x} {y} → R≅S .β≅ x y .forward))
            (γ-resp-arg 𝕄1 s βκ))
          es) ⟩
    constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (erase-mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
        (⋆-pres-⇒
          (×ᵣ-pres-⇒
            (λ {x} {y} → R≅S .α≅ x y .forward)
            (λ {x} {y} → R≅S .β≅ x y .forward))
          (γ-resp-arg 𝕄1 s βκ))
        es)
      ≡⟨ (cong (constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))) $
          sym $ erase-mor-vec-subst-≡ 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
            (⋆-pres-⇒
            (×ᵣ-pres-⇒
              (λ {x} {y} → R≅S .α≅ x y .forward)
              (λ {x} {y} → R≅S .β≅ x y .forward))
            (γ-resp-arg 𝕄1 s βκ))
            (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))
            es) ⟩
    constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (erase-mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
        (subst (⋆ (S .α ×ᵣ S .β) (⅀1 .TyPos s .fst))
          (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))
          (⋆-pres-⇒
            (×ᵣ-pres-⇒
              (λ {x} {y} → R≅S .α≅ x y .forward)
              (λ {x} {y} → R≅S .β≅ x y .forward))
            (γ-resp-arg 𝕄1 s βκ)))
        es)
      ≡⟨ (cong (λ x → constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
            (erase-mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ) x es)) $
          γ-resp-arg-≡-Path s βκ (cong (λ x → ⅀2 .TyPos x .fst) (γ1≗γ2-Path s βκ))) ⟩
    constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (erase-mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
        (γ-resp-arg 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
        es)
      ≡⟨ (cong (constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))) $
          sym $ erase-mor-vec-≡ 𝕄2 
            (R≅S .α≅ Γ1 Γ2 .forward αΓ)
            (γ-resp-arg 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
            es) ⟩
    constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (eraseVec ⅀2
        (mor-vec 𝕄2
          (R≅S .α≅ Γ1 Γ2 .forward αΓ)
          (γ-resp-arg 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ)) es))
      ≡⟨ substTy-erase ⅀2 (γ-ty-≡ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
          (constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
            (mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
              (γ-resp-arg 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ)) es)) ⟩
    erase ⅀2
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
      (constr (γ 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ))
        (mor-vec 𝕄2 (R≅S .α≅ Γ1 Γ2 .forward αΓ)
        (γ-resp-arg 𝕄2 s (R≅S .β≅ (⅀1 .TyPos s .snd) κ2 .forward βκ)) es))) ∎

  mor-vec-≡-Path {Σ1 = []} {[]}  αΓ αβ*Σ [] = refl
  mor-vec-≡-Path {Γ1} {Γ2} {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    cong₂ _∷_
      (mor 𝕄1 (R .α-++ αΔ αΓ) βκ e
        ≡⟨ mor-≡-Path (R .α-++ αΔ αΓ) βκ e ⟩
      mor 𝕄2
        (R≅S .α≅ (Δ1 ++ Γ1) (Δ2 ++ Γ2) .forward (R .α-++ αΔ αΓ))
        (R≅S .β≅ κ1 κ2 .forward βκ)
        e
        ≡⟨ cong (λ x → mor 𝕄2 x (R≅S .β≅ κ1 κ2 .forward βκ) e) (α-++-Path αΔ αΓ) ⟩
      mor 𝕄2
        (S .α-++
          (R≅S .α≅ Δ1 Δ2 .forward αΔ)
          (R≅S .α≅ Γ1 Γ2 .forward αΓ))
        (R≅S .β≅ κ1 κ2 .forward βκ)
        e ∎)
      (mor-vec-≡-Path αΓ αβ*Σ es)

open ParLangMorPath public

-- Extend a function on terms to a function on vectors
to-vec-fun : {⅀1 ⅀2 : SecondOrderSignature} (R : CtxKndRel ⅀1 ⅀2) →
             (∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 → Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2) →
             ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → ⋆ (R .α ×ᵣ R .β) Σ1 Σ2 → TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2
to-vec-fun R f {Σ1 = []} {[]} αΓ αβ*Σ [] = []
to-vec-fun R f {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
  f (R .α-++ αΔ αΓ) βκ e ∷ to-vec-fun R f αΓ αβ*Σ es

-- Functions which behave as a morphism
record IsParLangMor (⅀1 ⅀2 : SecondOrderSignature) (R : CtxKndRel ⅀1 ⅀2)
  (f : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 → Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2)
  (f-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → ⋆ (R .α ×ᵣ R .β) Σ1 Σ2 → TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2)
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
                    ⋆ (R .α ×ᵣ R .β)
                      (⅀1 .TyPos s .fst)
                      (⅀2 .TyPos (is-γ s βκ) .fst)

    -- Use γ to replace the constructor
    f-constr : ∀{Γ1 Γ2 κ} (s : ⅀1 .TyShape) (αΓ : R .α Γ1 Γ2) (βκ : R .β (⅀1 .TyPos s .snd) κ)
               (es : TmVec ⅀1 Γ1 (⅀1 .TyPos s .fst)) →
               f αΓ βκ (constr s es) ≡
               subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ) (
                 constr (is-γ s βκ) (f-vec αΓ (is-γ-resp-arg s βκ) es))
    -- The morphism acts identically on subterms
    f-vec-nil : ∀{Γ1 Γ2} (αΓ : R .α Γ1 Γ2) → f-vec αΓ (lift tt) [] ≡ []
    f-vec-cons : ∀{Γ1 Γ2 Δ1 Δ2 κ1 κ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αΔ : R .α Δ1 Δ2)
                  (βκ : R .β κ1 κ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2)
                  (e : Tm ⅀1 (Δ1 ++ Γ1) κ1) (es : TmVec ⅀1 Γ1 Σ1) →
                  f-vec αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) ≡
                  f (R .α-++ αΔ αΓ) βκ e ∷ f-vec αΓ αβ*Σ es

  -- The morphism that f is equivalent to
  f-mor : ParLangMor ⅀1 ⅀2 R
  mor-var f-mor αΓ βκ x = f αΓ βκ (var x)
  γ f-mor = is-γ
  γ-ty-≡ f-mor s βκ = is-γ-ty-≡ s βκ
  γ-resp-arg f-mor s βκ = is-γ-resp-arg s βκ

  -- f is extensionally equivalent to this morphism
  f-≗-f-mor : ∀{Γ1 Γ2 κ1 κ2} (αΓ : R .α Γ1 Γ2) (βκ : R .β κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
              f αΓ βκ e ≡ mor f-mor αΓ βκ e
  f-vec-≗-f-mor-vec : ∀{Γ1 Γ2 Σ1 Σ2} (αΓ : R .α Γ1 Γ2) (αβ*Σ : ⋆ (R .α ×ᵣ R .β) Σ1 Σ2)
                      (es : TmVec ⅀1 Γ1 Σ1) → f-vec αΓ αβ*Σ es ≡ mor-vec f-mor αΓ αβ*Σ es

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

  f-vec-≗-f-mor-vec {Σ1 = []} {[]} αΓ (lift tt) [] = f-vec-nil αΓ
  f-vec-≗-f-mor-vec {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es) =
    f-vec αΓ ((αΔ , βκ) , αβ*Σ) (e ∷ es)
      ≡⟨ f-vec-cons αΓ αΔ βκ αβ*Σ e es ⟩
    f (R .α-++ αΔ αΓ) βκ e ∷ f-vec αΓ αβ*Σ es
      ≡⟨ cong₂ _∷_ (f-≗-f-mor (R .α-++ αΔ αΓ) βκ e) (f-vec-≗-f-mor-vec αΓ αβ*Σ es) ⟩
    mor f-mor (R .α-++ αΔ αΓ) βκ e ∷ mor-vec f-mor αΓ αβ*Σ es ∎

open IsParLangMor public

-- Composition of morphisms
_∘ₘ_ : ∀{⅀1 ⅀2 ⅀3 R S} → ParLangMor ⅀2 ⅀3 R → ParLangMor ⅀1 ⅀2 S → ParLangMor ⅀1 ⅀3 (R ∘ᵣₖ S)
mor-var (𝕄1 ∘ₘ 𝕄2) (Γ2 , α23 , α12) (κ2 , β23 , β12) x =
  mor 𝕄1 α23 β23 (𝕄2 .mor-var α12 β12 x)
γ (_∘ₘ_ {R = R} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ (𝕄2 .γ s1 β12)
    (subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
γ-ty-≡ (_∘ₘ_ {R = R} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12)
    (subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
γ-resp-arg (_∘ₘ_ {⅀1} {⅀2} {⅀3} {R} {S} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  let
  eq1 : ⅀2 .TyPos (𝕄2 .γ s1 β12) .snd ≡ κ2
  eq1 = 𝕄2 .γ-ty-≡ s1 β12

  βs3 : R .β (⅀2 .TyPos (γ 𝕄2 s1 β12) .snd) κ3
  βs3 = subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23

  eq2 : ⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1 β12) βs3) .snd ≡ κ3
  eq2 = 𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) βs3
  in
  ⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
    (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⅀2 .TyPos (γ 𝕄2 s1 β12) .fst ,
      𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) βs3 ,
      𝕄2 .γ-resp-arg s1 β12))


-- Identity morphism
id-mor : ∀{⅀} → ParLangMor ⅀ ⅀ id-rel
mor-var (id-mor {⅀}) p q x = var (subst₂ (Var ⅀) p q x)
γ id-mor s p = s
γ-ty-≡ id-mor s p = p
γ-resp-arg (id-mor {⅀}) s p =
  ⋆-pres-refl (
    ×ᵣ-pres-refl {A = List (⅀ .Knd)} {⅀ .Knd} {_≡_} {_≡_}
      refl
      refl)

id-is-id : ∀{⅀} → IsParLangMor ⅀ ⅀ id-rel
                    (λ p q e → subst₂ (Tm ⅀) p q e)
                    (λ p q es → subst₂ (TmVec ⅀) p (⋆≡-≅-≡ _ _ .forward (⋆-pres-≅ᵣ {S = _≡_} ×ᵣ≡-≅-≡ _ _ .forward q)) es)
is-γ (id-is-id {⅀}) = id-mor {⅀} .γ
is-γ-ty-≡ (id-is-id {⅀}) = id-mor {⅀} .γ-ty-≡
is-γ-resp-arg id-is-id = id-mor .γ-resp-arg
f-constr (id-is-id {⅀}) s refl refl es =
  cong (constr s) $
  eraseVec-inj ⅀ $
  subst₂-eraseVec ⅀ refl _ es
f-vec-nil id-is-id refl = refl
f-vec-cons (id-is-id {⅀}) {Γ1} {.Γ1} {Δ1} {.Δ1} {κ1} {.κ1} {Σ1} {Σ2} refl refl refl s e es =
  eraseVec-inj ⅀ $
  eraseVec ⅀
  (subst₂ (TmVec ⅀) refl
    (cong₂ _∷_ refl (⋆≡-≅-≡-forward Σ1 Σ2 (⋆-pres-≅ᵣ ×ᵣ≡-≅-≡ Σ1 Σ2 .forward s)))
    (e ∷ es))
    ≡⟨ sym $ subst₂-eraseVec ⅀ refl
        (cong₂ _∷_ refl (⋆≡-≅-≡-forward Σ1 Σ2 (⋆-pres-≅ᵣ ×ᵣ≡-≅-≡ Σ1 Σ2 .forward s)))
        (e ∷ es) ⟩
  (erase ⅀ e , length Δ1) ∷ eraseVec ⅀ es
    ≡⟨ cong₂ _∷_ refl $
      subst₂-eraseVec ⅀ refl (⋆≡-≅-≡-forward Σ1 Σ2 (⋆-pres-≅ᵣ ×ᵣ≡-≅-≡ Σ1 Σ2 .forward s)) es ⟩
  (erase ⅀ e , length Δ1) ∷
    eraseVec ⅀
    (subst₂ (TmVec ⅀) refl
      (⋆≡-≅-≡-forward Σ1 Σ2 (⋆-pres-≅ᵣ ×ᵣ≡-≅-≡ Σ1 Σ2 .forward s))
      es) ∎

id-mor-≡-f-mor-id-is-id : ∀{⅀} → ParLangMor≡ {⅀} id-mor (f-mor id-is-id)
γ1≗γ2 id-mor-≡-f-mor-id-is-id s p = refl
γ-resp-arg-≡ id-mor-≡-f-mor-id-is-id s refl refl = refl
var1≗var2 id-mor-≡-f-mor-id-is-id refl refl x = refl

id-mor≗id : ∀{⅀ Γ1 Γ2 κ1 κ2} (αΓ : Γ1 ≡ Γ2) (βκ : κ1 ≡ κ2) (e : Tm ⅀ Γ1 κ1) →
            mor id-mor αΓ βκ e ≡ subst₂ (Tm ⅀) αΓ βκ e
id-mor≗id {⅀} αΓ βκ e =
  mor id-mor αΓ βκ e
    ≡⟨ mor-≡ id-mor-≡-f-mor-id-is-id αΓ βκ e ⟩
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
∘ₘ-is-∘ : ∀{⅀1 ⅀2 ⅀3 R S} (𝕄1 : ParLangMor ⅀2 ⅀3 R) (𝕄2 : ParLangMor ⅀1 ⅀2 S) →
          IsParLangMor ⅀1 ⅀3 (R ∘ᵣₖ S)
            (λ αΓ βκ e → mor 𝕄1 (αΓ .snd .fst) (βκ .snd .fst) (mor 𝕄2 (αΓ .snd .snd) (βκ .snd .snd) e))
            λ αΓ αβ*Σ es → mor-vec 𝕄1 (αΓ .snd .fst)
              (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
                  (⋆-pres-⇒ (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β)) αβ*Σ) .snd .fst)
              (mor-vec 𝕄2 (αΓ .snd .snd)
                (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
                  (⋆-pres-⇒ (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β)) αβ*Σ) .snd .snd)
                es)
is-γ (∘ₘ-is-∘ 𝕄1 𝕄2) = (𝕄1 ∘ₘ 𝕄2) .γ
is-γ-ty-≡ (∘ₘ-is-∘ 𝕄1 𝕄2) {κ3} = (𝕄1 ∘ₘ 𝕄2) .γ-ty-≡
is-γ-resp-arg (∘ₘ-is-∘ 𝕄1 𝕄2) = (𝕄1 ∘ₘ 𝕄2) .γ-resp-arg
f-constr (∘ₘ-is-∘ {⅀1} {⅀2} {⅀3} {R} {S} 𝕄1 𝕄2) {Γ1} {Γ3} {κ3} s1 (Γ2 , α23 , α12) (κ2 , β23 , β12) es =
  let
  eq1 : ⅀2 .TyPos (𝕄2 .γ s1 β12) .snd ≡ κ2
  eq1 = 𝕄2 .γ-ty-≡ s1 β12

  βs3 : R .β (⅀2 .TyPos (γ 𝕄2 s1 β12) .snd) κ3
  βs3 = subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23

  eq2 : ⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1 β12) βs3) .snd ≡ κ3
  eq2 = 𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) βs3

  β-ty : Set
  β-ty = (⋆ (R .α ×ᵣ R .β) ∘ᵣ ⋆ (S .α ×ᵣ S .β))
            (⅀1 .TyPos s1 .fst)
            (⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1 β12) βs3) .fst)

  β-fun : β-ty → β-ty
  β-fun =
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) ∘
    ⋆-pres-⇒ (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β)) ∘
    ⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β)) ∘
    ∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)

  β-fun≗id : β-fun ≗ id
  β-fun≗id x =
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒ (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
        (⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
          (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x)))
      ≡⟨ cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
          ⋆-pres-⇒-∘
            (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
            (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
            (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒
        (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β) ∘
        ∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
        (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x))
      ≡⟨ cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
          ⋆-pres-⇒-ext
            (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (R .α) (S .α) (R .β) (S .β) _ _ .retract)
            (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒ id
        (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x))
      ≡⟨ cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
          ⋆-pres-⇒-id (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) x)
      ≡⟨ ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) _ _ .section x ⟩
    x ∎

  αβ*s : (⋆ (R .α ×ᵣ R .β) ∘ᵣ ⋆ (S .α ×ᵣ S .β))
            (⅀1 .TyPos s1 .fst)
            (⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1 β12) βs3) .fst)
  αβ*s =
    ⅀2 .TyPos (γ 𝕄2 s1 β12) .fst ,
    𝕄1 .γ-resp-arg (𝕄2 .γ s1 β12) βs3 ,
    𝕄2 .γ-resp-arg s1 β12
  in erase-inj ⅀3 $ 
  erase ⅀3
    (mor 𝕄1 α23 β23
      (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
        (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es))))
    ≡⟨ erase-mor-≡ 𝕄1 α23 β23
        (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
          (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es))) ⟩
  erase-mor 𝕄1 α23 β23
    (subst (Tm ⅀2 Γ2) (γ-ty-≡ 𝕄2 s1 β12)
      (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es)))
    ≡⟨ erase-mor-substTy-≡ 𝕄1 α23 β23 (γ-ty-≡ 𝕄2 s1 β12) (sym (γ-ty-≡ 𝕄2 s1 β12))
        (constr (γ 𝕄2 s1 β12) (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es)) ⟩
  constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
    (erase-mor-vec 𝕄1 α23
      (γ-resp-arg 𝕄1 (γ 𝕄2 s1 β12) βs3)
      (mor-vec 𝕄2 α12 (γ-resp-arg 𝕄2 s1 β12) es))
    ≡⟨ cong (λ x → constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
        (erase-mor-vec 𝕄1 α23
          (x .snd .fst)
          (mor-vec 𝕄2 α12 (x .snd .snd) es))) $
        sym $ β-fun≗id αβ*s ⟩
  constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
    (erase-mor-vec 𝕄1 α23
      (β-fun αβ*s .snd .fst)
      (mor-vec 𝕄2 α12 (β-fun αβ*s .snd .snd) es))
    ≡⟨ sym $ cong (constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)) $
        erase-mor-vec-≡ 𝕄1 α23 (β-fun αβ*s .snd .fst)
          (mor-vec 𝕄2 α12 (β-fun αβ*s .snd .snd) es) ⟩
  constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
    (eraseVec ⅀3
      (mor-vec 𝕄1 α23 (β-fun αβ*s .snd .fst)
        (mor-vec 𝕄2 α12 (β-fun αβ*s .snd .snd) es)))
    ≡⟨ substTy-erase ⅀3 (𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) βs3) 
        (constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
          (mor-vec 𝕄1 α23 (β-fun αβ*s .snd .fst)
            (mor-vec 𝕄2 α12 (β-fun αβ*s .snd .snd) es))) ⟩
  erase ⅀3
    (subst (Tm ⅀3 Γ3) (𝕄1 .γ-ty-≡ (𝕄2 .γ s1 β12) βs3)
      (constr (γ 𝕄1 (γ 𝕄2 s1 β12) βs3)
        (mor-vec 𝕄1 α23 (β-fun αβ*s .snd .fst)
          (mor-vec 𝕄2 α12 (β-fun αβ*s .snd .snd) es)))) ∎
f-vec-nil (∘ₘ-is-∘ 𝕄1 𝕄2) αΓ = refl
f-vec-cons (∘ₘ-is-∘ 𝕄1 𝕄2) αΓ αΔ βκ αβ*Σ e es = refl

-- The morphism of the composition is equivalent to the composition of the morphisms
∘ₘ≗∘ : ∀{⅀1 ⅀2 ⅀3 R S} (𝕄1 : ParLangMor ⅀2 ⅀3 R) (𝕄2 : ParLangMor ⅀1 ⅀2 S)
       {Γ1 Γ2 κ1 κ2} (p : (R .α ∘ᵣ S .α) Γ1 Γ2) (q : (R .β ∘ᵣ S .β) κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
       mor 𝕄1 (p .snd .fst) (q .snd .fst) (mor 𝕄2 (p .snd .snd) (q .snd .snd) e)
       ≡ mor (𝕄1 ∘ₘ 𝕄2) p q e
∘ₘ≗∘ 𝕄1 𝕄2 p q e = f-≗-f-mor (∘ₘ-is-∘ 𝕄1 𝕄2) p q e
