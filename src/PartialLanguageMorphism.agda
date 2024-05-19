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

-- Identity relation
id-rel : ∀ ⅀ → CtxKndRel ⅀ ⅀
α (id-rel ⅀) Γ1 Γ2 = Γ1 ≡ Γ2
β (id-rel ⅀) κ1 κ2 = κ1 ≡ κ2
α-++ (id-rel ⅀) refl refl = refl

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
    γ : ⅀1 .TyShape → ⅀2 .TyShape
    -- γ respects constructor types
    γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) →
              R .β (⅀1 .TyPos s .snd) κ →
              ⅀2 .TyPos (γ s) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) →
                 R .β (⅀1 .TyPos s .snd) κ →
                 ⋆ (R .α ×ᵣ R .β)
                  (⅀1 .TyPos s .fst)
                  (⅀2 .TyPos (γ s) .fst)

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
      constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es))

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
    constr (γ s) (erase-mor-vec αΓ (γ-resp-arg s βκ) es)

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
        constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es)))
      ≡⟨ sym (substTy-erase ⅀2 (γ-ty-≡ s βκ) (
          constr (γ s) (mor-vec αΓ (γ-resp-arg s βκ) es))) ⟩
    constr (γ s) (eraseVec ⅀2 (mor-vec αΓ (γ-resp-arg s βκ) es))
      ≡⟨ cong (constr (γ s)) (erase-mor-vec-≡ αΓ (γ-resp-arg s βκ) es) ⟩
    constr (γ s) (erase-mor-vec αΓ (γ-resp-arg s βκ) es) ∎

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
      subst (⋆ (R .α ×ᵣ R .β) (⅀1 .TyPos s .fst)) (
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

-- Identity morphism
id-mor : ∀ ⅀ → ParLangMor ⅀ ⅀ (id-rel ⅀)
mor-var (id-mor ⅀) refl refl x = var x
γ (id-mor ⅀) s = s
γ-ty-≡ (id-mor ⅀) s refl = refl
γ-resp-arg (id-mor ⅀) s refl =
  ⋆-pres-refl (
    ×ᵣ-pres-refl {A = List (⅀ .Knd)} {⅀ .Knd} {_≡_} {_≡_}
      refl
      refl)

-- Functions which behave as a morphism
record IsParLangMor (⅀1 ⅀2 : SecondOrderSignature) (R : CtxKndRel ⅀1 ⅀2)
  (f : ∀{Γ1 Γ2 κ1 κ2} → R .α Γ1 Γ2 → R .β κ1 κ2 → Tm ⅀1 Γ1 κ1 → Tm ⅀2 Γ2 κ2)
  (f-vec : ∀{Γ1 Γ2 Σ1 Σ2} → R .α Γ1 Γ2 → ⋆ (R .α ×ᵣ R .β) Σ1 Σ2 → TmVec ⅀1 Γ1 Σ1 → TmVec ⅀2 Γ2 Σ2)
  : Set where
  field
    -- How constructors are mapped under the morphism
    is-γ : ⅀1 .TyShape → ⅀2 .TyShape
    -- γ respects constructor types
    is-γ-ty-≡ : ∀{κ} (s : ⅀1 .TyShape) →
                R .β (⅀1 .TyPos s .snd) κ →
                ⅀2 .TyPos (is-γ s) .snd ≡ κ
    -- γ preserves relatedness of constructor argument types
    is-γ-resp-arg : ∀{κ} (s : ⅀1 .TyShape) →
                 R .β (⅀1 .TyPos s .snd) κ →
                 ⋆ (R .α ×ᵣ R .β)
                  (⅀1 .TyPos s .fst)
                  (⅀2 .TyPos (is-γ s) .fst)

    -- Use γ to replace the constructor
    f-constr : ∀{Γ1 Γ2 κ} (s : ⅀1 .TyShape) (αΓ : R .α Γ1 Γ2) (βκ : R .β (⅀1 .TyPos s .snd) κ)
               (es : TmVec ⅀1 Γ1 (⅀1 .TyPos s .fst)) →
               f αΓ βκ (constr s es) ≡
               subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ) (
                 constr (is-γ s) (f-vec αΓ (is-γ-resp-arg s βκ) es))
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
      (constr (is-γ s) (f-vec αΓ (is-γ-resp-arg s βκ) es))
      ≡⟨ cong (λ x → subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ) (constr (is-γ s) x))
          (f-vec-≗-f-mor-vec αΓ (is-γ-resp-arg s βκ) es) ⟩
    subst (Tm ⅀2 Γ2) (is-γ-ty-≡ s βκ)
      (constr (is-γ s) (mor-vec f-mor αΓ (is-γ-resp-arg s βκ) es)) ∎

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
γ (𝕄1 ∘ₘ 𝕄2) = 𝕄1 .γ ∘ 𝕄2 .γ
γ-ty-≡ (_∘ₘ_ {R = R} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ-ty-≡ (𝕄2 .γ s1) (
    subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
γ-resp-arg (_∘ₘ_ {⅀1} {⅀2} {⅀3} {R} {S} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) = let
  Pos[γ1[s2]]≡κ2 : ⅀2 .TyPos (𝕄2 .γ s1) .snd ≡ κ2
  Pos[γ1[s2]]≡κ2 = 𝕄2 .γ-ty-≡ s1 β12

  Pos[γ1[γ2[s1]]]≡κ3 : ⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .snd ≡ κ3
  Pos[γ1[γ2[s1]]]≡κ3 =
    𝕄1 .γ-ty-≡ (𝕄2 .γ s1) (
      subst (flip (R .β) κ3) (sym Pos[γ1[s2]]≡κ2) β23)

  Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] : R .β (⅀2 .TyPos (𝕄2 .γ s1) .snd) (⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .snd)
  Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] = subst₂ (R .β) (sym Pos[γ1[s2]]≡κ2) (sym Pos[γ1[γ2[s1]]]≡κ3) β23
  in
  ⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
    {⅀1 .TyPos s1 .fst} {⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .fst}
    (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) 
      {⅀1 .TyPos s1 .fst} {⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .fst}
      (⅀2 .TyPos (γ 𝕄2 s1) .fst ,
      𝕄1 .γ-resp-arg (𝕄2 .γ s1) Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] ,
      𝕄2 .γ-resp-arg s1 β12))

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
is-γ (∘ₘ-is-∘ 𝕄1 𝕄2) = 𝕄1 .γ ∘ 𝕄2 .γ
is-γ-ty-≡ (∘ₘ-is-∘ {R = R} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  𝕄1 .γ-ty-≡ (𝕄2 .γ s1) (
    subst (flip (R .β) κ3) (sym (𝕄2 .γ-ty-≡ s1 β12)) β23)
is-γ-resp-arg (∘ₘ-is-∘ {⅀1} {⅀2} {⅀3} {R} {S} 𝕄1 𝕄2) {κ3} s1 (κ2 , β23 , β12) =
  let
  Pos[γ1[s2]]≡κ2 : ⅀2 .TyPos (𝕄2 .γ s1) .snd ≡ κ2
  Pos[γ1[s2]]≡κ2 = 𝕄2 .γ-ty-≡ s1 β12

  Pos[γ1[γ2[s1]]]≡κ3 : ⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .snd ≡ κ3
  Pos[γ1[γ2[s1]]]≡κ3 =
    𝕄1 .γ-ty-≡ (𝕄2 .γ s1) (
      subst (flip (R .β) κ3) (sym Pos[γ1[s2]]≡κ2) β23)

  Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] : R .β (⅀2 .TyPos (𝕄2 .γ s1) .snd) (⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .snd)
  Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] = subst₂ (R .β) (sym Pos[γ1[s2]]≡κ2) (sym Pos[γ1[γ2[s1]]]≡κ3) β23
  in
  ⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
    {⅀1 .TyPos s1 .fst} {⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .fst}
    (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      {⅀1 .TyPos s1 .fst} {⅀3 .TyPos (𝕄1 .γ (𝕄2 .γ s1)) .fst}
      (⅀2 .TyPos (γ 𝕄2 s1) .fst ,
      𝕄1 .γ-resp-arg (𝕄2 .γ s1) Pos[γ2[s1]]-R-Pos[γ1[γ2[s1]]] ,
      𝕄2 .γ-resp-arg s1 β12))
f-constr (∘ₘ-is-∘ {⅀1} {⅀2} {⅀3} {R} {S} 𝕄1 𝕄2) {Γ1} {Γ3} {κ3} s (Γ2 , α23 , α12) (κ2 , β23 , βs2) es
  with 𝕄2 .γ-ty-≡ s βs2 | inspect (𝕄2 .γ-ty-≡ s) βs2
... | refl | eq1 with 𝕄1 .γ-ty-≡ (𝕄2 .γ s) β23 | inspect (𝕄1 .γ-ty-≡ (𝕄2 .γ s)) β23
... | refl | eq2 =
  let
  αβ*s2 : (⋆ (R .α ×ᵣ R .β) ∘ᵣ ⋆ (S .α ×ᵣ S .β))
          (⅀1 .TyPos s .fst)
          (⅀3 .TyPos (γ 𝕄1 (𝕄2 .γ s)) .fst)
  αβ*s2 =
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒ (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
        (⋆-pres-⇒ (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
          (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
            (⅀2 .TyPos (γ 𝕄2 s) .fst ,
            𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
            𝕄2 .γ-resp-arg s βs2))))
  αβ*s1 : (⋆ (R .α ×ᵣ R .β) ∘ᵣ ⋆ (S .α ×ᵣ S .β))
          (⅀1 .TyPos s .fst)
          (⅀3 .TyPos (γ 𝕄1 (𝕄2 .γ s)) .fst)
  αβ*s1 =
    ⅀2 .TyPos (γ 𝕄2 s) .fst ,
    𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
    𝕄2 .γ-resp-arg s βs2
  eq : αβ*s2 ≡ αβ*s1
  eq =
    αβ*s2
      ≡⟨ (cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
          ⋆-pres-⇒-∘
            (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
            (∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
            (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
              (⅀2 .TyPos (γ 𝕄2 s) .fst ,
              𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
              𝕄2 .γ-resp-arg s βs2))) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒
        (×ᵣ-∘ᵣ-⇒ (R .α) (S .α) (R .β) (S .β) ∘
          ∘ᵣ-×ᵣ-⇒ (R .α) (S .α) (R .β) (S .β))
          (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
            (⅀2 .TyPos (γ 𝕄2 s) .fst ,
            𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
            𝕄2 .γ-resp-arg s βs2)))
      ≡⟨ (cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
          ⋆-pres-⇒-ext (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (R .α) (S .α) (R .β) (S .β) _ _ .retract)
          (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
            (⅀2 .TyPos (γ 𝕄2 s) .fst ,
            𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
            𝕄2 .γ-resp-arg s βs2))) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (⋆-pres-⇒ id
          (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
            (⅀2 .TyPos (γ 𝕄2 s) .fst ,
            𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
            𝕄2 .γ-resp-arg s βs2)))
      ≡⟨ (cong (⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)) $
            ⋆-pres-⇒-id 
              (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
              (⅀2 .TyPos (γ 𝕄2 s) .fst ,
              𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
              𝕄2 .γ-resp-arg s βs2))) ⟩
    ⋆-∘ᵣ-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
      (∘ᵣ-⋆-⇒ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β)
        (⅀2 .TyPos (γ 𝕄2 s) .fst ,
        𝕄1 .γ-resp-arg (𝕄2 .γ s) β23 ,
        𝕄2 .γ-resp-arg s βs2))
      ≡⟨ ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (R .α ×ᵣ R .β) (S .α ×ᵣ S .β) _ _ .section αβ*s1 ⟩
    αβ*s1 ∎
  in
  constr (γ 𝕄1 (γ 𝕄2 s))
    (mor-vec 𝕄1 α23 (αβ*s1 .snd .fst)
      (mor-vec 𝕄2 α12 (αβ*s1 .snd .snd) es))
    ≡⟨ cong (λ x → constr (γ 𝕄1 (γ 𝕄2 s))
        (mor-vec 𝕄1 α23 (x .snd .fst)
          (mor-vec 𝕄2 α12 (x .snd .snd) es)))
        (sym eq) ⟩
  constr (γ 𝕄1 (γ 𝕄2 s))
    (mor-vec 𝕄1 α23 (αβ*s2 .snd .fst)
      (mor-vec 𝕄2 α12 (αβ*s2 .snd .snd) es)) ∎
f-vec-nil (∘ₘ-is-∘ 𝕄1 𝕄2) αΓ = refl
f-vec-cons (∘ₘ-is-∘ 𝕄1 𝕄2) αΓ αΔ βκ αβ*Σ e es = cong₂ _∷_ refl refl

-- The morphism of the composition is equivalent to the composition of the morphisms
∘ₘ≗∘ : ∀{⅀1 ⅀2 ⅀3 R S} (𝕄1 : ParLangMor ⅀2 ⅀3 R) (𝕄2 : ParLangMor ⅀1 ⅀2 S)
       {Γ1 Γ2 κ1 κ2} (p : (R .α ∘ᵣ S .α) Γ1 Γ2) (q : (R .β ∘ᵣ S .β) κ1 κ2) (e : Tm ⅀1 Γ1 κ1) →
       mor 𝕄1 (p .snd .fst) (q .snd .fst) (mor 𝕄2 (p .snd .snd) (q .snd .snd) e)
       ≡ mor (𝕄1 ∘ₘ 𝕄2) p q e
∘ₘ≗∘ 𝕄1 𝕄2 p q e = f-≗-f-mor (∘ₘ-is-∘ 𝕄1 𝕄2) p q e