{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

module Common where

-- Cubical syntax for transitivity
infixr 30 _∙_
_∙_ : ∀{a} {A : Set a} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

-- Explicit uniqueness of identity proofs/Axiom-K lemma
UIP : ∀{a} {A : Set a} {x y : A}
      (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

cong-sym : ∀{a b} {A : Set a} {B : Set b} {x y : A}
           (f : A → B) (p : x ≡ y) →
           cong f (sym p) ≡ sym (cong f p)
cong-sym f refl = refl

-- Custom equational reasoning for functions
module FunExt {a b} {A : Set a} {B : Set b} where
  ≗-refl : {f : A → B} → f ≗ f
  ≗-refl x = refl

  ≗-sym : {f g : A → B} → f ≗ g → g ≗ f
  ≗-sym p x = sym (p x)

  ≗-trans : {f g h : A → B} → f ≗ g → g ≗ h → f ≗ h
  ≗-trans p q x = p x ∙ q x

  infix  3 _∎'
  infixr 2 _≗⟨⟩_ step-≗ step-≗⁻

  _≗⟨⟩_ : ∀ (x {y} : A → B) → x ≗ y → x ≗ y
  _ ≗⟨⟩ x≡y = x≡y

  step-≗ : ∀ (x {y z} : A → B) → y ≗ z → x ≗ y → x ≗ z
  step-≗ _ y≡z x≡y = ≗-trans x≡y y≡z

  step-≗⁻ : ∀ (x {y z} : A → B) → y ≗ z → y ≗ x → x ≗ z
  step-≗⁻ _ y≡z y≡x = ≗-trans (≗-sym y≡x) y≡z

  _∎' : ∀ (x : A → B) → x ≗ x
  _∎' _ = ≗-refl

  syntax step-≗  x y≡z x≡y = x ≗⟨  x≡y ⟩ y≡z
  syntax step-≗⁻ x y≡z y≡x = x ≗⁻⟨ y≡x ⟩ y≡z

open FunExt public