{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
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

-- Custom equational reasoning for functions
module FunExt {a b} {A : Set a} {B : A → Set b} where
  infix 4 _≈_
  _≈_ : (f g : (x : A) → B x) → Set (ℓ-max a b)
  f ≈ g = ∀ x → f x ≡ g x

  ≈-refl : Reflexive _≈_
  ≈-refl x = refl

  ≈-sym : Symmetric _≈_
  ≈-sym p x = sym (p x)

  ≈-trans : Transitive _≈_
  ≈-trans p q x = trans (p x) (q x)

  infix  3 _∎'
  infixr 2 _≈⟨⟩_ step-≈ step-≈˘

  _≈⟨⟩_ : ∀ (x {y} : (x : A) → B x) → x ≈ y → x ≈ y
  _ ≈⟨⟩ x≡y = x≡y

  step-≈ : ∀ (x {y z} : (x : A) → B x) → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ y≡z x≡y = ≈-trans x≡y y≡z

  step-≈˘ : ∀ (x {y z} : (x : A) → B x) → y ≈ z → y ≈ x → x ≈ z
  step-≈˘ _ y≡z y≡x = ≈-trans (≈-sym y≡x) y≡z

  _∎' : ∀ (x : (x : A) → B x) → x ≈ x
  _∎' _ = ≈-refl

  syntax step-≈  x y≡z x≡y = x ≈⟨  x≡y ⟩ y≡z
  syntax step-≈˘ x y≡z y≡x = x ≈˘⟨ y≡x ⟩ y≡z

  
open FunExt public
