{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Empty
open import Data.Unit
open import Data.List
open import Function

open ≡-Reasoning

module Common.Equality where

nil≢cons : ∀{a} {A : Set a} {x : A} {xs : List A} → [] ≢ x ∷ xs
nil≢cons ()

cons≢nil : ∀{a} {A : Set a} {x : A} {xs : List A} → x ∷ xs ≢ []
cons≢nil ()

-- Cubical syntax for transitivity
infixr 30 _∙_
_∙_ : ∀{a} {A : Set a} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

•-idᵣ : ∀{a} {A : Set a} {x y : A}
        (p : x ≡ y) → p ∙ refl ≡ p
•-idᵣ refl = refl        

-- Explicit uniqueness of identity proofs/Axiom-K lemma
UIP : ∀{a} {A : Set a} {x y : A}
      (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

J : ∀{a ℓ} {A : Set a} {x : A} (P : (y : A) → x ≡ y → Set ℓ) →
    (d : P x refl) →
    (y : A) (p : x ≡ y) → P y p
J P d x refl = d

-- Propositions
isProp : ∀{a} → Set a → Set a
isProp A = (x y : A) → x ≡ y

≡-isProp : ∀{a} {A : Set a} {x y : A} → isProp (x ≡ y)
≡-isProp = UIP

⊥-isProp : isProp ⊥
⊥-isProp ()

⊤-isProp : isProp ⊤
⊤-isProp tt tt = refl

×-isProp : ∀{a b} {A : Set a} {B : Set b} →
           isProp A → isProp B → isProp (A × B)
×-isProp A-prop B-prop (x1 , y1) (x2 , y2) = cong₂ _,_ (A-prop x1 x2) (B-prop y1 y2)           

Σ-isProp : ∀{a b} {A : Set a} {B : A → Set b} →
            (∀ x1 x2 → B x1 → B x2 → x1 ≡ x2) →
            ((x : A) → isProp (B x)) →
            isProp (Σ[ x ∈ A ] (B x))
Σ-isProp fst-uniq snd-prop (x1 , y1) (x2 , y2) with fst-uniq x1 x2 y1 y2
Σ-isProp fst-uniq snd-prop (x1 , y1) (x1 , y2) | refl = cong (x1 ,_) (snd-prop x1 y1 y2)

Lift-isProp : ∀{a ℓ} {A : Set a} → isProp A → isProp (Lift ℓ A)
Lift-isProp A-prop (lift x) (lift y) = cong lift (A-prop x y)

-- Transport across equal types
transport : ∀{a} {A B : Set a} → A ≡ B → A → B
transport refl x = x

transport-∘ : ∀{a} {A B C : Set a}
              (p : A ≡ B) (q : B ≡ C) →
              transport q ∘ transport p
              ≗ transport (p ∙ q)
transport-∘ refl refl x = refl

transport-cong : ∀{a b} {A : Set a} {x y : A}
                 (B : A → Set b) (p : x ≡ y) →
                 transport (cong B p) ≗ subst B p
transport-cong B refl Bx = refl

cong-sym : ∀{a b} {A : Set a} {B : Set b} {x y : A}
           (f : A → B) (p : x ≡ y) →
           cong f (sym p) ≡ sym (cong f p)
cong-sym f refl = refl

cong₃ : ∀{a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        {x1 x2 : A} {y1 y2 : B} {z1 z2 : C} →
        (f : A → B → C → D) → x1 ≡ x2 → y1 ≡ y2 → z1 ≡ z2 →
        f x1 y1 z1 ≡ f x2 y2 z2
cong₃ f refl refl refl = refl

subst₃ : ∀{a b c ℓ} {A : Set a} {B : Set b} {C : Set c}
         (P : A → B → C → Set ℓ) {x y : A} {u v : B} {w z : C} →
         x ≡ y → u ≡ v → w ≡ z → P x u w → P y v z
subst₃ P refl refl refl p = p         

subst₂-reflₗ : ∀{a b ℓ} {A : Set a} {x : A} {B : Set b} {y1 y2 : B}
               (P : A → B → Set ℓ) (p : y1 ≡ y2) (v : P x y1) →
               subst₂ P refl p v ≡ subst (P x) p v
subst₂-reflₗ P refl v = refl

subst₂-reflᵣ : ∀{a b ℓ} {A : Set a} {x1 x2 : A} {B : Set b} {y : B}
               (P : A → B → Set ℓ) (p : x1 ≡ x2) (v : P x1 y) →
               subst₂ P p refl v ≡ subst (flip P y) p v
subst₂-reflᵣ P refl v = refl

-- Prove two pairs are equal by proving their elements are equal
Σ-≡-→-≡-Σ : ∀{a b} {A : Set a} {B : A → Set b} {x1 x2 : A} {y1 : B x1} {y2 : B x2} →
            (p : x1 ≡ x2) → subst B p y1 ≡ y2 → (x1 , y1) ≡ (x2 , y2)
Σ-≡-→-≡-Σ refl refl = refl

subst-× : ∀{a b d} {D : Set d}
          (A : D → Set a) (B : D → Set b)
          {x y : D} (p : x ≡ y) (Ax : A x) (Bx : B x) →
          subst (λ x → A x × B x) p (Ax , Bx)
          ≡ (subst A p Ax , subst B p Bx)
subst-× A B refl Ax Bx = refl

subst-Σ-fst : ∀{a b d} {D : Set d}
              (A : D → Set a) (B : (d : D) → A d → Set b)
              {x y : D} (p : x ≡ y) (Ax : A x) (Bx : B x Ax) →
              subst (λ x → Σ[ y ∈ A x ] B x y) p (Ax , Bx) .fst
              ≡ subst A p Ax
subst-Σ-fst A B refl Ax Bx = refl

subst-≡ : ∀{a b} {A : Set a} {B : Set b}
          (f g : A → B)
          {x y : A} (p : x ≡ y) (q : f x ≡ g x) →
          subst (λ x → f x ≡ g x) p q
          ≡ sym (cong f p) ∙ q ∙ cong g p
subst-≡ f g refl q = sym $ •-idᵣ q

subst-const : ∀{a b} {A : Set a} {B : Set b}
              {x y : A} (p : x ≡ y) (b : B) →
              subst (λ x → B) p b ≡ b
subst-const refl b = refl

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

≡⇒≗ : ∀{a b} {A : Set a} {B : Set b} {f g : A → B} →
        f ≡ g → f ≗ g
≡⇒≗ p x = cong (λ y → y x) p