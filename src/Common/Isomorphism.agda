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

module Common.Isomorphism where

-- Isomorphisms between sets
infix 4 _≅_
record _≅_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward : A → B
    backward : B → A
    section : backward ∘ forward ≗ id
    retract : forward ∘ backward ≗ id

open _≅_ public

-- Isomorphism forms an equivalence relation
≅-refl : ∀{a} {A : Set a} → A ≅ A
forward (≅-refl {A = A}) x = x
backward (≅-refl {A = A}) x = x
section (≅-refl {A = A}) x = refl
retract (≅-refl {A = A}) x = refl

≅-sym : ∀{a b} {A : Set a} {B : Set b} → A ≅ B → B ≅ A
forward (≅-sym p) = p .backward
backward (≅-sym p) = p .forward
section (≅-sym p) = p .retract
retract (≅-sym p) = p .section

≅-trans : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} →
          A ≅ B → B ≅ C → A ≅ C
forward (≅-trans p q) = q .forward ∘ p .forward
backward (≅-trans p q) = p .backward ∘ q .backward
section (≅-trans p q) x =
  p .backward (q .backward (q .forward (p .forward x)))
    ≡⟨ cong (p .backward) (q .section (p .forward x)) ⟩
  p .backward (p .forward x)
    ≡⟨ p .section x ⟩
  x ∎
retract (≅-trans p q) z =
  q .forward (p .forward (p .backward (q .backward z)))
    ≡⟨ cong (q .forward) (p .retract (q .backward z)) ⟩
  q .forward (q .backward z)
    ≡⟨ q .retract z ⟩
  z ∎          

infix  3 _≅∎
infixr 2 _≅⟨⟩_ step-≅ step-≅˘

_≅⟨⟩_ : ∀{a b} (A : Set a) {B : Set b} → A ≅ B → A ≅ B
_ ≅⟨⟩ A≅B = A≅B

step-≅ : ∀{a b c} (A : Set a) {B : Set b} {C : Set c} →
          B ≅ C → A ≅ B → A ≅ C
step-≅ _ B≅C A≅B = ≅-trans A≅B B≅C

step-≅˘ : ∀{a b c} (A : Set a) {B : Set b} {C : Set c} →
          B ≅ C → B ≅ A → A ≅ C
step-≅˘ _ B≅C B≅A = ≅-trans (≅-sym B≅A) B≅C

_≅∎ : ∀{a} (A : Set a) → A ≅ A
_≅∎ _ = ≅-refl

syntax step-≅  A B≅C A≅B = A ≅⟨  A≅B ⟩ B≅C
syntax step-≅˘ A B≅C B≅A = A ≅˘⟨ B≅A ⟩ B≅C

×-≅ : ∀{a1 a2 b1 b2} {A1 : Set a1} {A2 : Set a2}
           {B1 : Set b1} {B2 : Set b2} →
           A1 ≅ A2 → B1 ≅ B2 → (A1 × B1) ≅ (A2 × B2)
forward (×-≅ p q) (x1 , y1) = p .forward x1 , q .forward y1
backward (×-≅ p q) (x2 , y2) = p .backward x2 , q .backward y2
section (×-≅ p q) (x1 , y1) = cong₂ _,_ (p .section x1) (q .section y1)
retract (×-≅ p q) (x2 , y2) = cong₂ _,_ (p .retract x2) (q .retract y2)

⊎-≅ : ∀{a1 a2 b1 b2} {A1 : Set a1} {A2 : Set a2}
      {B1 : Set b1} {B2 : Set b2} →
      A1 ≅ A2 → B1 ≅ B2 → (A1 ⊎ B1) ≅ (A2 ⊎ B2)
forward (⊎-≅ p q) (inl x1) = inl (p .forward x1)
forward (⊎-≅ p q) (inr y1) = inr (q .forward y1)
backward (⊎-≅ p q) (inl x2) = inl (p .backward x2)
backward (⊎-≅ p q) (inr y2) = inr (q .backward y2)
section (⊎-≅ p q) (inl x1) = cong inl (p .section x1)
section (⊎-≅ p q) (inr y1) = cong inr (q .section y1)
retract (⊎-≅ p q) (inl x2) = cong inl (p .retract x2)
retract (⊎-≅ p q) (inr y2) = cong inr (q .retract y2)

Σ-×-Σ-≅ : ∀{a b ℓ1 ℓ2} (A : Set a) (P : A → Set ℓ1)
          (B : Set b) (Q : B → Set ℓ2) →
          ((Σ[ x ∈ A ] (P x)) × (Σ[ y ∈ B ] (Q y))) ≅ 
          (Σ[ x ∈ A ] Σ[ y ∈ B ] (P x × Q y))
forward (Σ-×-Σ-≅ A P B Q) ((x , Px) , (y , Qy)) = x , y , Px , Qy
backward (Σ-×-Σ-≅ A P B Q) (x , y , Px , Qy) = (x , Px) , (y , Qy)
section (Σ-×-Σ-≅ A P B Q) ((x , Px) , (y , Qy)) = refl
retract (Σ-×-Σ-≅ A P B Q) (x , y , Px , Qy) = refl

Σ-List-≅ : ∀{a ℓ} (A : Set a) (P : List A → Set ℓ) →
            (Σ[ xs ∈ List A ] (P xs)) ≅
            (P [] ⊎ (Σ[ x ∈ A ] Σ[ xs ∈ List A ] (P (x ∷ xs))))
forward (Σ-List-≅ A P) ([] , P[]) = inl P[]
forward (Σ-List-≅ A P) (x ∷ xs , Px∷xs) = inr (x , xs , Px∷xs)
backward (Σ-List-≅ A P) (inl P[]) = [] , P[]
backward (Σ-List-≅ A P) (inr (x , xs , Px∷xs)) = x ∷ xs , Px∷xs
section (Σ-List-≅ A P) ([] , P[]) = refl
section (Σ-List-≅ A P) (x ∷ xs , Px∷xs) = refl
retract (Σ-List-≅ A P) (inl P[]) = refl
retract (Σ-List-≅ A P) (inr (x , xs , Px∷xs)) = refl

⊥-×-≅ : ∀{a b} {A : Set a} → (A → ⊥) → (B : Set b) → (A × B) ≅ ⊥
forward (⊥-×-≅ ¬A B) (x , y) = ⊥-elim (¬A x)
backward (⊥-×-≅ ¬A B) ()
section (⊥-×-≅ ¬A B) (x , y) = ⊥-elim (¬A x)
retract (⊥-×-≅ ¬A B) ()

⊥-⊎-≅ : ∀{a b} {A : Set a} → (A → ⊥) → (B : Set b) → (A ⊎ B) ≅ B
forward (⊥-⊎-≅ ¬A B) (inl x) = ⊥-elim (¬A x)
forward (⊥-⊎-≅ ¬A B) (inr y) = y
backward (⊥-⊎-≅ ¬A B) y = inr y
section (⊥-⊎-≅ ¬A B) (inl x) = ⊥-elim (¬A x)
section (⊥-⊎-≅ ¬A B) (inr y) = refl
retract (⊥-⊎-≅ ¬A B) y = refl

×-comm : ∀{a b} (A : Set a) (B : Set b) →
         (A × B) ≅ (B × A)
forward (×-comm A B) (x , y) = y , x 
backward (×-comm A B) (y , x) = x , y
section (×-comm A B) (x , y) = refl
retract (×-comm A B) (y , x) = refl

×-assoc : ∀{a b c} (A : Set a) (B : Set b) (C : Set c) →
          ((A × B) × C) ≅ (A × B × C)
forward (×-assoc A B C) ((x , y) , z) = x , y , z 
backward (×-assoc A B C) (x , y , z) = (x , y) , z
section (×-assoc A B C) ((x , y) , z) = refl
retract (×-assoc A B C) (x , y , z) = refl

Σ-≅ : ∀{a b1 b2} {A : Set a} {B1 : A → Set b1} {B2 : A → Set b2} →
      ((x : A) → B1 x ≅ B2 x) →
      (Σ[ x ∈ A ] (B1 x)) ≅ (Σ[ x ∈ A ] (B2 x))
forward (Σ-≅ p) (x , y) = x , p x .forward y 
backward (Σ-≅ p) (x , y) = x , p x .backward y
section (Σ-≅ p) (x , y) = cong (x ,_) (p x .section y)
retract (Σ-≅ p) (x , y) = cong (x ,_) (p x .retract y)      