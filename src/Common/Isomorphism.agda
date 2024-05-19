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

open import Common.Equality

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

-- Equality implies isomorphism
≡-⇒-≅ : ∀{a} {A B : Set a} → A ≡ B → A ≅ B
forward (≡-⇒-≅ p) = transport p
backward (≡-⇒-≅ p) = transport (sym p)
section (≡-⇒-≅ p) x = transport-∘ p (sym p) x ∙ cong (λ q → transport q x) (trans-symʳ p)
retract (≡-⇒-≅ p) y = transport-∘ (sym p) p y ∙ cong (λ q → transport q y) (trans-symˡ p)

-- Equality types are isomorphic under mapping each side with an injective function
inj-≅ : ∀{a b} {A : Set a} {B : Set b} {f : A → B} →
        Injective _≡_ _≡_ f →
        ∀ x y → (f x ≡ f y) ≅ (x ≡ y)
forward (inj-≅ f-inj x y) fx≡fy = f-inj fx≡fy
backward (inj-≅ {f = f} f-inj x y) x≡y = cong f x≡y
section (inj-≅ {f = f} f-inj x y) fx≡fy = UIP (cong f (f-inj fx≡fy)) fx≡fy
retract (inj-≅ {f = f} f-inj x y) x≡y = UIP (f-inj (cong f x≡y)) x≡y

-- Equality types are isomorphic under swapping the arguments
swap-≡ : ∀{a} {A : Set a} {x y : A} → (x ≡ y) ≅ (y ≡ x)
forward swap-≡ p = sym p
backward swap-≡ p = sym p
section swap-≡ refl = refl
retract swap-≡ refl = refl

-- Taking products respects isomorphisms
×-≅ : ∀{a1 a2 b1 b2} {A1 : Set a1} {A2 : Set a2}
      {B1 : Set b1} {B2 : Set b2} →
      A1 ≅ A2 → B1 ≅ B2 → (A1 × B1) ≅ (A2 × B2)
forward (×-≅ p q) (x1 , y1) = p .forward x1 , q .forward y1
backward (×-≅ p q) (x2 , y2) = p .backward x2 , q .backward y2
section (×-≅ p q) (x1 , y1) = cong₂ _,_ (p .section x1) (q .section y1)
retract (×-≅ p q) (x2 , y2) = cong₂ _,_ (p .retract x2) (q .retract y2)

-- Taking sums respects isomorphisms
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

-- Nested sigma types with disjoint predicates can be separated
Σ-×-Σ-≅ : ∀{a b ℓ1 ℓ2} (A : Set a) (P : A → Set ℓ1)
          (B : Set b) (Q : B → Set ℓ2) →
          ((Σ[ x ∈ A ] (P x)) × (Σ[ y ∈ B ] (Q y))) ≅ 
          (Σ[ x ∈ A ] Σ[ y ∈ B ] (P x × Q y))
forward (Σ-×-Σ-≅ A P B Q) ((x , Px) , (y , Qy)) = x , y , Px , Qy
backward (Σ-×-Σ-≅ A P B Q) (x , y , Px , Qy) = (x , Px) , (y , Qy)
section (Σ-×-Σ-≅ A P B Q) ((x , Px) , (y , Qy)) = refl
retract (Σ-×-Σ-≅ A P B Q) (x , y , Px , Qy) = refl

{-
A sigma type where the predicate has an equaity constraint
with a constant can eliminate the equality constraint by
substituting the constant in the rest of the predicate
-}
Σ-≡-×-≅ : ∀{a ℓ} {A : Set a} (y : A) (P : A → Set ℓ) →
          (Σ[ x ∈ A ] (x ≡ y × P x)) ≅ P y
forward (Σ-≡-×-≅ y P) (z , z≡y , Pz) = subst P z≡y Pz
backward (Σ-≡-×-≅ y P) Py = y , refl , Py
section (Σ-≡-×-≅ y P) (.y , refl , Pz) = Σ-≡-→-≡-Σ refl refl
retract (Σ-≡-×-≅ y P) Py = refl

-- A proof that some list satisfies a property is
-- isomorphic to either the empty list satisfying it,
-- or some non-empty list satisfying it
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

-- Empty types are annihilators for products
⊥-×-≅ : ∀{a b} {A : Set a} → (A → ⊥) → (B : Set b) → (A × B) ≅ ⊥
forward (⊥-×-≅ ¬A B) (x , y) = ⊥-elim (¬A x)
backward (⊥-×-≅ ¬A B) ()
section (⊥-×-≅ ¬A B) (x , y) = ⊥-elim (¬A x)
retract (⊥-×-≅ ¬A B) ()

-- Empty types are identities for sums
⊥-⊎-≅ : ∀{a b} {A : Set a} → (A → ⊥) → (B : Set b) → (A ⊎ B) ≅ B
forward (⊥-⊎-≅ ¬A B) (inl x) = ⊥-elim (¬A x)
forward (⊥-⊎-≅ ¬A B) (inr y) = y
backward (⊥-⊎-≅ ¬A B) y = inr y
section (⊥-⊎-≅ ¬A B) (inl x) = ⊥-elim (¬A x)
section (⊥-⊎-≅ ¬A B) (inr y) = refl
retract (⊥-⊎-≅ ¬A B) y = refl

-- Taking products is commutitive
×-comm : ∀{a b} (A : Set a) (B : Set b) →
         (A × B) ≅ (B × A)
forward (×-comm A B) (x , y) = y , x 
backward (×-comm A B) (y , x) = x , y
section (×-comm A B) (x , y) = refl
retract (×-comm A B) (y , x) = refl

-- Taking products is associative
×-assoc : ∀{a b c} (A : Set a) (B : Set b) (C : Set c) →
          ((A × B) × C) ≅ (A × B × C)
forward (×-assoc A B C) ((x , y) , z) = x , y , z 
backward (×-assoc A B C) (x , y , z) = (x , y) , z
section (×-assoc A B C) ((x , y) , z) = refl
retract (×-assoc A B C) (x , y , z) = refl

-- Isomorphic extensionality for sigma types
Σ-≅ : ∀{a b1 b2} {A : Set a} {B1 : A → Set b1} {B2 : A → Set b2} →
      ((x : A) → B1 x ≅ B2 x) →
      (Σ[ x ∈ A ] (B1 x)) ≅ (Σ[ x ∈ A ] (B2 x))
forward (Σ-≅ p) (x , y) = x , p x .forward y     
backward (Σ-≅ p) (x , y) = x , p x .backward y
section (Σ-≅ p) (x , y) = cong (x ,_) (p x .section y)
retract (Σ-≅ p) (x , y) = cong (x ,_) (p x .retract y)

-- Prove an isomorphism with a sigma type whose predicate is a proposition
Σ-Prop-≅ : ∀{a b ℓ} {A : Set a} {B : Set b}
            {P : A → Set ℓ} →
            (∀ x → isProp (P x)) →
            (f : (x : A) → P x → B)
            (g : B → A) →
            (∀ x Px → g (f x Px) ≡ x) →
            (Pg : ∀ y → P (g y)) →
            (∀ y → f (g y) (Pg y) ≡ y) →
            (Σ[ x ∈ A ] (P x)) ≅ B
forward (Σ-Prop-≅ P-isProp f g r Pg s) (x , Px) = f x Px 
backward (Σ-Prop-≅ P-isProp f g r Pg s) y = g y , Pg y
section (Σ-Prop-≅ P-isProp f g r Pg s) (x , Px) = Σ-≡-→-≡-Σ (r x Px) (P-isProp x _ _)
retract (Σ-Prop-≅ P-isProp f g r Pg s) y = s y            