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

open import Common.Isomorphism

module Common.Relations where

-- Isomorphisms between relations (a stronger condition than logical equivalence)
infix 4 _≅ᵣ_
_≅ᵣ_ : ∀{a b ℓ1 ℓ2} {A : Set a} {B : Set b} →
        REL A B ℓ1 → REL A B ℓ2 → Set (a ⊔ b ⊔ ℓ1 ⊔ ℓ2)
R ≅ᵣ S = ∀ x y → R x y ≅ S x y

{-
Extend a relation to related lists of matching length
Generalization of the Kleene star to a set of pairs
-}
⋆ : ∀{a b ℓ} {A : Set a} {B : Set b} →
    REL A B ℓ →
    REL (List A) (List B) ℓ
⋆ {ℓ = ℓ} R [] [] = Lift ℓ ⊤
⋆ {ℓ = ℓ} R [] (x ∷ ys) = Lift ℓ ⊥
⋆ {ℓ = ℓ} R (x ∷ xs) [] = Lift ℓ ⊥
⋆ R (x ∷ xs) (y ∷ ys) = R x y × ⋆ R xs ys

-- The relation on lists respects mapping
⋆-map-⇒ : ∀{a b ℓ} {A : Set a} {B : Set b} →
          {R : REL A B ℓ} (f : A → B) (xs : List A) →
          (∀ x → R x (f x)) →
          ⋆ R xs (map f xs)
⋆-map-⇒ f [] p = lift tt
⋆-map-⇒ f (x ∷ xs) p = p x , ⋆-map-⇒ f xs p

⋆-map-⇐ : ∀{a b ℓ} {A : Set a} {B : Set b} →
          {R : REL A B ℓ} (f : B → A) (xs : List B) →
          (∀ y → R (f y) y) →
          ⋆ R (map f xs) xs
⋆-map-⇐ f [] p = lift tt
⋆-map-⇐ f (y ∷ ys) p = p y , ⋆-map-⇐ f ys p

-- The relation on lists preserves reflexivity
⋆-pres-refl : ∀{a ℓ} {A : Set a} {R : Rel A ℓ} →
              Reflexive R → Reflexive (⋆ R)
⋆-pres-refl R-refl {x = []} = lift tt
⋆-pres-refl R-refl {x = x ∷ xs} = R-refl , ⋆-pres-refl R-refl

-- The relation on lists preserves implications
⋆-pres-⇒ : ∀{a b ℓ1 ℓ2} {A : Set a} {B : Set b}
            {R : REL A B ℓ1} {S : REL A B ℓ2} →
            R ⇒ S → ⋆ R ⇒ ⋆ S
⋆-pres-⇒ R⇒S {x = []} {y = []} (lift tt) = lift tt
⋆-pres-⇒ R⇒S {x = x ∷ xs} {y = y ∷ ys} (xRy , xsR*ys) =
  R⇒S xRy , ⋆-pres-⇒ R⇒S xsR*ys

-- The above function respects extensional equality
⋆-pres-⇒-ext : ∀{a b ℓ1 ℓ2} {A : Set a} {B : Set b}
                {R : REL A B ℓ1} {S : REL A B ℓ2} →
                {f g : R ⇒ S} → 
                (∀{x y} (r : R x y) → f r ≡ g r) → 
                ∀{xs ys} (r : ⋆ R xs ys) →
                ⋆-pres-⇒ f r ≡ ⋆-pres-⇒ g r
⋆-pres-⇒-ext p {[]} {[]} (lift tt) = refl
⋆-pres-⇒-ext p {x ∷ xs} {y ∷ ys} (xRy , xsR*ys) =
  cong₂ _,_
    (p xRy)
    (⋆-pres-⇒-ext p xsR*ys)

-- The above function respects the identity
⋆-pres-⇒-id : ∀{a b ℓ1} {A : Set a} {B : Set b}
              {R : REL A B ℓ1}
              {xs : List A} {ys : List B}
              (xs-⋆R-ys : ⋆ R xs ys) →
              ⋆-pres-⇒ id xs-⋆R-ys ≡ xs-⋆R-ys
⋆-pres-⇒-id {xs = []} {[]} (lift tt) = refl
⋆-pres-⇒-id {xs = x ∷ xs} {y ∷ ys} (x-R-y , xs-⋆R-ys) =
  cong₂ _,_
    refl
    (⋆-pres-⇒-id xs-⋆R-ys)

-- The above function respects composition
⋆-pres-⇒-∘ : ∀{a b ℓ1 ℓ2 ℓ3} {A : Set a} {B : Set b}
              {R : REL A B ℓ1}
              {S : REL A B ℓ2}
              {T : REL A B ℓ3}
              (f : S ⇒ T) (g : R ⇒ S)
              {xs : List A} {ys : List B}
              (xs-⋆R-ys : ⋆ R xs ys) →
              ⋆-pres-⇒ f (⋆-pres-⇒ g xs-⋆R-ys) ≡
              ⋆-pres-⇒ (f ∘ g) xs-⋆R-ys
⋆-pres-⇒-∘ f g {[]} {[]} (lift tt) = refl
⋆-pres-⇒-∘ f g {x ∷ xs} {y ∷ ys} (x-R-y , xs-⋆R-ys) =
  cong₂ _,_
    refl
    (⋆-pres-⇒-∘ f g xs-⋆R-ys)

-- Combine two relations into a relation on a pairs
infixr 5 _×ᵣ_
_×ᵣ_ : ∀{a1 a2 b1 b2 ℓ1 ℓ2}
        {A1 : Set a1} {A2 : Set a2}
        {B1 : Set b1} {B2 : Set b2} →
        REL A1 A2 ℓ1 →
        REL B1 B2 ℓ2 →
        REL (A1 × B1) (A2 × B2) (ℓ1 ⊔ ℓ2)
(R ×ᵣ S) (x1 , y1) (x2 , y2) = R x1 x2 × S y1 y2        

-- The relation on pairs preserves reflexivity
×ᵣ-pres-refl : ∀{a b ℓ1 ℓ2} {A : Set a} {B : Set b}
              {R : Rel A ℓ1} {S : Rel B ℓ2} →
              Reflexive R → Reflexive S →
              Reflexive (R ×ᵣ S)
×ᵣ-pres-refl R-refl S-refl {x = x , y} = R-refl , S-refl

-- The relation on pairs preserves implications
×ᵣ-pres-⇒ : ∀{a1 a2 b1 b2 ℓ1 ℓ2 ℓ3 ℓ4}
            {A1 : Set a1} {A2 : Set a2}
            {B1 : Set b1} {B2 : Set b2} →
            {R1 : REL A1 A2 ℓ1} {R2 : REL A1 A2 ℓ2} →
            {S1 : REL B1 B2 ℓ3} {S2 : REL B1 B2 ℓ4} →
            R1 ⇒ R2 →
            S1 ⇒ S2 →
            (R1 ×ᵣ S1) ⇒ (R2 ×ᵣ S2)
×ᵣ-pres-⇒ R1⇒R2 S1⇒S2 (R1x1x2 , S1y1y2) = R1⇒R2 R1x1x2 , S1⇒S2 S1y1y2

-- The composed relation (R ∘ᵣ S) relates x with z if there
-- is some y which R relates with z and S relates with x
_∘ᵣ_ : ∀{a b c ℓ1 ℓ2} {A : Set a} {B : Set b} {C : Set c} →
        REL B C ℓ2 → REL A B ℓ1 → REL A C (b ⊔ ℓ1 ⊔ ℓ2)
(R ∘ᵣ S) x z = Σ[ y ∈ _ ] (R y z × S x y)

-- Composing and taking a product of relations is
-- isomorphic to taking a product and then composing
module _
  {a1 a2 b1 b2 c1 c2 ℓ1 ℓ2 ℓ3 ℓ4}
  {A1 : Set a1} {A2 : Set a2}
  {B1 : Set b1} {B2 : Set b2}
  {C1 : Set c1} {C2 : Set c2}
  (R1 : REL B1 C1 ℓ1) (S1 : REL A1 B1 ℓ2)
  (R2 : REL B2 C2 ℓ3) (S2 : REL A2 B2 ℓ4)
  where
  ×ᵣ-∘ᵣ-⇒ : (R1 ∘ᵣ S1) ×ᵣ (R2 ∘ᵣ S2) ⇒
            (R1 ×ᵣ R2) ∘ᵣ (S1 ×ᵣ S2)
  ×ᵣ-∘ᵣ-⇒ {x = x1 , x2} {y = z1 , z2} ((y1 , y1-R1-z1 , x1-S1-y1) , (y2 , y2-R2-z2 , x2-S2-y2)) =
    (y1 , y2) , (y1-R1-z1 , y2-R2-z2) , x1-S1-y1 , x2-S2-y2

  ∘ᵣ-×ᵣ-⇒ : (R1 ×ᵣ R2) ∘ᵣ (S1 ×ᵣ S2) ⇒
            (R1 ∘ᵣ S1) ×ᵣ (R2 ∘ᵣ S2)
  ∘ᵣ-×ᵣ-⇒ {x = x1 , x2} {y = z1 , z2} ((y1 , y2) , (y1-R1-z1 , y2-R2-z2) , x1-S1-y1 , x2-S2-y2) =
    (y1 , y1-R1-z1 , x1-S1-y1) , (y2 , y2-R2-z2 , x2-S2-y2)

  ×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ : (R1 ∘ᵣ S1) ×ᵣ (R2 ∘ᵣ S2) ≅ᵣ
                   (R1 ×ᵣ R2) ∘ᵣ (S1 ×ᵣ S2)
  forward (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (x1 , x2) (z1 , z2)) = ×ᵣ-∘ᵣ-⇒
  backward (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (x1 , x2) (z1 , z2)) = ∘ᵣ-×ᵣ-⇒
  section (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (x1 , x2) (z1 , z2)) ((y1 , y1-R1-z1 , x1-S1-y1) , (y2 , y2-R2-z2 , x2-S2-y2)) = refl
  retract (×ᵣ-∘ᵣ-≅ᵣ-∘ᵣ-×ᵣ (x1 , x2) (z1 , z2)) ((y1 , y2) , (y1-R1-z1 , y2-R2-z2) , x1-S1-y1 , x2-S2-y2) = refl

-- ⋆ distributes over composition of relations
module _
  {a b c ℓ1 ℓ2} {A : Set a} {B : Set b} {C : Set c}
  (R : REL B C ℓ1) (S : REL A B ℓ2)
  where
  ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ : ⋆ R ∘ᵣ ⋆ S ≅ᵣ ⋆ (R ∘ᵣ S)
  forward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] []) ([] , lift tt , lift tt) = lift tt
  backward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] []) (lift tt) = [] , lift tt , lift tt
  section (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] []) ([] , lift tt , lift tt) = refl
  retract (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] []) (lift tt) = refl
  forward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) ([] , () , _)
  forward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) (y ∷ ys , _ , ())
  backward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) ()
  section (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) ([] , () , _)
  section (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) (y ∷ ys , _ , ())
  retract (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ [] (z ∷ zs)) ()
  forward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) ([] , _ , ())
  forward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) (y ∷ ys , () , _)
  backward (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) ()
  section (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) ([] , _ , ())
  section (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) (y ∷ ys , () , _)
  retract (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) []) ()
  ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ (x ∷ xs) (z ∷ zs) =
    (Σ[ ys ∈ List B ] (⋆ R ys (z ∷ zs) × ⋆ S (x ∷ xs) ys))
      ≅⟨ Σ-List-≅ B (λ ys → ⋆ R ys (z ∷ zs) × ⋆ S (x ∷ xs) ys) ⟩
    ((Lift ℓ1 ⊥ × Lift ℓ2 ⊥) ⊎ (Σ[ y ∈ B ] Σ[ ys ∈ List B ] (⋆ R (y ∷ ys) (z ∷ zs) × ⋆ S (x ∷ xs) (y ∷ ys))))
      ≅⟨ ⊎-≅ (⊥-×-≅ (λ{ (lift ()) }) (Lift ℓ2 ⊥)) ≅-refl ⟩
    (⊥ ⊎ (Σ[ y ∈ B ] Σ[ ys ∈ List B ] (⋆ R (y ∷ ys) (z ∷ zs) × ⋆ S (x ∷ xs) (y ∷ ys))))
      ≅⟨ ⊥-⊎-≅ id _ ⟩
    (Σ[ y ∈ B ] Σ[ ys ∈ List B ] ((R y z × ⋆ R ys zs) × (S x y × ⋆ S xs ys)))
      ≅⟨ Σ-≅ (λ y → Σ-≅ λ ys → 
        ((R y z × ⋆ R ys zs) × S x y × ⋆ S xs ys)
          ≅⟨ ×-assoc (R y z) (⋆ R ys zs) (S x y × ⋆ S xs ys) ⟩
        (R y z × ⋆ R ys zs × S x y × ⋆ S xs ys)
          ≅⟨ ×-≅ ≅-refl (≅-sym (×-assoc (⋆ R ys zs) (S x y) (⋆ S xs ys))) ⟩
        (R y z × (⋆ R ys zs × S x y) × ⋆ S xs ys)
          ≅⟨ ×-≅ ≅-refl (×-≅ (×-comm (⋆ R ys zs) (S x y)) ≅-refl) ⟩
        (R y z × (S x y × ⋆ R ys zs) × ⋆ S xs ys)
          ≅⟨ ×-≅ ≅-refl (×-assoc (S x y) (⋆ R ys zs) (⋆ S xs ys)) ⟩
        (R y z × S x y × ⋆ R ys zs × ⋆ S xs ys)
          ≅⟨ ≅-sym (×-assoc (R y z) (S x y) (⋆ R ys zs × ⋆ S xs ys)) ⟩
        ((R y z × S x y) × ⋆ R ys zs × ⋆ S xs ys) ≅∎) ⟩
    (Σ[ y ∈ B ] Σ[ ys ∈ List B ] ((R y z × S x y) × (⋆ R ys zs × ⋆ S xs ys)))
      ≅⟨ ≅-sym (Σ-×-Σ-≅ B (λ y → R y z × S x y) (List B) (λ ys → ⋆ R ys zs × ⋆ S xs ys)) ⟩
    ((Σ[ y ∈ B ] (R y z × S x y)) × (Σ[ ys ∈ List B ] (⋆ R ys zs × ⋆ S xs ys)))
      ≅⟨ ×-≅ ≅-refl (∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ xs zs) ⟩
    ((Σ[ y ∈ B ] (R y z × S x y)) × ⋆ (R ∘ᵣ S) xs zs) ≅∎

  ∘ᵣ-⋆-⇒ : ⋆ R ∘ᵣ ⋆ S ⇒ ⋆ (R ∘ᵣ S)
  ∘ᵣ-⋆-⇒ {xs} {zs} = ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ xs zs .forward

  ⋆-∘ᵣ-⇒ : ⋆ (R ∘ᵣ S) ⇒ ⋆ R ∘ᵣ ⋆ S 
  ⋆-∘ᵣ-⇒ {xs} {zs} = ∘ᵣ-⋆-≅ᵣ-⋆-∘ᵣ xs zs .backward