{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Nat
open import Function

open ≡-Reasoning

module Common.Equality where

ListPath : {A : Set} → List A → List A → Set
ListPath [] [] = ⊤
ListPath [] (y ∷ ys) = ⊥
ListPath (x ∷ xs) [] = ⊥
ListPath (x ∷ xs) (y ∷ ys) = x ≡ y × ListPath xs ys

evalListPath : {A : Set} {xs ys : List A} →
               ListPath xs ys → xs ≡ ys
evalListPath {xs = []} {[]} tt = refl
evalListPath {xs = x ∷ xs} {.x ∷ ys} (refl , p) =
  cong (x ∷_) $ evalListPath p

{-
"Equivalent below" equivalence relation between functions

f1 and f2 are equivalent below n if
f1 x ≡ f2 x for all x < n

We write it in a more explicit form so it's
easier to work with
-}
≗Below : {A : Set} → ℕ → (ℕ → A) → (ℕ → A) → Set
≗Below zero f1 f2 = ⊤
≗Below (suc n) f1 f2 =
  f1 zero ≡ f2 zero × ≗Below n (f1 ∘ suc) (f2 ∘ suc)

∘-≗Below : ∀{n} {A : Set} {B : Set}
            {f1 f2 : ℕ → A}
            (g : A → B) →
            ≗Below n f1 f2 →
            ≗Below n (g ∘ f1) (g ∘ f2)
∘-≗Below {n = zero} g f1≗f2 = tt
∘-≗Below {n = suc n} g (f1₀≡f2₀ , f1∘suc≗f2∘suc) =
  cong g f1₀≡f2₀ , ∘-≗Below g f1∘suc≗f2∘suc

_∈Image_ : ∀{a b} {A : Set a} {B : Set b}
           (y : B) (f : A → B) → Set (ℓ-max a b)
y ∈Image f = Σ[ x ∈ _ ] (f x ≡ y)

_∉Image_ : ∀{a b} {A : Set a} {B : Set b}
           (y : B) (f : A → B) → Set (ℓ-max a b)
y ∉Image f = ¬ (y ∈Image f)

nil≢cons : ∀{a} {A : Set a} {x : A} {xs : List A} → [] ≢ x ∷ xs
nil≢cons ()

cons≢nil : ∀{a} {A : Set a} {x : A} {xs : List A} → x ∷ xs ≢ []
cons≢nil ()

map-const : ∀{a b} {A : Set a} {B : Set b}
            (y : B) (xs : List A) →
            map (λ _ → y) xs ≡ replicate (length xs) y
map-const y [] = refl
map-const y (x ∷ xs) = cong (y ∷_) (map-const y xs)            

replicate-++ : ∀{a} {A : Set a}
              (m n : ℕ) (x : A) →
              replicate (m + n) x ≡ 
              replicate m x ++ replicate n x
replicate-++ zero n x = refl
replicate-++ (suc m) n x = cong (x ∷_) (replicate-++ m n x)            

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
Σ-≡-→-≡-Σ : ∀{a b} {A : Set a} {B : A → Set b}
            {x1 x2 : A} {y1 : B x1} {y2 : B x2} →
            (p : x1 ≡ x2) → subst B p y1 ≡ y2 → (x1 , y1) ≡ (x2 , y2)
Σ-≡-→-≡-Σ refl refl = refl

subst-const : ∀{a b} {A : Set a} {B : Set b}
              {x y : A} (p : x ≡ y) (b : B) →
              subst (λ x → B) p b ≡ b
subst-const refl b = refl

subst-cong : ∀{a b c} {A : Set a} {B : Set b}
              (C : B → Set c) (f : A → B)
              {x1 x2 : A} (p : x1 ≡ x2) (y : C (f x1)) →
              subst C (cong f p) y ≡ subst (C ∘ f) p y
subst-cong C f refl y = refl

subst-× : ∀{a b d} {D : Set d}
          (A : D → Set a) (B : D → Set b)
          {x y : D} (p : x ≡ y) (Ax : A x) (Bx : B x) →
          subst (λ x → A x × B x) p (Ax , Bx)
          ≡ (subst A p Ax , subst B p Bx)
subst-× A B refl Ax Bx = refl

subst-fst : ∀{a b d} {D : Set d}
            (A : D → Set a) (B : D → Set b)
            {x y : D} (p : x ≡ y) (ABx : A x × B x) →
            subst (λ x → A x × B x) p ABx .fst
            ≡ subst A p (ABx .fst)
subst-fst A B refl (Ax , Bx) = refl

subst-snd : ∀{a b d} {D : Set d}
            (A : D → Set a) (B : D → Set b)
            {x y : D} (p : x ≡ y) (ABx : A x × B x) →
            subst (λ x → A x × B x) p ABx .snd
            ≡ subst B p (ABx .snd)
subst-snd A B refl (Ax , Bx) = refl

subst-Σ-fst : ∀{a b d} {D : Set d}
              (A : D → Set a) (B : (d : D) → A d → Set b)
              {x y : D} (p : x ≡ y) (Ax : A x) (Bx : B x Ax) →
              subst (λ x → Σ[ y ∈ A x ] B x y) p (Ax , Bx) .fst
              ≡ subst A p Ax
subst-Σ-fst A B refl Ax Bx = refl

subst-Σ-snd : ∀{a b c} {A : Set a} {B : Set b}
              (C : A → B → Set c)
              {x1 x2 : A} (p : x1 ≡ x2) (s : Σ[ y ∈ B ] C x1 y) →
              subst (λ x → Σ[ y ∈ B ] C x y) p s .snd
              ≡ subst (C x2)
                  (sym (subst-Σ-fst (λ _ → B) C p (s .fst) (s .snd) ∙ subst-const p (s .fst)))
                  (subst (λ x → C x (s .fst)) p (s .snd))
subst-Σ-snd C refl (y , Cxy) = refl

subst-≡ : ∀{a b} {A : Set a} {B : Set b}
          (f g : A → B)
          {x y : A} (p : x ≡ y) (q : f x ≡ g x) →
          subst (λ x → f x ≡ g x) p q
          ≡ sym (cong f p) ∙ q ∙ cong g p
subst-≡ f g refl q = sym $ •-idᵣ q

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

-- Higher paths
PathP : ∀{a b} {A : Set a} (B : A → Set b)
        {x1 x2 : A} (p : x1 ≡ x2)
        (y1 : B x1) (y2 : B x2) → Set b
PathP B p y1 y2 = subst B p y1 ≡ y2        

congP : ∀{a b} {A : Set a} {B : A → Set b}
        (f : (x : A) → B x) {x1 x2 : A} (p : x1 ≡ x2) →
        PathP B p (f x1) (f x2)
congP f refl = refl

apP : ∀{a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
      {x1 x2 : A} {p : x1 ≡ x2}
      {f : B x1 → C x1} {g : B x2 → C x2}
      (q : PathP (λ x → B x → C x) p f g)
      (y : B x1) →
      PathP C p (f y) (g (subst B p y))
apP {p = refl} refl y = refl

congP′ : ∀{a b c} {A : Set a} (B : A → Set b) {C : Set c}
        (f : {x : A} → B x → C)
        {x1 x2 : A} (p : x1 ≡ x2)
        {y1 : B x1} {y2 : B x2} (q : PathP B p y1 y2) →
        f y1 ≡ f y2
congP′ B f refl refl = refl

Σ-PathP-→-≡-Σ : ∀{a b} {A : Set a} {B : A → Set b} {x1 x2 : A} {y1 : B x1} {y2 : B x2} →
                (p : x1 ≡ x2) → PathP B p y1 y2 → (x1 , y1) ≡ (x2 , y2)
Σ-PathP-→-≡-Σ refl refl = refl