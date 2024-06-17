{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (_<*>_)
open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Maybe renaming (map to mmap)
open import Data.Maybe.Properties
open import Function

open ≡-Reasoning

open import Common.Equality

module Common.MaybeOrder where

_∈Dom_ : ∀{a b} {A : Set a} {B : Set b} →
         A → (A → Maybe B) → Set b
x ∈Dom f = Σ[ y ∈ _ ] (f x ≡ just y)         

∈Dom-isProp : ∀{a b} {A : Set a} {B : Set b}
              (x : A) (f : A → Maybe B) →
              isProp (x ∈Dom f)
∈Dom-isProp x f (y1 , p) (y2 , q) =
  Σ-≡-→-≡-Σ
    (just-injective (sym p ∙ q))
    (UIP _ _)              

pure : ∀{a} {A : Set a} → A → Maybe A
pure = just

infixl 2 _<=<_
_<=<_ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → Maybe C) →
        (A → Maybe B) →
        A → Maybe C
(f <=< g) x = g x >>= f

infixl 2 _<*>_
_<*>_ : ∀{a b} {A : Set a} {B : Set b} →
        Maybe (A → B) →
        Maybe A →
        Maybe B
nothing <*> m = nothing
just f <*> nothing = nothing
just f <*> just x = just (f x)        

infixr 9 _<∘>_
_<∘>_ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) →
        (A → Maybe B) →
        A → Maybe C
(f <∘> g) x = mmap f (g x)        

infixr 9 _<*<_
_<*<_ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} →
        Maybe (B → C) →
        Maybe (A → B) →
        Maybe (A → C)
just f <*< just g = just (f ∘ g)
just f <*< nothing = nothing
nothing <*< just g = nothing
nothing <*< nothing = nothing        

map-<*> : ∀{a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : B → C)
          (g : Maybe (A → B))
          (x : Maybe A) →
          mmap f (g <*> x) ≡ ((just f <*< g) <*> x)
map-<*> f (just g) (just x) = refl
map-<*> f (just g) nothing = refl
map-<*> f nothing (just x) = refl
map-<*> f nothing nothing = refl          

module _ {a} {A : Set a} where
  -- More-defined-than or equal-to relation
  infix 4 _≼_
  _≼_ : (x y : Maybe A) → Set a
  just x  ≼ just y  = x ≡ y
  nothing ≼ just y  = Lift _ ⊥ 
  nothing ≼ nothing = Lift _ ⊤
  just x  ≼ nothing = Lift _ ⊤

  ≼-isProp : ∀{x y} → isProp (x ≼ y)
  ≼-isProp {just x}  {just x}  refl      refl      = refl
  ≼-isProp {just x}  {nothing} (lift tt) (lift tt) = refl
  ≼-isProp {nothing} {nothing} (lift tt) (lift tt) = refl

  ≼-refl : ∀{x} → x ≼ x
  ≼-refl {just x}  = refl 
  ≼-refl {nothing} = lift tt

  ≼-trans : ∀{x y z} → x ≼ y → y ≼ z → x ≼ z
  ≼-trans {just x}  {just .x} {just .x} refl      refl      = refl
  ≼-trans {just x}  {just .x} {nothing} refl      (lift tt) = lift tt
  ≼-trans {just x}  {nothing} {nothing} (lift tt) (lift tt) = lift tt
  ≼-trans {nothing} {nothing} {nothing} (lift tt) (lift tt) = lift tt

  ≼-antisym : ∀{x y} → x ≼ y → y ≼ x → x ≡ y
  ≼-antisym {just x} {just .x} refl refl = refl
  ≼-antisym {nothing} {nothing} (lift tt) (lift tt) = refl

  infix  3 _∎≼
  infixr 2 _≼⟨⟩_ step-≼ step-≼≡

  _≼⟨⟩_ : ∀ (x {y} : Maybe A) → x ≼ y → x ≼ y
  _ ≼⟨⟩ x≼y = x≼y

  step-≼ : ∀ (x {y z} : Maybe A) → y ≼ z → x ≼ y → x ≼ z
  step-≼ _ y≼z x≼y = ≼-trans x≼y y≼z

  step-≼≡ : ∀ (x {y z} : Maybe A) → y ≼ z → x ≡ y → x ≼ z
  step-≼≡ _ y≼z refl = y≼z

  _∎≼ : ∀ (x : Maybe A) → x ≼ x
  _∎≼ _ = ≼-refl

  syntax step-≼  x y≼z x≼y = x ≼⟨  x≼y ⟩ y≼z
  syntax step-≼≡  x y≼z x≡y = x ≼≡⟨  x≡y ⟩ y≼z

module _ {a b} {A : Set a} {B : Set b} where
  -- Everywhere more-defined-than or equal-to relation
  infix 4 _≾_
  _≾_ : (f g : A → Maybe B) → Set (ℓ-max a b)
  f ≾ g = ∀ x → f x ≼ g x

  ≾-refl : ∀{f} → f ≾ f
  ≾-refl x = ≼-refl

  ≾-trans : ∀{f g h} → f ≾ g → g ≾ h → f ≾ h
  ≾-trans p q x = ≼-trans (p x) (q x) 

  ≾-antisym : ∀{f g} → f ≾ g → g ≾ f → f ≗ g
  ≾-antisym p q x = ≼-antisym (p x) (q x)

  ≼-<*> : {f1 f2 : Maybe (A → B)} {x1 x2 : Maybe A} →
          f1 ≼ f2 → x1 ≼ x2 → (f1 <*> x1) ≼ (f2 <*> x2)
  ≼-<*> {just f}  {just .f} {just x}  {just .x} refl      refl      = refl
  ≼-<*> {just f}  {just .f} {just x}  {nothing} refl      (lift tt) = lift tt
  ≼-<*> {just f}  {just .f} {nothing} {nothing} refl      (lift tt) = lift tt
  ≼-<*> {just f}  {nothing} {just x}  {just .x} (lift tt) refl      = lift tt
  ≼-<*> {just f}  {nothing} {just x}  {nothing} (lift tt) (lift tt) = lift tt
  ≼-<*> {just f}  {nothing} {nothing} {nothing} (lift tt) (lift tt) = lift tt
  ≼-<*> {nothing} {nothing} {just x}  {just .x} (lift tt) refl      = lift tt
  ≼-<*> {nothing} {nothing} {just x}  {nothing} (lift tt) (lift tt) = lift tt
  ≼-<*> {nothing} {nothing} {nothing} {nothing} (lift tt) (lift tt) = lift tt

  map≼map : ∀{x1 x2} (f : A → B) → x1 ≼ x2 → mmap f x1 ≼ mmap f x2
  map≼map {just x} {just .x}  f refl      = refl
  map≼map {just x} {nothing}  f (lift tt) = lift tt
  map≼map {nothing} {nothing} f (lift tt) = lift tt
