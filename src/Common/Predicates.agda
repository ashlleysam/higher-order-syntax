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

module Common.Predicates where

AllElems : ∀{a} {A : Set a} →
           (A → Set) →
           List A → Set
AllElems P [] = ⊤
AllElems P (x ∷ xs) = P x × AllElems P xs

map-AllElems : ∀{a b} {A : Set a} {xs : List A} {B : Set b}
               (P : A → Set) (Q : B → Set) (f : A → B) →
               ((x : A) → P x → Q (f x)) →
               AllElems P xs →
               AllElems Q (map f xs)
map-AllElems {xs = []} P Q f P⇒Q∘f tt = tt
map-AllElems {xs = x ∷ xs} P Q f P⇒Q∘f (Px , Pxs) =
  P⇒Q∘f x Px ,
  map-AllElems P Q f P⇒Q∘f Pxs

map-AllElems⁻ : ∀{a b} {A : Set a} {xs : List A} {B : Set b}
               (P : A → Set) (Q : B → Set) (f : A → B) →
               ((x : A) → Q (f x) → P x) →
               AllElems Q (map f xs) →
               AllElems P xs
map-AllElems⁻ {xs = []} P Q f Q∘f⇒P tt = tt
map-AllElems⁻ {xs = x ∷ xs} P Q f Q∘f⇒P (Qfx , Qfxs) =
  Q∘f⇒P x Qfx ,
  map-AllElems⁻ P Q f Q∘f⇒P Qfxs
