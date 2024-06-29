{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import KindSignatures
open import Types
open import TypeSignatures
open import Terms

module TermEquality
  (⅀ : TypeSignature)
  (≡-dec-TySymb : DecidableEquality (⅀ .⅀ₖ .TySymb))
  (≡-dec-TmSymb : DecidableEquality (⅀ .TmSymb))
  where

open import TypeEquality (⅀ .⅀ₖ) ≡-dec-TySymb

≡-dec-Tm : DecidableEquality (Tm ⅀)
≡-dec-TmVec : DecidableEquality (TmVec ⅀)

≡-dec-Tm (var x1) (var x2) with x1 ≟ x2
... | yes p = yes $ cong var p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-Tm (var x1) (constr s2 ts2 es2) = no λ ()
≡-dec-Tm (constr s1 ts1 es1) (var x2) = no λ ()
≡-dec-Tm (constr s1 ts1 es1) (constr s2 ts2 es2)
  with ≡-dec-TmSymb s1 s2 | ≡-dec-TyVec ts1 ts2 | ≡-dec-TmVec es1 es2
... | yes p | yes q | yes r = yes (cong₃ constr p q r)
... | yes p | yes q | no ¬r = no λ{ refl → ¬r refl }
... | yes p | no ¬q | _     = no λ{ refl → ¬q refl }
... | no ¬p | _     | _     = no λ{ refl → ¬p refl }

≡-dec-TmVec [] [] = yes refl
≡-dec-TmVec [] ((e2 , m2 , n2) ∷ es2) = no (λ ())
≡-dec-TmVec ((e1 , m1 , n1) ∷ es1) [] = no (λ ())
≡-dec-TmVec ((e1 , m1 , n1) ∷ es1) ((e2 , m2 , n2) ∷ es2)
  with ≡-dec-Tm e1 e2 | m1 ≟ m2 | n1 ≟ n2 | ≡-dec-TmVec es1 es2
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | yes p | yes q | yes r | no ¬s = no λ{ refl → ¬s refl }
... | yes p | yes q | no ¬r | _     = no λ{ refl → ¬r refl }
... | yes p | no ¬q | _     | _     = no λ{ refl → ¬q refl }
... | no ¬p | _     | _     | _     = no λ{ refl → ¬p refl }
