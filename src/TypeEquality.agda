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

module TypeEquality
  (⅀ : KindSignature)
  (≡-dec-TySymb : DecidableEquality (⅀ .TySymb))
  where

≡-dec-Ty : DecidableEquality (Ty ⅀)
≡-dec-TyVec : DecidableEquality (TyVec ⅀)

≡-dec-Ty (tyVar x1) (tyVar x2) with x1 ≟ x2
... | yes p = yes $ cong tyVar p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-Ty (tyVar x1) (tyConstr s2 ts2) = no λ ()
≡-dec-Ty (tyConstr s1 ts1) (tyVar x2) = no λ ()
≡-dec-Ty (tyConstr s1 ts1) (tyConstr s2 ts2)
  with ≡-dec-TySymb s1 s2 | ≡-dec-TyVec ts1 ts2
... | yes p | yes q = yes $ cong₂ tyConstr p q
... | yes p | no ¬q = no λ{ refl → ¬q refl }
... | no ¬p | _     = no λ{ refl → ¬p refl }

≡-dec-TyVec [] [] = yes refl
≡-dec-TyVec [] ((t2 , k2) ∷ ts2) = no λ ()
≡-dec-TyVec ((t1 , k1) ∷ ts1) [] = no λ ()
≡-dec-TyVec ((t1 , k1) ∷ ts1) ((t2 , k2) ∷ ts2)
  with ≡-dec-Ty t1 t2 | k1 ≟ k2 | ≡-dec-TyVec ts1 ts2
... | yes p | yes q | yes r = yes $ cong₃ (λ x y z → (x , y) ∷ z) p q r
... | yes p | yes q | no ¬r = no λ{ refl → ¬r refl }
... | yes p | no ¬q | _     = no λ{ refl → ¬q refl }
... | no ¬p | _     | _     = no λ{ refl → ¬p refl }