{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures

-- Untyped and possibly ill-scoped representations of terms
module SecondOrderLanguageUntyped (⅀ : SecondOrderSignature) where

open SecondOrderSignature ⅀
open import SecondOrderLanguage ⅀

-------------------
-- UNTYPED TERMS --
-------------------

data UTm : Set
data UTmVec : Set

-- Untyped terms
data UTm where
  var : ℕ → UTm
  constr : (s : ⅀ .TyShape) (es : UTmVec) → UTm

-- Untyped lists of terms
data UTmVec where
  [] : UTmVec
  _∷_ : (ek : UTm × ℕ) →
        (es : UTmVec) →
        UTmVec

eraseCons : UTm → ℕ → UTmVec → UTmVec
eraseCons e k es = (e , k) ∷ es

----------------------
-- BASIC PROPERTIES --
----------------------

-- Injectivity of constructors
unVar-inj : ∀{x y} → _≡_ {A = UTm} (var x) (var y) → x ≡ y
unVar-inj refl = refl

unConstr-inj : ∀{s1 s2 es1 es2} →
              _≡_ {A = UTm} (constr s1 es1) (constr s2 es2) →
              s1 ≡ s2 × es1 ≡ es2
unConstr-inj refl = refl , refl

unCons-inj : ∀{e1 e2 k1 k2 es1 es2} →
              _≡_ {A = UTmVec} ((e1 , k1) ∷ es1) ((e2 , k2) ∷ es2) →
              e1 ≡ e2 × k1 ≡ k2 × es1 ≡ es2
unCons-inj refl = refl , refl , refl

--------------
-- RENAMING --
--------------

{-
Because we do not have type annotations, but we
need to be able to represent the identity renaming
without knowing the current context, we make it
an explicit constructor of the data type.
-}
data URen : Set where
  UIdRen : URen
  UKeep : URen → URen
  UDrop : URen → URen

{-
Equivalence relation on renamings
By adding a constructor for the identity renaming,
we have lost uniqueness of representation because
Keep Id ≗ Id. Therefore we quotient by
this equivalence to regain uniqueness.
-}
infix 4 _≈ᵣ_
data _≈ᵣ_ : URen → URen → Set where
  IdRen≈ᵣ : UIdRen ≈ᵣ UIdRen
  UKeep≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → UKeep ξ1 ≈ᵣ UKeep ξ2
  UDrop≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → UDrop ξ1 ≈ᵣ UDrop ξ2
  Keep-Id≈ᵣId : ∀{ξ} → ξ ≈ᵣ UIdRen → UKeep ξ ≈ᵣ UIdRen
  Id≈ᵣKeep-Id : ∀{ξ} → UIdRen ≈ᵣ ξ → UIdRen ≈ᵣ UKeep ξ

≈ᵣ-isProp : ∀{ξ1 ξ2} (p q : ξ1 ≈ᵣ ξ2) → p ≡ q
≈ᵣ-isProp IdRen≈ᵣ IdRen≈ᵣ = refl
≈ᵣ-isProp (UKeep≈ᵣ p) (UKeep≈ᵣ q) = cong UKeep≈ᵣ (≈ᵣ-isProp p q)
≈ᵣ-isProp (UDrop≈ᵣ p) (UDrop≈ᵣ q) = cong UDrop≈ᵣ (≈ᵣ-isProp p q)
≈ᵣ-isProp (Keep-Id≈ᵣId p) (Keep-Id≈ᵣId q) = cong Keep-Id≈ᵣId (≈ᵣ-isProp p q)
≈ᵣ-isProp (Id≈ᵣKeep-Id p) (Id≈ᵣKeep-Id q) = cong Id≈ᵣKeep-Id (≈ᵣ-isProp p q)

≈ᵣ-refl : ∀{ξ} → ξ ≈ᵣ ξ
≈ᵣ-refl {UIdRen} = IdRen≈ᵣ
≈ᵣ-refl {UKeep ξ} = UKeep≈ᵣ ≈ᵣ-refl
≈ᵣ-refl {UDrop ξ} = UDrop≈ᵣ ≈ᵣ-refl

≡⇒≈ᵣ : _≡_ ⇒ _≈ᵣ_
≡⇒≈ᵣ refl = ≈ᵣ-refl

≈ᵣ-sym : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → ξ2 ≈ᵣ ξ1
≈ᵣ-sym IdRen≈ᵣ = IdRen≈ᵣ
≈ᵣ-sym (UKeep≈ᵣ p) = UKeep≈ᵣ (≈ᵣ-sym p)
≈ᵣ-sym (UDrop≈ᵣ p) = UDrop≈ᵣ (≈ᵣ-sym p)
≈ᵣ-sym (Keep-Id≈ᵣId p) = Id≈ᵣKeep-Id (≈ᵣ-sym p)
≈ᵣ-sym (Id≈ᵣKeep-Id p) = Keep-Id≈ᵣId (≈ᵣ-sym p)

≈ᵣ-trans : ∀{ξ1 ξ2 ξ3} → ξ1 ≈ᵣ ξ2 → ξ2 ≈ᵣ ξ3 → ξ1 ≈ᵣ ξ3
≈ᵣ-trans IdRen≈ᵣ IdRen≈ᵣ = IdRen≈ᵣ
≈ᵣ-trans IdRen≈ᵣ (Id≈ᵣKeep-Id q) = Id≈ᵣKeep-Id q
≈ᵣ-trans (UKeep≈ᵣ p) (UKeep≈ᵣ q) = UKeep≈ᵣ (≈ᵣ-trans p q)
≈ᵣ-trans (UKeep≈ᵣ p) (Keep-Id≈ᵣId q) = Keep-Id≈ᵣId (≈ᵣ-trans p q)
≈ᵣ-trans (UDrop≈ᵣ p) (UDrop≈ᵣ q) = UDrop≈ᵣ (≈ᵣ-trans p q)
≈ᵣ-trans (Keep-Id≈ᵣId p) IdRen≈ᵣ = Keep-Id≈ᵣId p
≈ᵣ-trans (Keep-Id≈ᵣId p) (Id≈ᵣKeep-Id q) = UKeep≈ᵣ (≈ᵣ-trans p q)
≈ᵣ-trans (Id≈ᵣKeep-Id p) (UKeep≈ᵣ q) = Id≈ᵣKeep-Id (≈ᵣ-trans p q)
≈ᵣ-trans (Id≈ᵣKeep-Id p) (Keep-Id≈ᵣId q) = ≈ᵣ-trans p q

infix  3 _≈ᵣ∎
infixr 2 step-≈ᵣ

step-≈ᵣ : ∀ (x {y z} : URen) → y ≈ᵣ z → x ≈ᵣ y → x ≈ᵣ z
step-≈ᵣ _ y≡z x≡y = ≈ᵣ-trans x≡y y≡z

_≈ᵣ∎ : ∀ (x : URen) → x ≈ᵣ x
_≈ᵣ∎ _ = ≈ᵣ-refl

syntax step-≈ᵣ  x y≡z x≡y = x ≈ᵣ⟨ x≡y ⟩ y≡z

UKeep-inj : Injective _≡_ _≡_ UKeep
UKeep-inj refl = refl

UKeep-inj≈ᵣ : Injective _≈ᵣ_ _≈ᵣ_ UKeep
UKeep-inj≈ᵣ (UKeep≈ᵣ p) = p

UDrop-inj : Injective _≡_ _≡_ UDrop
UDrop-inj refl = refl

UDrop-inj≈ᵣ : Injective _≈ᵣ_ _≈ᵣ_ UDrop
UDrop-inj≈ᵣ (UDrop≈ᵣ p) = p

_•U_ : URen → URen → URen
UIdRen •U ξ2 = ξ2
UKeep ξ1 •U UIdRen = UKeep ξ1
UKeep ξ1 •U UKeep ξ2 = UKeep (ξ1 •U ξ2)
UKeep ξ1 •U UDrop ξ2 = UDrop (ξ1 •U ξ2)
UDrop ξ1 •U UIdRen = UDrop ξ1
UDrop ξ1 •U UKeep ξ2 = UDrop (ξ1 •U UKeep ξ2)
UDrop ξ1 •U UDrop ξ2 = UDrop (ξ1 •U UDrop ξ2)

•U-id-l : ∀{ξ1} → ξ1 ≈ᵣ UIdRen → (ξ2 : URen) → ξ1 •U ξ2 ≈ᵣ ξ2
•U-id-l IdRen≈ᵣ ξ2 = ≈ᵣ-refl
•U-id-l (Keep-Id≈ᵣId p) UIdRen = Keep-Id≈ᵣId p
•U-id-l (Keep-Id≈ᵣId p) (UKeep ξ2) = UKeep≈ᵣ (•U-id-l p ξ2)
•U-id-l (Keep-Id≈ᵣId p) (UDrop ξ2) = UDrop≈ᵣ (•U-id-l p ξ2)

•U-id-r : ∀{ξ2} (ξ1 : URen) → ξ2 ≈ᵣ UIdRen → ξ1 •U ξ2 ≈ᵣ ξ1
•U-id-r UIdRen IdRen≈ᵣ = IdRen≈ᵣ
•U-id-r UIdRen (Keep-Id≈ᵣId p) = Keep-Id≈ᵣId p
•U-id-r (UKeep ξ1) IdRen≈ᵣ = ≈ᵣ-refl
•U-id-r (UKeep ξ1) (Keep-Id≈ᵣId p) = UKeep≈ᵣ (•U-id-r ξ1 p)
•U-id-r (UDrop ξ1) IdRen≈ᵣ = ≈ᵣ-refl
•U-id-r (UDrop ξ1) (Keep-Id≈ᵣId p) = UDrop≈ᵣ (•U-id-r ξ1 (Keep-Id≈ᵣId p))

•U-resp-≈ᵣ-l : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → (ξ3 : URen) → ξ1 •U ξ3 ≈ᵣ ξ2 •U ξ3
•U-resp-≈ᵣ-l IdRen≈ᵣ ξ3 = ≈ᵣ-refl
•U-resp-≈ᵣ-l (UKeep≈ᵣ p) UIdRen = UKeep≈ᵣ p
•U-resp-≈ᵣ-l (UKeep≈ᵣ p) (UKeep ξ3) = UKeep≈ᵣ (•U-resp-≈ᵣ-l p ξ3)
•U-resp-≈ᵣ-l (UKeep≈ᵣ p) (UDrop ξ3) = UDrop≈ᵣ (•U-resp-≈ᵣ-l p ξ3)
•U-resp-≈ᵣ-l (UDrop≈ᵣ p) UIdRen = UDrop≈ᵣ p
•U-resp-≈ᵣ-l (UDrop≈ᵣ p) (UKeep ξ3) = UDrop≈ᵣ (•U-resp-≈ᵣ-l p (UKeep ξ3))
•U-resp-≈ᵣ-l (UDrop≈ᵣ p) (UDrop ξ3) = UDrop≈ᵣ (•U-resp-≈ᵣ-l p (UDrop ξ3))
•U-resp-≈ᵣ-l (Keep-Id≈ᵣId p) UIdRen = Keep-Id≈ᵣId p
•U-resp-≈ᵣ-l (Keep-Id≈ᵣId p) (UKeep ξ3) = UKeep≈ᵣ (•U-resp-≈ᵣ-l p ξ3)
•U-resp-≈ᵣ-l (Keep-Id≈ᵣId p) (UDrop ξ3) = UDrop≈ᵣ (•U-resp-≈ᵣ-l p ξ3)
•U-resp-≈ᵣ-l (Id≈ᵣKeep-Id p) UIdRen = Id≈ᵣKeep-Id p
•U-resp-≈ᵣ-l (Id≈ᵣKeep-Id p) (UKeep ξ3) = UKeep≈ᵣ (•U-resp-≈ᵣ-l p ξ3)
•U-resp-≈ᵣ-l (Id≈ᵣKeep-Id p) (UDrop ξ3) = UDrop≈ᵣ (•U-resp-≈ᵣ-l p ξ3)

•U-resp-≈ᵣ-r : ∀{ξ2 ξ3} → (ξ1 : URen) → ξ2 ≈ᵣ ξ3 → ξ1 •U ξ2 ≈ᵣ ξ1 •U ξ3
•U-resp-≈ᵣ-r UIdRen p = p
•U-resp-≈ᵣ-r (UKeep ξ1) IdRen≈ᵣ = ≈ᵣ-refl
•U-resp-≈ᵣ-r (UKeep ξ1) (UKeep≈ᵣ p) = UKeep≈ᵣ (•U-resp-≈ᵣ-r ξ1 p)
•U-resp-≈ᵣ-r (UKeep ξ1) (UDrop≈ᵣ p) = UDrop≈ᵣ (•U-resp-≈ᵣ-r ξ1 p)
•U-resp-≈ᵣ-r (UKeep ξ1) (Keep-Id≈ᵣId p) = UKeep≈ᵣ (•U-id-r ξ1 p)
•U-resp-≈ᵣ-r (UKeep ξ1) (Id≈ᵣKeep-Id p) = UKeep≈ᵣ (≈ᵣ-sym (•U-id-r ξ1 (≈ᵣ-sym p)))
•U-resp-≈ᵣ-r (UDrop ξ1) IdRen≈ᵣ = ≈ᵣ-refl
•U-resp-≈ᵣ-r (UDrop ξ1) (UKeep≈ᵣ p) = UDrop≈ᵣ (•U-resp-≈ᵣ-r ξ1 (UKeep≈ᵣ p))
•U-resp-≈ᵣ-r (UDrop ξ1) (UDrop≈ᵣ p) = UDrop≈ᵣ (•U-resp-≈ᵣ-r ξ1 (UDrop≈ᵣ p))
•U-resp-≈ᵣ-r (UDrop ξ1) (Keep-Id≈ᵣId p) = UDrop≈ᵣ (•U-id-r ξ1 (Keep-Id≈ᵣId p))
•U-resp-≈ᵣ-r (UDrop ξ1) (Id≈ᵣKeep-Id p) = UDrop≈ᵣ (≈ᵣ-sym (•U-id-r ξ1 (Keep-Id≈ᵣId (≈ᵣ-sym p))))

•U-resp-≈ᵣ : ∀{ξ1 ξ2 ξ3 ξ4} → ξ1 ≈ᵣ ξ2 → ξ3 ≈ᵣ ξ4 → ξ1 •U ξ3 ≈ᵣ ξ2 •U ξ4
•U-resp-≈ᵣ {ξ1} {ξ2} {ξ3} {ξ4} p q = 
  (ξ1 •U ξ3) ≈ᵣ⟨ •U-resp-≈ᵣ-l p ξ3 ⟩
  (ξ2 •U ξ3) ≈ᵣ⟨ •U-resp-≈ᵣ-r ξ2 q ⟩
  (ξ2 •U ξ4) ≈ᵣ∎

UKeep* : URen → ℕ → URen
UKeep* ξ zero = ξ
UKeep* ξ (suc k) = UKeep (UKeep* ξ k)

UKeep*-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → (n : ℕ) → UKeep* ξ1 n ≈ᵣ UKeep* ξ2 n
UKeep*-resp-≈ᵣ p zero = p
UKeep*-resp-≈ᵣ p (suc n) = UKeep≈ᵣ (UKeep*-resp-≈ᵣ p n)

UKeep*-IdRenIdRen≈ᵣ : (n : ℕ) → UKeep* UIdRen n ≈ᵣ UIdRen
UKeep*-IdRenIdRen≈ᵣ zero = IdRen≈ᵣ
UKeep*-IdRenIdRen≈ᵣ (suc n) = Keep-Id≈ᵣId (UKeep*-IdRenIdRen≈ᵣ n)

UDrop* : URen → ℕ → URen
UDrop* ξ zero = ξ
UDrop* ξ (suc k) = UDrop (UDrop* ξ k)

UDrop*-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → (n : ℕ) → UDrop* ξ1 n ≈ᵣ UDrop* ξ2 n
UDrop*-resp-≈ᵣ p zero = p
UDrop*-resp-≈ᵣ p (suc n) = UDrop≈ᵣ (UDrop*-resp-≈ᵣ p n)

renVarUnty : URen → ℕ → ℕ
renVarUnty UIdRen x = x
renVarUnty (UKeep ξ) zero = zero
renVarUnty (UKeep ξ) (suc x) = suc (renVarUnty ξ x)
renVarUnty (UDrop ξ) x = suc (renVarUnty ξ x)

renVarUnty-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → renVarUnty ξ1 ≗ renVarUnty ξ2
renVarUnty-resp-≈ᵣ IdRen≈ᵣ x = refl
renVarUnty-resp-≈ᵣ (UKeep≈ᵣ p) zero = refl
renVarUnty-resp-≈ᵣ (UKeep≈ᵣ p) (suc x) = cong suc (renVarUnty-resp-≈ᵣ p x)
renVarUnty-resp-≈ᵣ (UDrop≈ᵣ p) x = cong suc (renVarUnty-resp-≈ᵣ p x)
renVarUnty-resp-≈ᵣ (Keep-Id≈ᵣId p) zero = refl
renVarUnty-resp-≈ᵣ (Keep-Id≈ᵣId p) (suc x) = cong suc (renVarUnty-resp-≈ᵣ p x)
renVarUnty-resp-≈ᵣ (Id≈ᵣKeep-Id p) zero = refl
renVarUnty-resp-≈ᵣ (Id≈ᵣKeep-Id p) (suc x) = cong suc (renVarUnty-resp-≈ᵣ p x)

renUnty : URen → UTm → UTm
renVecUnty : URen → UTmVec → UTmVec

renUnty ξ (var x) = var (renVarUnty ξ x)
renUnty ξ (constr s es) = constr s (renVecUnty ξ es)

renVecUnty ξ [] = []
renVecUnty ξ ((e , k) ∷ es) = (renUnty (UKeep* ξ k) e , k) ∷ renVecUnty ξ es

renUnty-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → renUnty ξ1 ≗ renUnty ξ2
renVecUnty-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → renVecUnty ξ1 ≗ renVecUnty ξ2

renUnty-resp-≈ᵣ p (var x) = cong var (renVarUnty-resp-≈ᵣ p x)
renUnty-resp-≈ᵣ p (constr s es) = cong (constr s) (renVecUnty-resp-≈ᵣ p es)

renVecUnty-resp-≈ᵣ p [] = refl
renVecUnty-resp-≈ᵣ p ((e , k) ∷ es) =
  cong₂ (λ x y → (x , k) ∷ y)
    (renUnty-resp-≈ᵣ (UKeep*-resp-≈ᵣ p k) e)
    (renVecUnty-resp-≈ᵣ p es)

------------------
-- SUBSTITUTION --
------------------

data USub : Set where
  USubε : USub
  _▹_ : (σ : USub) (e : UTm) → USub

▹-inj : ∀{σ1 σ2 e1 e2} → σ1 ▹ e1 ≡ σ2 ▹ e2 → σ1 ≡ σ2 × e1 ≡ e2
▹-inj refl = refl , refl

infixr 9 _•◦U_
_•◦U_ : URen → USub → USub
ξ •◦U USubε = USubε
ξ •◦U (σ ▹ e) = (ξ •◦U σ) ▹ renUnty ξ e

•◦U-resp-≈ᵣ : ∀{ξ1 ξ2} → ξ1 ≈ᵣ ξ2 → (σ : USub) → ξ1 •◦U σ ≡ ξ2 •◦U σ
•◦U-resp-≈ᵣ p USubε = refl
•◦U-resp-≈ᵣ p (σ ▹ e) =
  cong₂ _▹_
    (•◦U-resp-≈ᵣ p σ)
    (renUnty-resp-≈ᵣ p e)

UDropSub : USub → USub
UDropSub σ = UDrop UIdRen •◦U σ

UKeepSub : USub → USub
UKeepSub σ = UDropSub σ ▹ var zero

UKeepSub* : USub → ℕ → USub
UKeepSub* σ zero = σ
UKeepSub* σ (suc k) = UKeepSub (UKeepSub* σ k)

UDropSub* : USub → ℕ → USub
UDropSub* σ zero = σ
UDropSub* σ (suc k) = UDropSub (UDropSub* σ k)

subVarUnty : USub → ℕ → UTm
subVarUnty USubε x = var x
subVarUnty (σ ▹ e) zero = e
subVarUnty (σ ▹ e) (suc x) = subVarUnty σ x

subUnty : USub → UTm → UTm
subVecUnty : USub → UTmVec → UTmVec

subUnty σ (var x) = subVarUnty σ x
subUnty σ (constr s es) = constr s (subVecUnty σ es)

subVecUnty σ [] = []
subVecUnty σ ((e , k) ∷ es) = (subUnty (UKeepSub* σ k) e , k) ∷ subVecUnty σ es

infixr 9 _◦U_ 
_◦U_ : USub → USub → USub
σ1 ◦U USubε = USubε
σ1 ◦U (σ2 ▹ e) = (σ1 ◦U σ2) ▹ subUnty σ1 e

------------------
-- TYPE ERASURE --
------------------

-- Convert a typed to an untyped representation
eraseVar : ∀{Γ t} → Var Γ t → ℕ
eraseVar V0 = zero
eraseVar (VS x) = suc (eraseVar x)

erase : ∀{Γ t} → Tm Γ t → UTm
eraseVec : ∀{Γ Σ} → TmVec Γ Σ → UTmVec

erase (var x) = var (eraseVar x)
erase (constr s es) = constr s (eraseVec es)

eraseVec [] = []
eraseVec (_∷_ {Δ = Δ} e es) = (erase e , length Δ) ∷ eraseVec es

eraseRen : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → URen
eraseRen ε = UIdRen
eraseRen (Keep ξ) = UKeep (eraseRen ξ)
eraseRen (Drop ξ) = UDrop (eraseRen ξ)

eraseSub : ∀{Γ1 Γ2} → Sub Γ1 Γ2 → USub
eraseSub ε = USubε
eraseSub (σ ▸ e) = eraseSub σ ▹ erase e

-- Type erasure is injective
eraseVar-injH : ∀{Γ1 Γ2 t1 t2} {x : Var Γ1 t1} {y : Var Γ2 t2}
                (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
                eraseVar x ≡ eraseVar y →
                subst₂ Var p q x ≡ y
eraseVar-injH {x = V0} {V0} refl refl refl = refl
eraseVar-injH {x = VS x} {VS y} refl refl r =
  cong VS (eraseVar-injH {x = x} {y} refl refl (suc-injective r))

erase-injH : ∀{Γ1 Γ2 t1 t2} {x : Tm Γ1 t1} {y : Tm Γ2 t2} →
            (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
            erase x ≡ erase y →
            subst₂ Tm p q x ≡ y
eraseVec-injH : ∀{Γ1 Γ2 Σ1 Σ2} {x : TmVec Γ1 Σ1} {y : TmVec Γ2 Σ2} →
                (p : Γ1 ≡ Γ2) (q : Σ1 ≡ Σ2) →
                eraseVec x ≡ eraseVec y →
                subst₂ TmVec p q x ≡ y

erase-injH {x = var x} {var y} refl refl r = cong var (eraseVar-injH refl refl (unVar-inj r))
erase-injH {x = constr s1 es1} {constr s2 es2} refl q r with unConstr-inj r .fst
erase-injH {x = constr s1 es1} {constr .s1 es2} refl refl r | refl =
  cong (constr s1) (eraseVec-injH refl refl (unConstr-inj r .snd))

eraseVec-injH {x = []} {[]} refl refl refl = refl
eraseVec-injH {x = e1 ∷ es1} {e2 ∷ es2} refl refl r =
  cong₂ _∷_
  (erase-injH refl refl (unCons-inj r .fst))
  (eraseVec-injH refl refl (unCons-inj r .snd .snd))

eraseRen-injH : ∀{Γ1 Γ1' Γ2 Γ2'} {ξ1 : Ren Γ1 Γ2} {ξ2 : Ren Γ1' Γ2'} →
              (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
              eraseRen ξ1 ≡ eraseRen ξ2 →
              subst₂ Ren p q ξ1 ≡ ξ2
eraseRen-injH {ξ1 = ε} {ε} refl refl r = refl
eraseRen-injH {ξ1 = Keep ξ1} {Keep ξ2} refl refl r =
  cong Keep (eraseRen-injH refl refl (UKeep-inj r))
eraseRen-injH {ξ1 = Drop ξ1} {Drop ξ2} refl refl r =
  cong Drop (eraseRen-injH refl refl (UDrop-inj r))

eraseRen-injH≈ᵣ : ∀{Γ1 Γ1' Γ2 Γ2'} {ξ1 : Ren Γ1 Γ2} {ξ2 : Ren Γ1' Γ2'} →
                  (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
                  eraseRen ξ1 ≈ᵣ eraseRen ξ2 →
                  subst₂ Ren p q ξ1 ≡ ξ2
eraseRen-injH≈ᵣ {ξ1 = ε} {ε} refl refl r = refl
eraseRen-injH≈ᵣ {ξ1 = Keep ξ1} {Keep ξ2} refl refl r =
  cong Keep (eraseRen-injH≈ᵣ refl refl (UKeep-inj≈ᵣ r))
eraseRen-injH≈ᵣ {ξ1 = Drop ξ1} {Drop ξ2} refl refl r =
  cong Drop (eraseRen-injH≈ᵣ refl refl (UDrop-inj≈ᵣ r))

eraseSub-injH : ∀{Γ1 Γ1' Γ2 Γ2'} {σ1 : Sub Γ1 Γ2} {σ2 : Sub Γ1' Γ2'} →
               (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
               eraseSub σ1 ≡ eraseSub σ2 →
               subst₂ Sub p q σ1 ≡ σ2
eraseSub-injH {σ1 = ε} {ε} refl refl r = refl
eraseSub-injH {σ1 = σ1 ▸ e1} {σ2 ▸ e2} refl refl r =
  cong₂ _▸_
    (eraseSub-injH refl refl (▹-inj r .fst))
    (erase-injH refl refl (▹-inj r .snd))

eraseVar-inj : ∀{Γ t} {x y : Var Γ t} → eraseVar x ≡ eraseVar y → x ≡ y
eraseVar-inj = eraseVar-injH refl refl

erase-inj : ∀{Γ t} {x y : Tm Γ t} → erase x ≡ erase y → x ≡ y
erase-inj = erase-injH refl refl

eraseVec-inj : ∀{Γ Σ} {x y : TmVec Γ Σ} → eraseVec x ≡ eraseVec y → x ≡ y
eraseVec-inj = eraseVec-injH refl refl

eraseRen-inj : ∀{Γ1 Γ2} {ξ1 ξ2 : Ren Γ1 Γ2} → eraseRen ξ1 ≡ eraseRen ξ2 → ξ1 ≡ ξ2
eraseRen-inj = eraseRen-injH refl refl

eraseRen-inj≈ᵣ : ∀{Γ1 Γ2} {ξ1 ξ2 : Ren Γ1 Γ2} → eraseRen ξ1 ≈ᵣ eraseRen ξ2 → ξ1 ≡ ξ2
eraseRen-inj≈ᵣ = eraseRen-injH≈ᵣ refl refl

eraseSub-inj : ∀{Γ1 Γ2} {σ1 σ2 : Sub Γ1 Γ2} → eraseSub σ1 ≡ eraseSub σ2 → σ1 ≡ σ2
eraseSub-inj = eraseSub-injH refl refl

-- Type erasure distributes over renaming operations
eraseRen-Id : ∀{Γ} → eraseRen (IdRen {Γ}) ≡ UKeep* UIdRen (length Γ)
eraseRen-Id {[]} = refl
eraseRen-Id {t ∷ Γ} = cong UKeep eraseRen-Id

eraseRen-Keep* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) (Δ : Ctx) →
                 eraseRen (Keep* ξ Δ) ≡ UKeep* (eraseRen ξ) (length Δ)
eraseRen-Keep* ξ [] = refl
eraseRen-Keep* ξ (t ∷ Δ) = cong UKeep (eraseRen-Keep* ξ Δ)

eraseRen-Drop* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) (Δ : Ctx) →
                 eraseRen (Drop* ξ Δ) ≡ UDrop* (eraseRen ξ) (length Δ)
eraseRen-Drop* ξ [] = refl
eraseRen-Drop* ξ (t ∷ Δ) = cong UDrop (eraseRen-Drop* ξ Δ)

-- Type erasure distributes over the action of renaming
eraseVar-distr-ren : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (x : Var Γ1 t) →
                    eraseVar (renVar ξ x) ≡ renVarUnty (eraseRen ξ) (eraseVar x)
eraseVar-distr-ren (Keep ξ) V0 = refl
eraseVar-distr-ren (Keep ξ) (VS x) = cong suc (eraseVar-distr-ren ξ x)
eraseVar-distr-ren (Drop ξ) x = cong suc (eraseVar-distr-ren ξ x)

erase-distr-ren : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (e : Tm Γ1 t) →
                 erase (ren ξ e) ≡ renUnty (eraseRen ξ) (erase e)
eraseVec-distr-ren : ∀{Γ1 Γ2 Σ} (ξ : Ren Γ1 Γ2) (es : TmVec Γ1 Σ) →
                    eraseVec (renVec ξ es) ≡ renVecUnty (eraseRen ξ) (eraseVec es)

erase-distr-ren ξ (var x) = cong var (eraseVar-distr-ren ξ x)
erase-distr-ren ξ (constr s es) = cong (constr s) (eraseVec-distr-ren ξ es)

eraseVec-distr-ren ξ [] = refl
eraseVec-distr-ren ξ (_∷_ {Δ = Δ} {Σ = Σ} e es) = cong₃ eraseCons
  (erase (ren (Keep* ξ Δ) e)
    ≡⟨ erase-distr-ren (Keep* ξ Δ) e ⟩
  renUnty (eraseRen (Keep* ξ Δ)) (erase e)
    ≡⟨ (cong (flip renUnty (erase e)) $ eraseRen-Keep* ξ Δ) ⟩
  renUnty (UKeep* (eraseRen ξ) (length Δ)) (erase e) ∎)
  refl
  (eraseVec-distr-ren ξ es)

-- Type erasure distributes over substitution operations
erase-•◦U : ∀{Γ1 Γ2 Γ3} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
            eraseSub (ξ •◦ σ) ≡ eraseRen ξ •◦U eraseSub σ
erase-•◦U ξ ε = refl
erase-•◦U ξ (σ ▸ e) = cong₂ _▹_ (erase-•◦U ξ σ) (erase-distr-ren ξ e)

eraseSub-distr-DropSub : ∀{Γ1 Γ2 t} (σ : Sub Γ1 Γ2) →
                          eraseSub (DropSub {t = t} σ) ≡ UDropSub (eraseSub σ)
eraseSub-distr-DropSub {Γ1} {Γ2} σ =
  eraseSub (Drop IdRen •◦ σ)
    ≡⟨ erase-•◦U (Drop IdRen) σ ⟩
  UDrop (eraseRen IdRen) •◦U eraseSub σ
    ≡⟨ (cong (λ x → UDrop x •◦U eraseSub σ) $ eraseRen-Id) ⟩
  UDrop (UKeep* UIdRen (length Γ2)) •◦U eraseSub σ
    ≡⟨ •◦U-resp-≈ᵣ (UDrop≈ᵣ (UKeep*-IdRenIdRen≈ᵣ (length Γ2))) (eraseSub σ) ⟩
  UDrop UIdRen •◦U eraseSub σ ∎

eraseSub-distr-KeepSub : ∀{Γ1 Γ2 t} (σ : Sub Γ1 Γ2) →
                         eraseSub (KeepSub {t = t} σ) ≡ UKeepSub (eraseSub σ)
eraseSub-distr-KeepSub σ = cong (λ x → x ▹ var zero) (eraseSub-distr-DropSub σ)

eraseSub-distr-KeepSub* : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) (Δ : Ctx) →
                 eraseSub (KeepSub* σ Δ) ≡ UKeepSub* (eraseSub σ) (length Δ)
eraseSub-distr-KeepSub* σ [] = refl
eraseSub-distr-KeepSub* σ (t ∷ Δ) =
  eraseSub (KeepSub (KeepSub* σ Δ))
    ≡⟨ eraseSub-distr-KeepSub (KeepSub* σ Δ) ⟩
  UKeepSub (eraseSub (KeepSub* σ Δ))
    ≡⟨ cong UKeepSub (eraseSub-distr-KeepSub* σ Δ) ⟩
  UKeepSub (UKeepSub* (eraseSub σ) (length Δ)) ∎

eraseSub-distr-DropSub* : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) (Δ : Ctx) →
                          eraseSub (DropSub* σ Δ) ≡ UDropSub* (eraseSub σ) (length Δ)
eraseSub-distr-DropSub* σ [] = refl
eraseSub-distr-DropSub* σ (t ∷ Δ) =
  eraseSub (DropSub (DropSub* σ Δ))
    ≡⟨ eraseSub-distr-DropSub (DropSub* σ Δ) ⟩
  UDropSub (eraseSub (DropSub* σ Δ))
    ≡⟨ cong UDropSub (eraseSub-distr-DropSub* σ Δ) ⟩
  UDropSub (UDropSub* (eraseSub σ) (length Δ)) ∎

-- Type erasure distributes over the action of substitution
eraseVar-distr-sub : ∀{Γ1 Γ2 t} (σ : Sub Γ1 Γ2) (x : Var Γ1 t) →
                    erase (subVar σ x) ≡ subVarUnty (eraseSub σ) (eraseVar x)
eraseVar-distr-sub (σ ▸ e) V0 = refl
eraseVar-distr-sub (σ ▸ e) (VS x) = eraseVar-distr-sub σ x

eraseSub-distr-•◦ : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) (x : Var Γ1 t) →
              subVarUnty (eraseSub (ξ •◦ σ)) (eraseVar x) ≡
              renUnty (eraseRen ξ) (subVarUnty (eraseSub σ) (eraseVar x))
eraseSub-distr-•◦ ξ (σ ▸ e) V0 = erase-distr-ren ξ e
eraseSub-distr-•◦ ξ (σ ▸ e) (VS x) = eraseSub-distr-•◦ ξ σ x

erase-distr-sub : ∀{Γ1 Γ2 t} (σ : Sub Γ1 Γ2) (e : Tm Γ1 t) →
                 erase (sub σ e) ≡ subUnty (eraseSub σ) (erase e)
eraseVec-distr-sub : ∀{Γ1 Γ2 Σ} (σ : Sub Γ1 Γ2) (es : TmVec Γ1 Σ) →
                    eraseVec (subVec σ es) ≡ subVecUnty (eraseSub σ) (eraseVec es)

erase-distr-sub σ (var x) = eraseVar-distr-sub σ x
erase-distr-sub σ (constr s es) = cong (constr s) (eraseVec-distr-sub σ es)

eraseVec-distr-sub σ [] = refl
eraseVec-distr-sub σ (_∷_ {Δ} {t} {Σ} e es) =
  cong₂ (λ x y → (x , length Δ) ∷ y)
    (erase (sub (KeepSub* σ Δ) e)
      ≡⟨ erase-distr-sub (KeepSub* σ Δ) e ⟩
    subUnty (eraseSub (KeepSub* σ Δ)) (erase e)
      ≡⟨ cong (flip subUnty (erase e)) (eraseSub-distr-KeepSub* σ Δ) ⟩
    subUnty (UKeepSub* (eraseSub σ) (length Δ)) (erase e) ∎)
    (eraseVec-distr-sub σ es)

-- Type erasure is invariant under propositional equality substitution
subst₂-eraseVar : ∀{Γ1 Γ2 t1 t2}
               (p : Γ1 ≡ Γ2) (q : t1 ≡ t2)
               (x : Var Γ1 t1) →
               eraseVar x ≡ eraseVar (subst₂ Var p q x)
subst₂-eraseVar refl refl x = refl

substCtx-eraseVar : ∀{Γ1 Γ2 t}
                   (p : Γ1 ≡ Γ2)
                   (x : Var Γ1 t) →
                  eraseVar x ≡ eraseVar (subst (flip Var t) p x)
substCtx-eraseVar refl x = refl

substTy-eraseVar : ∀{Γ t1 t2}
                   (p : t1 ≡ t2)
                   (x : Var Γ t1) →
                  eraseVar x ≡ eraseVar (subst (Var Γ) p x)
substTy-eraseVar refl x = refl

subst₂-erase : ∀{Γ1 Γ2 t1 t2}
              (p : Γ1 ≡ Γ2) (q : t1 ≡ t2)
              (x : Tm Γ1 t1) →
              erase x ≡ erase (subst₂ Tm p q x)
subst₂-erase refl refl x = refl

substCtx-erase : ∀{Γ1 Γ2 t}
                (p : Γ1 ≡ Γ2)
                (x : Tm Γ1 t) →
                erase x ≡ erase (subst (flip Tm t) p x)
substCtx-erase refl x = refl

substTy-erase : ∀{Γ t1 t2}
                (p : t1 ≡ t2)
                (x : Tm Γ t1) →
                erase x ≡ erase (subst (Tm Γ) p x)
substTy-erase refl x = refl

subst₂-eraseVec : ∀{Γ1 Γ2 Σ1 Σ2}
                (p : Γ1 ≡ Γ2) (q : Σ1 ≡ Σ2)
                (x : TmVec Γ1 Σ1) →
                eraseVec x ≡ eraseVec (subst₂ TmVec p q x)
subst₂-eraseVec refl refl x = refl

substCtx-eraseVec : ∀{Γ1 Γ2 Σ}
                   (p : Γ1 ≡ Γ2)
                   (x : TmVec Γ1 Σ) →
                  eraseVec x ≡ eraseVec (subst (flip TmVec Σ) p x)
substCtx-eraseVec refl x = refl

substTy-eraseVec : ∀{Γ Σ1 Σ2}
                   (p : Σ1 ≡ Σ2)
                   (x : TmVec Γ Σ1) →
                  eraseVec x ≡ eraseVec (subst (TmVec Γ) p x)
substTy-eraseVec refl x = refl

subst₂-eraseSub : ∀{Γ1 Γ1' Γ2 Γ2'}
                  (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2')
                  (σ : Sub Γ1 Γ2) →
                  eraseSub σ ≡ eraseSub (subst₂ Sub p q σ)
subst₂-eraseSub refl refl σ = refl

subst-fst-eraseSub : ∀{Γ1 Γ1' Γ2}
                    (p : Γ1 ≡ Γ1')
                    (σ : Sub Γ1 Γ2) →
                    eraseSub σ ≡ eraseSub (subst (flip Sub Γ2) p σ)
subst-fst-eraseSub refl σ = refl

subst-snd-eraseSub : ∀{Γ1 Γ2 Γ2'}
                    (p : Γ2 ≡ Γ2')
                    (σ : Sub Γ1 Γ2) →
                    eraseSub σ ≡ eraseSub (subst (Sub Γ1) p σ)
subst-snd-eraseSub refl σ = refl

subst₂-eraseRen : ∀{Γ1 Γ1' Γ2 Γ2'}
                  (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2')
                  (ξ : Ren Γ1 Γ2) →
                  eraseRen ξ ≡ eraseRen (subst₂ Ren p q ξ)
subst₂-eraseRen refl refl ξ = refl
 
subst-fst-eraseRen : ∀{Γ1 Γ1' Γ2}
                    (p : Γ1 ≡ Γ1')
                    (ξ : Ren Γ1 Γ2) →
                    eraseRen ξ ≡ eraseRen (subst (flip Ren Γ2) p ξ)
subst-fst-eraseRen refl ξ = refl
 
subst-snd-eraseRen : ∀{Γ1 Γ2 Γ2'}
                    (p : Γ2 ≡ Γ2')
                    (ξ : Ren Γ1 Γ2) →
                    eraseRen ξ ≡ eraseRen (subst (Ren Γ1) p ξ)
subst-snd-eraseRen refl ξ = refl

---------------------
-- TYPING JUDGMENT --
---------------------

-- Explicit typing judgment for variables
data _⊢var_∶_ : Ctx → ℕ → ⅀ .Knd → Set where
  ⊢0 : ∀{Γ κ} → (κ ∷ Γ) ⊢var 0 ∶ κ
  ⊢S : ∀{Γ κ1 κ2 x} →
        Γ ⊢var x ∶ κ1 →
        (κ2 ∷ Γ) ⊢var suc x ∶ κ1

varTyped = _⊢var_∶_

-- The typing judgment for variables is a proposition
⊢var-isProp : ∀{Γ x κ} → isProp (Γ ⊢var x ∶ κ)
⊢var-isProp ⊢0 ⊢0 = refl
⊢var-isProp (⊢S p) (⊢S q) = cong ⊢S (⊢var-isProp p q)

-- Types of variables are unique
⊢var-uniq : ∀{Γ x κ1 κ2} → Γ ⊢var x ∶ κ1 → Γ ⊢var x ∶ κ2 → κ1 ≡ κ2
⊢var-uniq ⊢0 ⊢0 = refl
⊢var-uniq (⊢S x) (⊢S y) = ⊢var-uniq x y

-- Explicit typing judgment for terms
data _⊢_∶_ (Γ : Ctx) : UTm → ⅀ .Knd → Set
-- Explicit typing judgment for vectors
data _⊢vec_∶_ (Γ : Ctx) : UTmVec → List (Ctx × (⅀ .Knd)) → Set

data _⊢_∶_ Γ where
  ⊢var : ∀{x κ} → Γ ⊢var x ∶ κ → Γ ⊢ var x ∶ κ
  ⊢constr : ∀ s {es} →
            Γ ⊢vec es ∶ ⅀ .TyPos s .fst →
            Γ ⊢ constr s es ∶ ⅀ .TyPos s .snd

data _⊢vec_∶_ Γ where
  ⊢[] : Γ ⊢vec [] ∶ []
  ⊢∷ : ∀{e es Δ κ Σ} →
       (Δ ++ Γ) ⊢ e ∶ κ →
       Γ ⊢vec es ∶ Σ →
       Γ ⊢vec (e , length Δ) ∷ es ∶ ((Δ , κ) ∷ Σ)

typed = _⊢_∶_
vecTyped = _⊢vec_∶_

⊢∷-elim : ∀{Γ e es n Δ κ Σ} →
          (p : Γ ⊢vec ((e , n) ∷ es) ∶ ((Δ , κ) ∷ Σ)) →
          Σ[ q ∈ n ≡ length Δ ]
          Σ[ r ∈ (Δ ++ Γ) ⊢ e ∶ κ ]
          Σ[ s ∈ Γ ⊢vec es ∶ Σ ]
          subst (λ x → Γ ⊢vec ((e , x) ∷ es) ∶ ((Δ , κ) ∷ Σ)) q p
          ≡ ⊢∷ r s
⊢∷-elim (⊢∷ r s) = refl , r , s , refl          

-- The typing judgment is a proposition
⊢-isProp : ∀{Γ e κ} → isProp (Γ ⊢ e ∶ κ)
⊢vec-isProp : ∀{Γ es Σ} → isProp (Γ ⊢vec es ∶ Σ)

⊢-isProp (⊢var x) (⊢var y) = cong ⊢var (⊢var-isProp x y)
⊢-isProp (⊢constr s es1) (⊢constr .s es2) = cong (⊢constr s) (⊢vec-isProp es1 es2)

⊢vec-isProp ⊢[] ⊢[] = refl
⊢vec-isProp (⊢∷ e1 es1) (⊢∷ e2 es2) = cong₂ ⊢∷ (⊢-isProp e1 e2) (⊢vec-isProp es1 es2)

-- Types of terms are unique
⊢-uniq : ∀{Γ e κ1 κ2} → Γ ⊢ e ∶ κ1 → Γ ⊢ e ∶ κ2 → κ1 ≡ κ2
⊢-uniq (⊢var x1) (⊢var x2) = ⊢var-uniq x1 x2
⊢-uniq (⊢constr s es1) (⊢constr .s es2) = refl

-- An erased term is well-typed
⊢eraseVar : ∀{Γ κ} (x : Var Γ κ) → Γ ⊢var eraseVar x ∶ κ
⊢eraseVar V0 = ⊢0
⊢eraseVar (VS x) = ⊢S (⊢eraseVar x)

⊢erase : ∀{Γ κ} (e : Tm Γ κ) → Γ ⊢ erase e ∶ κ
⊢eraseVec : ∀{Γ Σ} (es : TmVec Γ Σ) → Γ ⊢vec eraseVec es ∶ Σ

⊢erase (var x) = ⊢var (⊢eraseVar x)
⊢erase (constr s es) = ⊢constr s (⊢eraseVec es)

⊢eraseVec [] = ⊢[]
⊢eraseVec (e ∷ es) = ⊢∷ (⊢erase e) (⊢eraseVec es) 

-- If two erased terms are equivalent, then they have the same type
erase≡⇒ty≡ : ∀{Γ κ1 κ2} {e1 : Tm Γ κ1} {e2 : Tm Γ κ2} →
             erase e1 ≡ erase e2 → κ1 ≡ κ2
erase≡⇒ty≡ {Γ} {κ1} {κ2} {e1} {e2} p =
  ⊢-uniq (⊢erase e1) $ subst (λ x → Γ ⊢ x ∶ κ2) (sym p) (⊢erase e2)

{-
Convert a proof of well-typedness of a term to
an inherently well-typed term
-}
toVar : ∀{x Γ κ} → Γ ⊢var x ∶ κ → Var Γ κ
toVar ⊢0 = V0
toVar (⊢S x) = VS (toVar x)

toTm : ∀{e Γ κ} → Γ ⊢ e ∶ κ → Tm Γ κ
toTmVec : ∀{es Γ Σ} → Γ ⊢vec es ∶ Σ → TmVec Γ Σ

toTm (⊢var x) = var (toVar x)
toTm (⊢constr s es) = constr s (toTmVec es)

toTmVec ⊢[] = []
toTmVec (⊢∷ e es) = toTm e ∷ toTmVec es

substTy-toTm-constr : ∀{Γ s es κ} →
                      (p : ⅀ .TyPos s .snd ≡ κ)
                      (⊢es : Γ ⊢vec es ∶ ⅀ .TyPos s .fst) →
                      toTm (subst (λ x → Γ ⊢ constr s es ∶ x) p (⊢constr s ⊢es))
                      ≡ subst (Tm Γ) p (constr s (toTmVec ⊢es))
substTy-toTm-constr refl ⊢es = refl

{-
Converting a proof of well-typedness of a term to
an inherently well-typed term and then erasing
the type results in the original raw term
-}
eraseVar∘toVar : ∀{x Γ κ} (⊢x : Γ ⊢var x ∶ κ) → eraseVar (toVar ⊢x) ≡ x
eraseVar∘toVar ⊢0 = refl
eraseVar∘toVar (⊢S x) = cong suc (eraseVar∘toVar x)

erase∘toTm : ∀{e Γ κ} (⊢e : Γ ⊢ e ∶ κ) → erase (toTm ⊢e) ≡ e
eraseVec∘toTmVec : ∀{es Γ Σ} (⊢es : Γ ⊢vec es ∶ Σ) → eraseVec (toTmVec ⊢es) ≡ es

erase∘toTm (⊢var x) = cong var (eraseVar∘toVar x)
erase∘toTm (⊢constr s es) = cong (constr s) (eraseVec∘toTmVec es)

eraseVec∘toTmVec ⊢[] = refl
eraseVec∘toTmVec (⊢∷ e es) = cong₃ eraseCons
  (erase∘toTm e)
  refl
  (eraseVec∘toTmVec es)

toVar∘⊢eraseVar : ∀{Γ κ} (x : Var Γ κ) → toVar (⊢eraseVar x) ≡ x
toVar∘⊢eraseVar V0 = refl
toVar∘⊢eraseVar (VS x) = cong VS (toVar∘⊢eraseVar x)

toTm∘⊢erase : ∀{Γ κ} (e : Tm Γ κ) → toTm (⊢erase e) ≡ e
toTmVec∘⊢eraseVec : ∀{Γ Σ} (es : TmVec Γ Σ) → toTmVec (⊢eraseVec es) ≡ es

toTm∘⊢erase (var x) = cong var (toVar∘⊢eraseVar x)
toTm∘⊢erase (constr s es) = cong (constr s) (toTmVec∘⊢eraseVec es)

toTmVec∘⊢eraseVec [] = refl
toTmVec∘⊢eraseVec (e ∷ es) = cong₂ _∷_ (toTm∘⊢erase e) (toTmVec∘⊢eraseVec es)

-- Inherent and non-inherent representations are isomorphic
untyped≅inherent : ∀{Γ κ} → (Σ[ e ∈ UTm ] Γ ⊢ e ∶ κ) ≅ Tm Γ κ
untyped≅inherent = Σ-Prop-≅
  (λ _ → ⊢-isProp)
  (λ _ → toTm)
  erase
  (λ e → erase∘toTm)
  ⊢erase
  toTm∘⊢erase
