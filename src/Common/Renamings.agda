{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common.Equality

module Common.Renamings where

---------------
-- RENAMINGS --
---------------

Ren : Set
Ren = ℕ → ℕ

Keep : Ren → Ren
Keep ξ zero = zero
Keep ξ (suc x) = suc (ξ x)

Keep-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (Keep ξ)
Keep-inj ξ-inj {x = zero} {zero} p = refl
Keep-inj ξ-inj {x = suc x} {suc y} p = cong suc (ξ-inj (suc-injective p))

Keep-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → Keep ξ1 ≗ Keep ξ2
Keep-ext p zero = refl
Keep-ext p (suc x) = cong suc (p x)

Keep-id : Keep id ≗ id
Keep-id zero = refl
Keep-id (suc x) = refl

Keep* : Ren → ℕ → Ren
Keep* ξ zero = ξ
Keep* ξ (suc k) = Keep (Keep* ξ k)

Keep*-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → (n : ℕ) → Injective _≡_ _≡_ (Keep* ξ n)
Keep*-inj ξ-inj zero = ξ-inj
Keep*-inj ξ-inj (suc n) = Keep-inj (Keep*-inj ξ-inj n)

Keep*-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → (n : ℕ) → Keep* ξ1 n ≗ Keep* ξ2 n
Keep*-ext p zero = p
Keep*-ext p (suc n) = Keep-ext (Keep*-ext p n)

Keep*-id : (n : ℕ) → Keep* id n ≗ id
Keep*-id zero = ≗-refl
Keep*-id (suc n) x = Keep-ext (Keep*-id n) x ∙ Keep-id x

Drop : Ren → Ren
Drop ξ x = suc (ξ x)

Drop-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (Drop ξ)
Drop-inj ξ-inj p = ξ-inj $ suc-injective p

Drop-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → Drop ξ1 ≗ Drop ξ2
Drop-ext p x = cong suc (p x)

Drop* : Ren → ℕ → Ren
Drop* ξ zero = ξ
Drop* ξ (suc k) = Drop (Drop* ξ k)

Drop*-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → (n : ℕ) → Injective _≡_ _≡_ (Drop* ξ n)
Drop*-inj ξ-inj zero = ξ-inj
Drop*-inj ξ-inj (suc n) = Drop-inj (Drop*-inj ξ-inj n)

Drop*-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → (n : ℕ) → Drop* ξ1 n ≗ Drop* ξ2 n
Drop*-ext p zero = p
Drop*-ext p (suc n) = Drop-ext (Drop*-ext p n)

_•_ : Ren → Ren → Ren
ξ1 • ξ2 = ξ1 ∘ ξ2

•-ext : ∀{ξ1 ξ1' ξ2 ξ2'} →
            ξ1 ≗ ξ1' →
            ξ2 ≗ ξ2' →
            ξ1 • ξ2 ≗ ξ1' • ξ2'
•-ext {ξ1} {ξ1'} {ξ2} {ξ2'} p q x =
  cong ξ1 (q x) ∙ p (ξ2' x)

Keep•Keep : (ξ1 ξ2 : Ren) → Keep ξ1 • Keep ξ2 ≗ Keep (ξ1 • ξ2)
Keep•Keep ξ1 ξ2 zero = refl
Keep•Keep ξ1 ξ2 (suc x) = refl

Keep*•Keep* : (ξ1 ξ2 : Ren) (n : ℕ) → Keep* ξ1 n • Keep* ξ2 n ≗ Keep* (ξ1 • ξ2) n
Keep*•Keep* ξ1 ξ2 zero = ≗-refl
Keep*•Keep* ξ1 ξ2 (suc n) x = 
  (Keep (Keep* ξ1 n) • Keep (Keep* ξ2 n)) x
    ≡⟨ Keep•Keep (Keep* ξ1 n) (Keep* ξ2 n) x ⟩
  Keep (Keep* ξ1 n • Keep* ξ2 n) x
    ≡⟨ Keep-ext (Keep*•Keep* ξ1 ξ2 n) x ⟩
  Keep (Keep* (ξ1 • ξ2) n) x ∎

Drop• : (ξ1 ξ2 : Ren) → Drop ξ1 • ξ2 ≗ Drop (ξ1 • ξ2)
Drop• ξ1 ξ2 x = refl

Drop*• : (ξ1 ξ2 : Ren) (n : ℕ) → Drop* ξ1 n • ξ2 ≗ Drop* (ξ1 • ξ2) n
Drop*• ξ1 ξ2 zero = ≗-refl
Drop*• ξ1 ξ2 (suc n) x = 
  (Drop (Drop* ξ1 n) • ξ2) x
    ≡⟨ Drop• (Drop* ξ1 n) ξ2 x ⟩
  Drop (Drop* ξ1 n • ξ2) x
    ≡⟨ Drop-ext (Drop*• ξ1 ξ2 n) x ⟩
  Drop (Drop* (ξ1 • ξ2) n) x ∎

Keep•Drop : (ξ1 ξ2 : Ren) → Keep ξ1 • Drop ξ2 ≗ Drop (ξ1 • ξ2)
Keep•Drop ξ1 ξ2 zero = refl
Keep•Drop ξ1 ξ2 (suc x) = refl

Keep*•Drop* : (ξ1 ξ2 : Ren) (n : ℕ) → Keep* ξ1 n • Drop* ξ2 n ≗ Drop* (ξ1 • ξ2) n
Keep*•Drop* ξ1 ξ2 zero = ≗-refl
Keep*•Drop* ξ1 ξ2 (suc n) x = 
  (Keep (Keep* ξ1 n) • Drop (Drop* ξ2 n)) x
    ≡⟨ Keep•Drop (Keep* ξ1 n) (Drop* ξ2 n) x ⟩
  Drop (Keep* ξ1 n • Drop* ξ2 n) x
    ≡⟨ Drop-ext (Keep*•Drop* ξ1 ξ2 n) x ⟩
  Drop (Drop* (ξ1 • ξ2) n) x ∎

---------------------------------
-- ORDER-PRESERVING EMBEDDINGS --
---------------------------------

-- Order-preserving embeddings (OPEs)
data OPE (ξ : Ren) : Set where
  IdOPE≗ : (ξ≗id : ξ ≗ id) → OPE ξ
  KeepOPE≗ : ∀{ξ'} (ξ≗Keep : ξ ≗ Keep ξ') (ξ'-OPE : OPE ξ') → OPE ξ
  DropOPE≗ : ∀{ξ'} (ξ≗Drop : ξ ≗ Drop ξ') (ξ'-OPE : OPE ξ') → OPE ξ

IdOPE : OPE id
IdOPE = IdOPE≗ ≗-refl

KeepOPE : ∀{ξ} → OPE ξ → OPE (Keep ξ)
KeepOPE ξ-OPE = KeepOPE≗ ≗-refl ξ-OPE

DropOPE : ∀{ξ} → OPE ξ → OPE (Drop ξ)
DropOPE ξ-OPE = DropOPE≗ ≗-refl ξ-OPE

-- The property of being an OPE is extensional
OPE-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → OPE ξ1 → OPE ξ2
OPE-ext ξ1≗ξ2 (IdOPE≗ ξ≗id) =
  IdOPE≗ λ x → sym (ξ1≗ξ2 x) ∙ ξ≗id x
OPE-ext ξ1≗ξ2 (KeepOPE≗ ξ≗Keep ξ'-OPE) =
  KeepOPE≗ (λ x → sym (ξ1≗ξ2 x) ∙ ξ≗Keep x) ξ'-OPE
OPE-ext ξ1≗ξ2 (DropOPE≗ ξ≗Drop ξ'-OPE) =
  DropOPE≗ (λ x → sym (ξ1≗ξ2 x) ∙ ξ≗Drop x) ξ'-OPE

-- OPEs are injective
OPE-inj : ∀{ξ} → OPE ξ → Injective _≡_ _≡_ ξ
OPE-inj (IdOPE≗ ξ≗id) {x} {y} p = sym (ξ≗id x) ∙ p ∙ ξ≗id y
OPE-inj (KeepOPE≗ ξ≗Keep ξ'-OPE) {zero} {zero} p = refl
OPE-inj (KeepOPE≗ ξ≗Keep ξ'-OPE) {zero} {suc y} p =
  ⊥-elim $ 0≢1+n $ sym (ξ≗Keep zero) ∙ p ∙ ξ≗Keep (suc y)
OPE-inj (KeepOPE≗ ξ≗Keep ξ'-OPE) {suc x} {zero} p =
  ⊥-elim $ 1+n≢0 $ sym (ξ≗Keep (suc x)) ∙ p ∙ ξ≗Keep zero
OPE-inj (KeepOPE≗ ξ≗Keep ξ'-OPE) {suc x} {suc y} p =
  cong suc $ OPE-inj ξ'-OPE {x} {y} $
    suc-injective $ sym (ξ≗Keep (suc x)) ∙ p ∙ ξ≗Keep (suc y)
OPE-inj (DropOPE≗ ξ≗Drop ξ'-OPE) {x} {y} p =
  OPE-inj ξ'-OPE {x} {y} $
    suc-injective $ sym (ξ≗Drop x) ∙ p ∙ ξ≗Drop y

-- OPEs are order-preserving
OPE-pres-≤ : ∀{ξ} → OPE ξ → {x y : ℕ} → x ≤ y → ξ x ≤ ξ y
OPE-pres-≤ (IdOPE≗ ξ≗id) {x} {y} x≤y =
  subst₂ _≤_ (sym (ξ≗id x)) (sym (ξ≗id y)) x≤y
OPE-pres-≤ {ξ} (KeepOPE≗ ξ≗Keep ξ-OPE) {zero} {y} z≤n =
  subst (_≤ ξ y) (sym (ξ≗Keep zero)) z≤n
OPE-pres-≤ (KeepOPE≗ ξ≗Keep ξ-OPE) {suc x} {suc y} (s≤s x≤y) =
  subst₂ _≤_ (sym $ ξ≗Keep (suc x)) (sym $ ξ≗Keep (suc y))
    (s≤s $ OPE-pres-≤ ξ-OPE x≤y)
OPE-pres-≤ (DropOPE≗ ξ≗Drop ξ-OPE) {x} {y} x≤y =
  subst₂ _≤_ (sym $ ξ≗Drop x) (sym $ ξ≗Drop y)
    (s≤s $ OPE-pres-≤ ξ-OPE x≤y)

-- OPEs are order-reflecting
OPE-refl-≤ : ∀{ξ} → OPE ξ → {x y : ℕ} → ξ x ≤ ξ y → x ≤ y
OPE-refl-≤ (IdOPE≗ ξ≗id) {x} {y} ξx≤ξy =
  subst₂ _≤_ (ξ≗id x) (ξ≗id y) ξx≤ξy
OPE-refl-≤ (KeepOPE≗ ξ≗Keep ξ-OPE) {zero} {zero} ξx≤ξy = z≤n
OPE-refl-≤ (KeepOPE≗ ξ≗Keep ξ-OPE) {zero} {suc y} ξx≤ξy = z≤n
OPE-refl-≤ (KeepOPE≗ ξ≗Keep ξ-OPE) {suc x} {zero} ξx≤ξy =
  ⊥-elim $ 1+n≢0 $ n≤0⇒n≡0 $
  subst₂ _≤_ (ξ≗Keep (suc x)) (ξ≗Keep zero) ξx≤ξy
OPE-refl-≤ (KeepOPE≗ ξ≗Keep ξ-OPE) {suc x} {suc y} ξx≤ξy
  with subst₂ _≤_ (ξ≗Keep (suc x)) (ξ≗Keep (suc y)) ξx≤ξy
... | s≤s ξ'x≤ξ'y = s≤s $ OPE-refl-≤ ξ-OPE ξ'x≤ξ'y
OPE-refl-≤ (DropOPE≗ ξ≗Drop ξ-OPE) {x} {y} ξx≤ξy
  with subst₂ _≤_ (ξ≗Drop x) (ξ≗Drop y) ξx≤ξy
... | s≤s ξ'x≤ξ'y = OPE-refl-≤ ξ-OPE ξ'x≤ξ'y