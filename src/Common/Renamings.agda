{-# OPTIONS --safe #-}

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

Drop-inj : Injective _≗_ _≗_ Drop
Drop-inj p x = suc-injective (p x)

Drop-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → Drop ξ1 ≗ Drop ξ2
Drop-ext p x = cong suc (p x)

Drop* : Ren → ℕ → Ren
Drop* ξ zero = ξ
Drop* ξ (suc k) = Drop (Drop* ξ k)

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
