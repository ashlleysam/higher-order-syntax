{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
open import Data.Unit
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import KindSignatures

-- Untyped and possibly ill-scoped representations of types
module Types (⅀ : KindSignature) where

open KindSignature ⅀

---------------
-- RAW TYPES --
---------------

data Ty : Set
data TyVec : Set

-- Raw types
data Ty where
  tyVar : ℕ → Ty
  tyConstr : (s : ⅀ .TySymb) (ts : TyVec) → Ty

infixr 5 _∷_
-- Lists of raw terms
data TyVec where
  [] : TyVec
  _∷_ : (tk : Ty × ℕ) →
        (ts : TyVec) →
        TyVec

tyCons : Ty → ℕ → TyVec → TyVec
tyCons e k es = (e , k) ∷ es

----------------------
-- BASIC PROPERTIES --
----------------------

-- Injectivity of constructors
tyVar-inj : Injective _≡_ _≡_ tyVar
tyVar-inj refl = refl

tyConstr-inj : ∀{s1 s2 es1 es2} →
              _≡_ {A = Ty} (tyConstr s1 es1) (tyConstr s2 es2) →
              s1 ≡ s2 × es1 ≡ es2
tyConstr-inj refl = refl , refl

tyCons-inj : ∀{e1 e2 k1 k2 es1 es2} →
              _≡_ {A = TyVec} ((e1 , k1) ∷ es1) ((e2 , k2) ∷ es2) →
              e1 ≡ e2 × k1 ≡ k2 × es1 ≡ es2
tyCons-inj refl = refl , refl , refl

--------------
-- RENAMING --
--------------

renTy : Ren → Ty → Ty
renTyVec : Ren → TyVec → TyVec

renTy ξ (tyVar x) = tyVar (ξ x)
renTy ξ (tyConstr s es) = tyConstr s (renTyVec ξ es)

renTyVec ξ [] = []
renTyVec ξ ((e , k) ∷ es) = (renTy (Keep* ξ k) e , k) ∷ renTyVec ξ es

renTy-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renTy ξ1 ≗ renTy ξ2
renTyVec-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renTyVec ξ1 ≗ renTyVec ξ2

renTy-ext p (tyVar x) = cong tyVar (p x)
renTy-ext p (tyConstr s es) = cong (tyConstr s) (renTyVec-ext p es)

renTyVec-ext p [] = refl
renTyVec-ext p ((e , k) ∷ es) =
  cong₃ tyCons
    (renTy-ext (Keep*-ext p k) e)
    refl
    (renTyVec-ext p es)

renTy-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (renTy ξ)
renTyVec-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (renTyVec ξ)

renTy-inj ξ-inj {x = tyVar x1} {y = tyVar x2} p = cong tyVar (ξ-inj (tyVar-inj p))
renTy-inj ξ-inj {x = tyConstr s1 es1} {y = tyConstr s2 es2} p with tyConstr-inj p
... | (q , r) = cong₂ tyConstr q (renTyVec-inj ξ-inj r)

renTyVec-inj ξ-inj {x = []} {y = []} p = refl
renTyVec-inj ξ-inj {x = (e1 , k1) ∷ es1} {y = (e2 , k2) ∷ es2} p with tyCons-inj p
... | (q , refl , r) =
  cong₃ tyCons
    (renTy-inj (Keep*-inj ξ-inj k1) q)
    refl
    (renTyVec-inj ξ-inj r)

renTy-≈Id : ∀{ξ} → ξ ≗ id → renTy ξ ≗ id
renTyVec-≈Id : ∀{ξ} → ξ ≗ id → renTyVec ξ ≗ id

renTy-≈Id p (tyVar x) = cong tyVar (p x)
renTy-≈Id p (tyConstr s es) = cong (tyConstr s) (renTyVec-≈Id p es)

renTyVec-≈Id p [] = refl
renTyVec-≈Id p ((e , k) ∷ es) =
  cong₃ tyCons
    (renTy-≈Id (λ x → Keep*-ext p k x ∙ Keep*-id k x) e)
    refl
    (renTyVec-≈Id p es)

renTyId : renTy id ≗ id
renTyId e = renTy-≈Id ≗-refl e

renTyVecId : renTyVec id ≗ id
renTyVecId es = renTyVec-≈Id ≗-refl es

renTy• : (ξ1 ξ2 : Ren) → renTy ξ1 ∘ renTy ξ2 ≗ renTy (ξ1 • ξ2)
renTyVec• : (ξ1 ξ2 : Ren) → renTyVec ξ1 ∘ renTyVec ξ2 ≗ renTyVec (ξ1 • ξ2)

renTy• ξ1 ξ2 (tyVar x) = refl
renTy• ξ1 ξ2 (tyConstr s es) = cong (tyConstr s) $ renTyVec• ξ1 ξ2 es

renTyVec• ξ1 ξ2 [] = refl
renTyVec• ξ1 ξ2 ((e , k) ∷ es) =
  cong₃ tyCons
    (renTy (Keep* ξ1 k) (renTy (Keep* ξ2 k) e)
      ≡⟨ renTy• (Keep* ξ1 k) (Keep* ξ2 k) e ⟩
    renTy (Keep* ξ1 k • Keep* ξ2 k) e
      ≡⟨ renTy-ext (Keep*•Keep* ξ1 ξ2 k) e ⟩
    renTy (Keep* (ξ1 • ξ2) k) e ∎)
    refl
    (renTyVec• ξ1 ξ2 es)

------------------
-- SUBSTITUTION --
------------------

TySub : Set
TySub = ℕ → Ty

ιₜ : Ren → TySub
ιₜ ξ x = tyVar (ξ x)

ιₜ-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → ιₜ ξ1 ≗ ιₜ ξ2
ιₜ-ext p x = cong tyVar (p x)

ιₜId : ∀{ξ} → ξ ≗ id → ιₜ ξ ≗ tyVar
ιₜId p x = cong tyVar (p x)

_▸ₜ_ : TySub → Ty → TySub
(σ ▸ₜ e) zero = e
(σ ▸ₜ e) (suc x) = σ x

addTySub = _▸ₜ_

▸ₜ-inj : ∀{σ1 σ2 e1 e2} → σ1 ▸ₜ e1 ≗ σ2 ▸ₜ e2 → σ1 ≗ σ2 × e1 ≡ e2
▸ₜ-inj p = p ∘ suc , p zero

▸ₜ-ext : ∀{σ1 σ2 e1 e2} → σ1 ≗ σ2 → e1 ≡ e2 → σ1 ▸ₜ e1 ≗ σ2 ▸ₜ e2
▸ₜ-ext p q zero = q
▸ₜ-ext p q (suc x) = p x

infixr 9 _•◦ₜ_
_•◦ₜ_ : Ren → TySub → TySub
(ξ •◦ₜ σ) x = renTy ξ (σ x)

•◦ₜ-ext : ∀{ξ1 ξ2 σ1 σ2} →
          ξ1 ≗ ξ2 →
          σ1 ≗ σ2 →
          (ξ1 •◦ₜ σ1) ≗ (ξ2 •◦ₜ σ2)
•◦ₜ-ext {ξ1} {ξ2} {σ1} {σ2} p q x =
  renTy ξ1 (σ1 x)
    ≡⟨ renTy-ext p (σ1 x) ⟩
  renTy ξ2 (σ1 x)
    ≡⟨ cong (renTy ξ2) (q x) ⟩
  renTy ξ2 (σ2 x) ∎

••◦ₜ : (ξ1 ξ2 : Ren) (σ : TySub) →
       (ξ1 • ξ2) •◦ₜ σ ≗ ξ1 •◦ₜ (ξ2 •◦ₜ σ)
••◦ₜ ξ1 ξ2 σ x = sym $ renTy• ξ1 ξ2 (σ x)

Id•◦ₜ : (σ : TySub) → id •◦ₜ σ ≗ σ
Id•◦ₜ σ x = renTyId (σ x)

•◦ₜId : (ξ : Ren) → ξ •◦ₜ tyVar ≗ ιₜ ξ
•◦ₜId ξ x = refl

•◦ₜ-▸ₜ : (ξ : Ren) (σ : TySub) (e : Ty) →
          (ξ •◦ₜ (σ ▸ₜ e)) ≗ (ξ •◦ₜ σ) ▸ₜ renTy ξ e
•◦ₜ-▸ₜ ξ σ e zero = refl
•◦ₜ-▸ₜ ξ σ e (suc x) = refl     

TyIgnoreSub : TySub → TySub
TyIgnoreSub σ = σ ▸ₜ tyVar zero

TyDropSub : TySub → TySub
TyDropSub σ = Drop id •◦ₜ σ

TyDropSub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → TyDropSub σ1 ≗ TyDropSub σ2
TyDropSub-ext p = •◦ₜ-ext ≗-refl p

TyDropSub* : TySub → ℕ → TySub
TyDropSub* σ zero = σ
TyDropSub* σ (suc k) = TyDropSub (TyDropSub* σ k)

TyDropSub*-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → (n : ℕ) → TyDropSub* σ1 n ≗ TyDropSub* σ2 n
TyDropSub*-ext p zero = p
TyDropSub*-ext p (suc n) = TyDropSub-ext (TyDropSub*-ext p n)

TyKeepSub : TySub → TySub
TyKeepSub σ = TyDropSub σ ▸ₜ tyVar zero

TyKeepSub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → TyKeepSub σ1 ≗ TyKeepSub σ2
TyKeepSub-ext p = ▸ₜ-ext (TyDropSub-ext p) refl

TyKeepSub-id : TyKeepSub tyVar ≗ tyVar
TyKeepSub-id zero = refl
TyKeepSub-id (suc x) = refl

TyKeepSub* : TySub → ℕ → TySub
TyKeepSub* σ zero = σ
TyKeepSub* σ (suc k) = TyKeepSub (TyKeepSub* σ k)

TyKeepSub*-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → (n : ℕ) → TyKeepSub* σ1 n ≗ TyKeepSub* σ2 n
TyKeepSub*-ext p zero = p
TyKeepSub*-ext p (suc n) = TyKeepSub-ext (TyKeepSub*-ext p n)

TyKeepSub*-id : (n : ℕ) → TyKeepSub* tyVar n ≗ tyVar
TyKeepSub*-id zero = ≗-refl
TyKeepSub*-id (suc n) x = TyKeepSub-ext (TyKeepSub*-id n) x ∙ TyKeepSub-id x

Keep•◦ₜDrop : (ξ : Ren) (σ : TySub) → Keep ξ •◦ₜ TyDropSub σ ≗ TyDropSub (ξ •◦ₜ σ)
Keep•◦ₜDrop ξ σ x =
  renTy (Keep ξ) (renTy suc (σ x))
    ≡⟨ renTy• (Keep ξ) suc (σ x) ⟩
  renTy (suc ∘ ξ) (σ x)
    ≡⟨ (sym $ renTy• suc ξ (σ x)) ⟩
  renTy suc (renTy ξ (σ x)) ∎

Keep*•◦ₜDrop* : (ξ : Ren) (σ : TySub) (n : ℕ) →
                Keep* ξ n •◦ₜ TyDropSub* σ n ≗ TyDropSub* (ξ •◦ₜ σ) n
Keep*•◦ₜDrop* ξ σ zero = ≗-refl
Keep*•◦ₜDrop* ξ σ (suc n) x = 
  (Keep (Keep* ξ n) •◦ₜ TyDropSub (TyDropSub* σ n)) x
    ≡⟨ Keep•◦ₜDrop (Keep* ξ n) (TyDropSub* σ n) x ⟩
  TyDropSub (Keep* ξ n •◦ₜ TyDropSub* σ n) x
    ≡⟨ TyDropSub-ext (Keep*•◦ₜDrop* ξ σ n) x ⟩
  TyDropSub (TyDropSub* (ξ •◦ₜ σ) n) x ∎

Keep•◦ₜKeep : (ξ : Ren) (σ : TySub) → Keep ξ •◦ₜ TyKeepSub σ ≗ TyKeepSub (ξ •◦ₜ σ)
Keep•◦ₜKeep ξ σ zero = refl
Keep•◦ₜKeep ξ σ (suc x) = Keep•◦ₜDrop ξ σ x

Keep*•◦ₜKeep* : (ξ : Ren) (σ : TySub) (n : ℕ) →
                Keep* ξ n •◦ₜ TyKeepSub* σ n ≗ TyKeepSub* (ξ •◦ₜ σ) n
Keep*•◦ₜKeep* ξ σ zero = ≗-refl
Keep*•◦ₜKeep* ξ σ (suc n) x = 
  (Keep (Keep* ξ n) •◦ₜ TyKeepSub (TyKeepSub* σ n)) x
    ≡⟨ Keep•◦ₜKeep (Keep* ξ n) (TyKeepSub* σ n) x ⟩
  TyKeepSub (Keep* ξ n •◦ₜ TyKeepSub* σ n) x
    ≡⟨ TyKeepSub-ext (Keep*•◦ₜKeep* ξ σ n) x ⟩
  TyKeepSub (TyKeepSub* (ξ •◦ₜ σ) n) x ∎

Keepιₜ : (ξ : Ren) → ιₜ (Keep ξ) ≗ TyKeepSub (ιₜ ξ)
Keepιₜ ξ zero = refl
Keepιₜ ξ (suc x) = refl

Dropιₜ : (ξ : Ren) → ιₜ (Drop ξ) ≗ TyDropSub (ιₜ ξ)
Dropιₜ ξ x = refl

Keep*ιₜ : (ξ : Ren) (n : ℕ) → ιₜ (Keep* ξ n) ≗ TyKeepSub* (ιₜ ξ) n
Keep*ιₜ ξ zero = ≗-refl
Keep*ιₜ ξ (suc n) x =
  ιₜ (Keep (Keep* ξ n)) x
    ≡⟨ Keepιₜ (Keep* ξ n) x ⟩
  TyKeepSub (ιₜ (Keep* ξ n)) x
    ≡⟨ TyKeepSub-ext (Keep*ιₜ ξ n) x ⟩
  TyKeepSub (TyKeepSub* (ιₜ ξ) n) x ∎

Drop*ιₜ : (ξ : Ren) (n : ℕ) → ιₜ (Drop* ξ n) ≗ TyDropSub* (ιₜ ξ) n
Drop*ιₜ ξ zero = ≗-refl
Drop*ιₜ ξ (suc n) x =
  ιₜ (Drop (Drop* ξ n)) x
    ≡⟨ Dropιₜ (Drop* ξ n) x ⟩
  TyDropSub (ιₜ (Drop* ξ n)) x
    ≡⟨ TyDropSub-ext (Drop*ιₜ ξ n) x ⟩
  TyDropSub (TyDropSub* (ιₜ ξ) n) x ∎

subTy : TySub → Ty → Ty
subTyVec : TySub → TyVec → TyVec

subTy σ (tyVar x) = σ x
subTy σ (tyConstr s es) = tyConstr s (subTyVec σ es)

subTyVec σ [] = []
subTyVec σ ((e , k) ∷ es) = (subTy (TyKeepSub* σ k) e , k) ∷ subTyVec σ es

subTy-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subTy σ1 ≗ subTy σ2
subTyVec-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subTyVec σ1 ≗ subTyVec σ2

subTy-ext p (tyVar x) = p x
subTy-ext p (tyConstr s es) = cong (tyConstr s) (subTyVec-ext p es)

subTyVec-ext p [] = refl
subTyVec-ext p ((e , k) ∷ es) =
  cong₃ tyCons
    (subTy-ext (TyKeepSub*-ext p k) e)
    refl
    (subTyVec-ext p es)

subTy-≈Id : ∀{σ} → σ ≗ tyVar → subTy σ ≗ id
subTyVec-≈Id : ∀{σ} → σ ≗ tyVar → subTyVec σ ≗ id

subTy-≈Id p (tyVar x) = p x
subTy-≈Id p (tyConstr s es) = cong (tyConstr s) (subTyVec-≈Id p es)

subTyVec-≈Id p [] = refl
subTyVec-≈Id p ((e , k) ∷ es) =
  cong₃ tyCons
    (subTy-≈Id (λ x → TyKeepSub*-ext p k x ∙ TyKeepSub*-id k x) e)
    refl
    (subTyVec-≈Id p es)

subTyId : subTy tyVar ≗ id
subTyId = subTy-≈Id ≗-refl

subTyVecId : subTyVec tyVar ≗ id
subTyVecId = subTyVec-≈Id ≗-refl

subTy•◦ₜ : (ξ : Ren) (σ : TySub) → renTy ξ ∘ subTy σ ≗ subTy (ξ •◦ₜ σ)
subTyVec•◦ₜ : (ξ : Ren) (σ : TySub) → renTyVec ξ ∘ subTyVec σ ≗ subTyVec (ξ •◦ₜ σ)

subTy•◦ₜ ξ σ (tyVar x) = refl
subTy•◦ₜ ξ σ (tyConstr s es) = cong (tyConstr s) (subTyVec•◦ₜ ξ σ es)

subTyVec•◦ₜ ξ σ [] = refl
subTyVec•◦ₜ ξ σ ((e , k) ∷ es) =
  cong₃ tyCons
    (renTy (Keep* ξ k) (subTy (TyKeepSub* σ k) e)
      ≡⟨ subTy•◦ₜ (Keep* ξ k) (TyKeepSub* σ k) e ⟩
    subTy (Keep* ξ k •◦ₜ TyKeepSub* σ k) e
      ≡⟨ subTy-ext (Keep*•◦ₜKeep* ξ σ k) e ⟩
    subTy (TyKeepSub* (ξ •◦ₜ σ) k) e ∎)
    refl
    (subTyVec•◦ₜ ξ σ es)

infixr 9 _◦•ₜ_
_◦•ₜ_ : TySub → Ren → TySub
(σ ◦•ₜ ξ) x = σ (ξ x)

Keep◦•ₜDrop : (σ : TySub) (ξ : Ren) → TyKeepSub σ ◦•ₜ Drop ξ ≗ TyDropSub (σ ◦•ₜ ξ)
Keep◦•ₜDrop σ ξ x = refl

Keep*◦•ₜDrop* : (σ : TySub) (ξ : Ren) (n : ℕ) →
                TyKeepSub* σ n ◦•ₜ Drop* ξ n ≗ TyDropSub* (σ ◦•ₜ ξ) n
Keep*◦•ₜDrop* σ ξ zero = ≗-refl
Keep*◦•ₜDrop* σ ξ (suc n) x = 
  (TyKeepSub (TyKeepSub* σ n) ◦•ₜ Drop (Drop* ξ n)) x
    ≡⟨ Keep◦•ₜDrop (TyKeepSub* σ n) (Drop* ξ n) x ⟩
  TyDropSub (TyKeepSub* σ n ◦•ₜ Drop* ξ n) x
    ≡⟨ TyDropSub-ext (Keep*◦•ₜDrop* σ ξ n) x ⟩
  TyDropSub (TyDropSub* (σ ◦•ₜ ξ) n) x ∎

Keep◦•ₜKeep : (σ : TySub) (ξ : Ren) → TyKeepSub σ ◦•ₜ Keep ξ ≗ TyKeepSub (σ ◦•ₜ ξ)
Keep◦•ₜKeep σ ξ zero = refl
Keep◦•ₜKeep σ ξ (suc x) = Keep◦•ₜDrop σ ξ x

Keep*◦•ₜKeep* : (σ : TySub) (ξ : Ren) (n : ℕ) →
                TyKeepSub* σ n ◦•ₜ Keep* ξ n ≗ TyKeepSub* (σ ◦•ₜ ξ) n
Keep*◦•ₜKeep* σ ξ zero = ≗-refl
Keep*◦•ₜKeep* σ ξ (suc n) x = 
  (TyKeepSub (TyKeepSub* σ n) ◦•ₜ Keep (Keep* ξ n)) x
    ≡⟨ Keep◦•ₜKeep (TyKeepSub* σ n) (Keep* ξ n) x ⟩
  TyKeepSub (TyKeepSub* σ n ◦•ₜ Keep* ξ n) x
    ≡⟨ TyKeepSub-ext (Keep*◦•ₜKeep* σ ξ n) x ⟩
  TyKeepSub (TyKeepSub* (σ ◦•ₜ ξ) n) x ∎

Id◦•ₜ : (ξ : Ren) → tyVar ◦•ₜ ξ ≗ ιₜ ξ
Id◦•ₜ ξ x = refl

◦•ₜId : (σ : TySub) → σ ◦•ₜ id ≗ σ
◦•ₜId σ x = refl

subTy◦•ₜ : (σ : TySub) (ξ : Ren) → subTy σ ∘ renTy ξ ≗ subTy (σ ◦•ₜ ξ)
subTyVec◦•ₜ : (σ : TySub) (ξ : Ren) → subTyVec σ ∘ renTyVec ξ ≗ subTyVec (σ ◦•ₜ ξ)

subTy◦•ₜ σ ξ (tyVar x) = refl
subTy◦•ₜ σ ξ (tyConstr s es) = cong (tyConstr s) (subTyVec◦•ₜ σ ξ es)

subTyVec◦•ₜ σ ξ [] = refl
subTyVec◦•ₜ σ ξ ((e , k) ∷ es) =
  cong₃ tyCons
    (subTy (TyKeepSub* σ k) (renTy (Keep* ξ k) e)
      ≡⟨ subTy◦•ₜ (TyKeepSub* σ k) (Keep* ξ k) e ⟩
    subTy (TyKeepSub* σ k ◦•ₜ Keep* ξ k) e
      ≡⟨ subTy-ext (λ x → Keep*◦•ₜKeep* σ ξ k x) e ⟩
    subTy (TyKeepSub* (σ ◦•ₜ ξ) k) e ∎)
    refl
    (subTyVec◦•ₜ σ ξ es)

infixr 9 _◦ₜ_ 
_◦ₜ_ : TySub → TySub → TySub
(σ1 ◦ₜ σ2) x = subTy σ1 (σ2 x)

◦ₜ-ext : ∀{σ1 σ1' σ2 σ2'} →
          σ1 ≗ σ1' → σ2 ≗ σ2' →
          σ1 ◦ₜ σ2 ≗ σ1' ◦ₜ σ2'
◦ₜ-ext {σ1} {σ1'} {σ2} {σ2'} p q x =
  subTy σ1 (σ2 x)
    ≡⟨ subTy-ext p (σ2 x) ⟩
  subTy σ1' (σ2 x)
    ≡⟨ cong (subTy σ1') (q x) ⟩
  subTy σ1' (σ2' x) ∎

◦ₜ-▸ₜ : (σ1 σ2 : TySub) (e : Ty) →
        σ1 ◦ₜ (σ2 ▸ₜ e) ≗ (σ1 ◦ₜ σ2) ▸ₜ subTy σ1 e
◦ₜ-▸ₜ σ1 σ2 e zero = refl
◦ₜ-▸ₜ σ1 σ2 e (suc x) = refl

Keep◦ₜKeep : (σ1 σ2 : TySub) → TyKeepSub σ1 ◦ₜ TyKeepSub σ2 ≗ TyKeepSub (σ1 ◦ₜ σ2)
Keep◦ₜKeep σ1 σ2 zero = refl
Keep◦ₜKeep σ1 σ2 (suc x) =
  subTy (TyKeepSub σ1) (renTy suc (σ2 x))
    ≡⟨ subTy◦•ₜ (TyKeepSub σ1) suc (σ2 x) ⟩
  subTy (renTy suc ∘ σ1) (σ2 x)
    ≡⟨ sym $ subTy•◦ₜ suc σ1 (σ2 x) ⟩
  renTy suc (subTy σ1 (σ2 x)) ∎

Keep*◦ₜKeep* : (σ1 σ2 : TySub) (n : ℕ) →
               TyKeepSub* σ1 n ◦ₜ TyKeepSub* σ2 n ≗ TyKeepSub* (σ1 ◦ₜ σ2) n
Keep*◦ₜKeep* σ1 σ2 zero = ≗-refl
Keep*◦ₜKeep* σ1 σ2 (suc n) x =
  (TyKeepSub (TyKeepSub* σ1 n) ◦ₜ TyKeepSub (TyKeepSub* σ2 n)) x
    ≡⟨ Keep◦ₜKeep (TyKeepSub* σ1 n) (TyKeepSub* σ2 n) x ⟩
  TyKeepSub (TyKeepSub* σ1 n ◦ₜ TyKeepSub* σ2 n) x
    ≡⟨ TyKeepSub-ext (Keep*◦ₜKeep* σ1 σ2 n) x ⟩
  TyKeepSub (TyKeepSub* (σ1 ◦ₜ σ2) n) x ∎

Id◦ₜ : (σ : TySub) → tyVar ◦ₜ σ ≗ σ
Id◦ₜ σ x = subTyId (σ x)

◦ₜId : (σ : TySub) → σ ◦ₜ tyVar ≗ σ
◦ₜId σ x = refl

subTy◦ₜ : (σ1 σ2 : TySub) → subTy σ1 ∘ subTy σ2 ≗ subTy (σ1 ◦ₜ σ2)
subTyVec◦ₜ : (σ1 σ2 : TySub) → subTyVec σ1 ∘ subTyVec σ2 ≗ subTyVec (σ1 ◦ₜ σ2)

subTy◦ₜ σ1 σ2 (tyVar x) = refl
subTy◦ₜ σ1 σ2 (tyConstr s es) = cong (tyConstr s) (subTyVec◦ₜ σ1 σ2 es)

subTyVec◦ₜ σ1 σ2 [] = refl 
subTyVec◦ₜ σ1 σ2 ((e , k) ∷ es) =
  cong₃ tyCons
    (subTy (TyKeepSub* σ1 k) (subTy (TyKeepSub* σ2 k) e)
      ≡⟨ subTy◦ₜ (TyKeepSub* σ1 k) (TyKeepSub* σ2 k) e ⟩
    subTy (TyKeepSub* σ1 k ◦ₜ TyKeepSub* σ2 k) e
      ≡⟨ subTy-ext (λ x → Keep*◦ₜKeep* σ1 σ2 k x) e ⟩
    subTy (TyKeepSub* (σ1 ◦ₜ σ2) k) e ∎)
    refl        
    (subTyVec◦ₜ σ1 σ2 es)

subTyιₜ : (ξ : Ren) → subTy (ιₜ ξ) ≗ renTy ξ
subTyVecιₜ : (ξ : Ren) → subTyVec (ιₜ ξ) ≗ renTyVec ξ

subTyιₜ ξ (tyVar x) = refl
subTyιₜ ξ (tyConstr s es) = cong (tyConstr s) (subTyVecιₜ ξ es)

subTyVecιₜ ξ [] = refl 
subTyVecιₜ ξ ((e , k) ∷ es) =
  cong₃ tyCons
    (subTy (TyKeepSub* (ιₜ ξ) k) e
      ≡⟨ (sym $ subTy-ext (Keep*ιₜ ξ k) e) ⟩
    subTy (ιₜ (Keep* ξ k)) e
      ≡⟨ subTyιₜ (Keep* ξ k) e ⟩
    renTy (Keep* ξ k) e ∎)
    refl
    (subTyVecιₜ ξ es)

◦•◦ₜ : (σ1 : TySub) (ξ : Ren) (σ2 : TySub) →
       (σ1 ◦•ₜ ξ) ◦ₜ σ2 ≗ σ1 ◦ₜ (ξ •◦ₜ σ2)
◦•◦ₜ σ1 ξ σ2 x = sym $ subTy◦•ₜ σ1 ξ (σ2 x)

Drop◦ₜ : (σ1 σ2 : TySub) → TyDropSub σ1 ◦ₜ σ2 ≗ TyDropSub (σ1 ◦ₜ σ2)
Drop◦ₜ σ1 σ2 x = sym $ subTy•◦ₜ suc σ1 (σ2 x)

Drop*◦ₜ : (σ1 σ2 : TySub) (n : ℕ) → TyDropSub* σ1 n ◦ₜ σ2 ≗ TyDropSub* (σ1 ◦ₜ σ2) n
Drop*◦ₜ σ1 σ2 zero = ≗-refl
Drop*◦ₜ σ1 σ2 (suc n) x =
  (TyDropSub (TyDropSub* σ1 n) ◦ₜ σ2) x
    ≡⟨ Drop◦ₜ (TyDropSub* σ1 n) σ2 x ⟩
  TyDropSub (TyDropSub* σ1 n ◦ₜ σ2) x
    ≡⟨ TyDropSub-ext (Drop*◦ₜ σ1 σ2 n) x ⟩
  TyDropSub (TyDropSub* (σ1 ◦ₜ σ2) n) x ∎

Keep◦ₜDrop : (σ1 σ2 : TySub) → TyKeepSub σ1 ◦ₜ TyDropSub σ2 ≗ TyDropSub (σ1 ◦ₜ σ2)
Keep◦ₜDrop σ1 σ2 x =
  (TyKeepSub σ1 ◦ₜ Drop id •◦ₜ σ2) x
    ≡⟨ (sym $ ◦•◦ₜ (TyKeepSub σ1) (Drop id) σ2 x) ⟩
  (TyDropSub σ1 ◦ₜ σ2) x
    ≡⟨ Drop◦ₜ σ1 σ2 x ⟩
  TyDropSub (σ1 ◦ₜ σ2) x ∎

Keep*◦ₜDrop* : (σ1 σ2 : TySub) (n : ℕ) → TyKeepSub* σ1 n ◦ₜ TyDropSub* σ2 n ≗ TyDropSub* (σ1 ◦ₜ σ2) n
Keep*◦ₜDrop* σ1 σ2 zero = ≗-refl
Keep*◦ₜDrop* σ1 σ2 (suc n) x =
  (TyKeepSub (TyKeepSub* σ1 n) ◦ₜ TyDropSub (TyDropSub* σ2 n)) x
    ≡⟨ Keep◦ₜDrop (TyKeepSub* σ1 n) (TyDropSub* σ2 n) x ⟩
  TyDropSub (TyKeepSub* σ1 n ◦ₜ TyDropSub* σ2 n) x
    ≡⟨ TyDropSub-ext (Keep*◦ₜDrop* σ1 σ2 n) x ⟩
  TyDropSub (TyDropSub* (σ1 ◦ₜ σ2) n) x ∎

▸ₜ-◦ₜ-Drop : (σ1 : TySub) (e : Ty) (σ2 : TySub) →
             (σ1 ▸ₜ e) ◦ₜ TyDropSub σ2 ≗ σ1 ◦ₜ σ2
▸ₜ-◦ₜ-Drop σ1 e σ2 x = subTy◦•ₜ (σ1 ▸ₜ e) suc (σ2 x)

▸ₜ-◦ₜ-Keep : (σ1 : TySub) (e : Ty) (σ2 : TySub) →
             (σ1 ▸ₜ e) ◦ₜ TyKeepSub σ2 ≗ (σ1 ◦ₜ σ2) ▸ₜ e
▸ₜ-◦ₜ-Keep σ1 e σ2 zero = refl  
▸ₜ-◦ₜ-Keep σ1 e σ2 (suc x) = ▸ₜ-◦ₜ-Drop σ1 e σ2 x

Drop*-id•◦≗DropSub* :
  (σ : TySub) (n : ℕ) →
  Drop* id n •◦ₜ σ ≗ TyDropSub* σ n
Drop*-id•◦≗DropSub* σ zero x = renTyId (σ x)
Drop*-id•◦≗DropSub* σ (suc n) x =
  renTy (suc ∘ Drop* id n) (σ x)
    ≡⟨ (sym $ renTy• suc (Drop* id n) (σ x)) ⟩
  renTy suc (renTy (Drop* id n) (σ x))
    ≡⟨ cong (renTy suc) (Drop*-id•◦≗DropSub* σ n x) ⟩
  renTy suc (TyDropSub* σ n x) ∎

-- Whether a variable occurs free in a type
notFreeInTy : ℕ → Ty → Set
notFreeInTyVec : ℕ → TyVec → Set

notFreeInTy x (tyVar y) = x ≢ y
notFreeInTy x (tyConstr s ts) = notFreeInTyVec x ts

notFreeInTyVec x [] = ⊤
notFreeInTyVec x ((t , k) ∷ ts) =
  notFreeInTy (k + x) t × notFreeInTyVec x ts

?notFreeInTy : (x : ℕ) (t : Ty) → Dec (notFreeInTy x t)
?notFreeInTyVec : (x : ℕ) (ts : TyVec) → Dec (notFreeInTyVec x ts)

?notFreeInTy x (tyVar y) with ≡-dec-ℕ x y
... | yes x≡y = no λ x≢y → x≢y x≡y
... | no  x≢y = yes x≢y
?notFreeInTy x (tyConstr s ts) = ?notFreeInTyVec x ts

?notFreeInTyVec x [] = yes tt
?notFreeInTyVec x ((t , k) ∷ ts)
  with ?notFreeInTy (k + x) t | ?notFreeInTyVec x ts
... | yes p | yes q = yes (p , q)
... | yes p | no ¬q = no λ{ (_ , q) → ¬q q }
... | no ¬p | _     = no λ{ (p , _) → ¬p p }