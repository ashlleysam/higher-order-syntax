{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import TypeSignatures

-- Untyped and possibly ill-scoped representations of terms
module Terms (⅀ : TypeSignature) where

open TypeSignature ⅀
open import Types (⅀ .⅀ₖ)

---------------
-- RAW TERMS --
---------------

data Tm : Set
data TmVec : Set

-- Raw terms
data Tm where
  var : ℕ → Tm
  constr : (s : ⅀ .TmSymb) (ts : TyVec) (es : TmVec) → Tm

infixr 5 _∷_
-- Lists of raw terms
data TmVec where
  [] : TmVec
  _∷_ : (emn : Tm × ℕ × ℕ)
        (es : TmVec) →
        TmVec

tmCons : Tm → ℕ → ℕ → TmVec → TmVec
tmCons e m n es = (e , m , n) ∷ es

----------------------
-- BASIC PROPERTIES --
----------------------

-- Injectivity of constructors
var-inj : ∀{x y} → var x ≡ var y → x ≡ y
var-inj refl = refl

constr-inj : ∀{s1 s2 ts1 es1 ts2 es2} →
             constr s1 ts1 es1 ≡ constr s2 ts2 es2 →
            s1 ≡ s2 × ts1 ≡ ts2 × es1 ≡ es2
constr-inj refl = refl , refl , refl

tmCons-inj : ∀{e1 e2 m1 m2 n1 n2 es1 es2} →
              _≡_ {A = TmVec} ((e1 , m1 , n1) ∷ es1) ((e2 , m2 , n2) ∷ es2) →
              e1 ≡ e2 × m1 ≡ m2 × n1 ≡ n2 × es1 ≡ es2
tmCons-inj refl = refl , refl , refl , refl

-------------------
-- TYPE RENAMING --
-------------------

tyRen : Ren → Tm → Tm
tyRenVec : Ren → TmVec → TmVec

tyRen ξ (var x) = var x
tyRen ξ (constr s ts es) =
  constr s (renTyVec ξ ts) (tyRenVec ξ es)

tyRenVec ξ [] = []
tyRenVec ξ ((e , m , n) ∷ es) =
  (tyRen (Keep* ξ m) e , m , n) ∷ tyRenVec ξ es

tyRen-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → tyRen ξ1 ≗ tyRen ξ2
tyRenVec-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → tyRenVec ξ1 ≗ tyRenVec ξ2

tyRen-ext p (var x) = refl
tyRen-ext p (constr s ts es) =
  cong₂ (constr s) 
    (renTyVec-ext p ts)
    (tyRenVec-ext p es)

tyRenVec-ext p [] = refl
tyRenVec-ext p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tyRen-ext (Keep*-ext p m) e)
    (tyRenVec-ext p es)

tyRen-≈Id : ∀{ξ} → ξ ≗ id → tyRen ξ ≗ id
tyRenVec-≈Id : ∀{ξ} → ξ ≗ id → tyRenVec ξ ≗ id

tyRen-≈Id p (var x) = refl
tyRen-≈Id p (constr s ts es) =
  cong₂ (constr s)
    (renTyVec-≈Id p ts)
    (tyRenVec-≈Id p es)

tyRenVec-≈Id p [] = refl
tyRenVec-≈Id p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tyRen-≈Id (λ x → Keep*-ext p m x ∙ Keep*-id m x) e)
    (tyRenVec-≈Id p es)

tyRenId : tyRen id ≗ id
tyRenId e = tyRen-≈Id ≗-refl e

tyRenVecId : tyRenVec id ≗ id
tyRenVecId es = tyRenVec-≈Id ≗-refl es

tyRen• : (ξ1 ξ2 : Ren) → tyRen ξ1 ∘ tyRen ξ2 ≗ tyRen (ξ1 • ξ2)
tyRenVec• : (ξ1 ξ2 : Ren) → tyRenVec ξ1 ∘ tyRenVec ξ2 ≗ tyRenVec (ξ1 • ξ2)

tyRen• ξ1 ξ2 (var x) = refl
tyRen• ξ1 ξ2 (constr s ts es) =
  cong₂ (constr s)
    (renTyVec• ξ1 ξ2 ts)
    (tyRenVec• ξ1 ξ2 es)

tyRenVec• ξ1 ξ2 [] = refl
tyRenVec• ξ1 ξ2 ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tyRen (Keep* ξ1 m) (tyRen (Keep* ξ2 m) e)
      ≡⟨ tyRen• (Keep* ξ1 m) (Keep* ξ2 m) e ⟩
    tyRen (Keep* ξ1 m • Keep* ξ2 m) e
      ≡⟨ tyRen-ext (Keep*•Keep* ξ1 ξ2 m) e ⟩
    tyRen (Keep* (ξ1 • ξ2) m) e ∎)
    (tyRenVec• ξ1 ξ2 es)

-----------------------
-- TYPE SUBSTITUTION --
-----------------------

tySub : TySub → Tm → Tm
tySubVec : TySub → TmVec → TmVec

tySub σ (var x) = var x
tySub σ (constr s ts es) =
  constr s (subTyVec σ ts) (tySubVec σ es)

tySubVec σ [] = []
tySubVec σ ((e , m , n) ∷ es) =
  (tySub (TyKeepSub* σ m) e , m , n) ∷ tySubVec σ es

tySub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → tySub σ1 ≗ tySub σ2
tySubVec-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → tySubVec σ1 ≗ tySubVec σ2

tySub-ext p (var x) = refl
tySub-ext p (constr s ts es) =
  cong₂ (constr s)
    (subTyVec-ext p ts)
    (tySubVec-ext p es)

tySubVec-ext p [] = refl
tySubVec-ext p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tySub-ext (TyKeepSub*-ext p m) e)
    (tySubVec-ext p es)

tySub-≈Id : ∀{σ} → σ ≗ tyVar → tySub σ ≗ id
tySubVec-≈Id : ∀{σ} → σ ≗ tyVar → tySubVec σ ≗ id

tySub-≈Id p (var x) = refl
tySub-≈Id p (constr s ts es) =
  cong₂ (constr s)
    (subTyVec-≈Id p ts)
    (tySubVec-≈Id p es)

tySubVec-≈Id p [] = refl
tySubVec-≈Id p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tySub-≈Id (λ x → TyKeepSub*-ext p m x ∙ TyKeepSub*-id m x) e)
    (tySubVec-≈Id p es)

tySubId : tySub tyVar ≗ id
tySubId = tySub-≈Id ≗-refl

tySubVecId : tySubVec tyVar ≗ id
tySubVecId = tySubVec-≈Id ≗-refl

tySub•◦ₜ : (ξ : Ren) (σ : TySub) → tyRen ξ ∘ tySub σ ≗ tySub (ξ •◦ₜ σ)
tySubVec•◦ₜ : (ξ : Ren) (σ : TySub) → tyRenVec ξ ∘ tySubVec σ ≗ tySubVec (ξ •◦ₜ σ)

tySub•◦ₜ ξ σ (var x) = refl
tySub•◦ₜ ξ σ (constr s ts es) =
  cong₂ (constr s)
    (subTyVec•◦ₜ ξ σ ts)
    (tySubVec•◦ₜ ξ σ es)

tySubVec•◦ₜ ξ σ [] = refl
tySubVec•◦ₜ ξ σ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tyRen (Keep* ξ m) (tySub (TyKeepSub* σ m) e)
      ≡⟨ tySub•◦ₜ (Keep* ξ m) (TyKeepSub* σ m) e ⟩
    tySub (Keep* ξ m •◦ₜ TyKeepSub* σ m) e
      ≡⟨ tySub-ext (Keep*•◦ₜKeep* ξ σ m) e ⟩
    tySub (TyKeepSub* (ξ •◦ₜ σ) m) e ∎)
    (tySubVec•◦ₜ ξ σ es)

tySub◦•ₜ : (σ : TySub) (ξ : Ren) → tySub σ ∘ tyRen ξ ≗ tySub (σ ◦•ₜ ξ)
tySubVec◦•ₜ : (σ : TySub) (ξ : Ren) → tySubVec σ ∘ tyRenVec ξ ≗ tySubVec (σ ◦•ₜ ξ)

tySub◦•ₜ σ ξ (var x) = refl
tySub◦•ₜ σ ξ (constr s ts es) =
  cong₂ (constr s)
    (subTyVec◦•ₜ σ ξ ts)
    (tySubVec◦•ₜ σ ξ es)

tySubVec◦•ₜ σ ξ [] = refl
tySubVec◦•ₜ σ ξ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tySub (TyKeepSub* σ m) (tyRen (Keep* ξ m) e)
      ≡⟨ tySub◦•ₜ (TyKeepSub* σ m) (Keep* ξ m) e ⟩
    tySub (TyKeepSub* σ m ◦•ₜ Keep* ξ m) e
      ≡⟨ tySub-ext (Keep*◦•ₜKeep* σ ξ m) e ⟩
    tySub (TyKeepSub* (σ ◦•ₜ ξ) m) e ∎)
    (tySubVec◦•ₜ σ ξ es)

tySub◦ₜ : (σ1 σ2 : TySub) → tySub σ1 ∘ tySub σ2 ≗ tySub (σ1 ◦ₜ σ2)
tySubVec◦ₜ : (σ1 σ2 : TySub) → tySubVec σ1 ∘ tySubVec σ2 ≗ tySubVec (σ1 ◦ₜ σ2)

tySub◦ₜ σ1 σ2 (var x) = refl
tySub◦ₜ σ1 σ2 (constr s ts es) =
  cong₂ (constr s)
    (subTyVec◦ₜ σ1 σ2 ts)
    (tySubVec◦ₜ σ1 σ2 es)

tySubVec◦ₜ σ1 σ2 [] = refl
tySubVec◦ₜ σ1 σ2 ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tySub (TyKeepSub* σ1 m) (tySub (TyKeepSub* σ2 m) e)
      ≡⟨ tySub◦ₜ (TyKeepSub* σ1 m) (TyKeepSub* σ2 m) e ⟩
    tySub (TyKeepSub* σ1 m ◦ₜ TyKeepSub* σ2 m) e
      ≡⟨ tySub-ext (Keep*◦ₜKeep* σ1 σ2 m) e ⟩
    tySub (TyKeepSub* (σ1 ◦ₜ σ2) m) e ∎)
    (tySubVec◦ₜ σ1 σ2 es)

tySubιₜ : (ξ : Ren) → tySub (ιₜ ξ) ≗ tyRen ξ
tySubVecιₜ : (ξ : Ren) → tySubVec (ιₜ ξ) ≗ tyRenVec ξ

tySubιₜ ξ (var x) = refl
tySubιₜ ξ (constr s ts es) =
  cong₂ (constr s)
    (subTyVecιₜ ξ ts)
    (tySubVecιₜ ξ es)

tySubVecιₜ ξ [] = refl
tySubVecιₜ ξ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (tySub (TyKeepSub* (ιₜ ξ) m) e
      ≡⟨ (sym $ tySub-ext (Keep*ιₜ ξ m) e) ⟩
    tySub (ιₜ (Keep* ξ m)) e
      ≡⟨ tySubιₜ (Keep* ξ m) e ⟩
    tyRen (Keep* ξ m) e ∎)
    (tySubVecιₜ ξ es)

--------------
-- RENAMING --
--------------

ren : Ren → Tm → Tm
renVec : Ren → TmVec → TmVec

ren ξ (var x) = var (ξ x)
ren ξ (constr s ts es) =
  constr s ts (renVec ξ es)

renVec ξ [] = []
renVec ξ ((e , m , n) ∷ es) =
  (ren (Keep* ξ n) e , m , n) ∷ renVec ξ es

ren-tyRen-comm : (ξ ξₜ : Ren) → ren ξ ∘ tyRen ξₜ ≗ tyRen ξₜ ∘ ren ξ
renVec-tyRenVec-comm : (ξ ξₜ : Ren) → renVec ξ ∘ tyRenVec ξₜ ≗ tyRenVec ξₜ ∘ renVec ξ

ren-tyRen-comm ξ ξₜ (var x) = refl
ren-tyRen-comm ξ ξₜ (constr s ts es) =
  cong (constr s (renTyVec ξₜ ts))
    (renVec-tyRenVec-comm ξ ξₜ es)

renVec-tyRenVec-comm ξ ξₜ [] = refl
renVec-tyRenVec-comm ξ ξₜ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (ren-tyRen-comm (Keep* ξ n) (Keep* ξₜ m) e)
    (renVec-tyRenVec-comm ξ ξₜ es)

ren-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → ren ξ1 ≗ ren ξ2
renVec-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renVec ξ1 ≗ renVec ξ2

ren-ext p (var x) = cong var (p x)
ren-ext p (constr s ts es) =
  cong (constr s ts) (renVec-ext p es)

renVec-ext p [] = refl
renVec-ext p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (ren-ext (Keep*-ext p n) e)
    (renVec-ext p es)

ren-≈Id : ∀{ξ} → ξ ≗ id → ren ξ ≗ id
renVec-≈Id : ∀{ξ} → ξ ≗ id → renVec ξ ≗ id

ren-≈Id p (var x) = cong var (p x)
ren-≈Id p (constr s ts es) =
  cong (constr s ts) (renVec-≈Id p es)

renVec-≈Id p [] = refl
renVec-≈Id p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (ren-≈Id (λ x → Keep*-ext p n x ∙ Keep*-id n x) e)
    (renVec-≈Id p es)

renId : ren id ≗ id
renId e = ren-≈Id ≗-refl e

renVecId : renVec id ≗ id
renVecId es = renVec-≈Id ≗-refl es

ren• : (ξ1 ξ2 : Ren) → ren ξ1 ∘ ren ξ2 ≗ ren (ξ1 • ξ2)
renVec• : (ξ1 ξ2 : Ren) → renVec ξ1 ∘ renVec ξ2 ≗ renVec (ξ1 • ξ2)

ren• ξ1 ξ2 (var x) = refl
ren• ξ1 ξ2 (constr s ts es) =
  cong (constr s ts) (renVec• ξ1 ξ2 es)

renVec• ξ1 ξ2 [] = refl
renVec• ξ1 ξ2 ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (ren (Keep* ξ1 n) (ren (Keep* ξ2 n) e)
      ≡⟨ ren• (Keep* ξ1 n) (Keep* ξ2 n) e ⟩
    ren (Keep* ξ1 n • Keep* ξ2 n) e
      ≡⟨ ren-ext (Keep*•Keep* ξ1 ξ2 n) e ⟩
    ren (Keep* (ξ1 • ξ2) n) e ∎)
    (renVec• ξ1 ξ2 es)

------------------
-- SUBSTITUTION --
------------------

Sub : Set
Sub = ℕ → Tm

ι : Ren → Sub
ι ξ x = var (ξ x)

ι-ext : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → ι ξ1 ≗ ι ξ2
ι-ext p x = cong var (p x)

ιId : ∀{ξ} → ξ ≗ id → ι ξ ≗ var
ιId p x = cong var (p x)

infixr 9 _•◦_
_•◦_ : Ren → Sub → Sub
(ξ •◦ σ) x = ren ξ (σ x)

•◦-ext : ∀{ξ1 ξ2 σ1 σ2} →
          ξ1 ≗ ξ2 →
          σ1 ≗ σ2 →
          (ξ1 •◦ σ1) ≗ (ξ2 •◦ σ2)
•◦-ext {ξ1} {ξ2} {σ1} {σ2} p q x =
  ren ξ1 (σ1 x)
    ≡⟨ ren-ext p (σ1 x) ⟩
  ren ξ2 (σ1 x)
    ≡⟨ cong (ren ξ2) (q x) ⟩
  ren ξ2 (σ2 x) ∎

••◦ : (ξ1 ξ2 : Ren) (σ : Sub) →
      (ξ1 • ξ2) •◦ σ ≗ ξ1 •◦ (ξ2 •◦ σ)
••◦ ξ1 ξ2 σ x = sym $ ren• ξ1 ξ2 (σ x)

Id•◦ : (σ : Sub) → id •◦ σ ≗ σ
Id•◦ σ x = renId (σ x)

•◦Id : (ξ : Ren) → ξ •◦ var ≗ ι ξ
•◦Id ξ x = refl

•◦-▸ : (ξ : Ren) (σ : Sub) (e : Tm) →
        (ξ •◦ (σ ▸ e)) ≗ (ξ •◦ σ) ▸ ren ξ e
•◦-▸ ξ σ e zero = refl
•◦-▸ ξ σ e (suc x) = refl     

DropSub : Sub → Sub
DropSub σ = Drop id •◦ σ

DropSub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → DropSub σ1 ≗ DropSub σ2
DropSub-ext p = •◦-ext ≗-refl p

DropSub* : Sub → ℕ → Sub
DropSub* σ zero = σ
DropSub* σ (suc k) = DropSub (DropSub* σ k)

DropSub*-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → (n : ℕ) → DropSub* σ1 n ≗ DropSub* σ2 n
DropSub*-ext p zero = p
DropSub*-ext p (suc n) = DropSub-ext (DropSub*-ext p n)

KeepSub : Sub → Sub
KeepSub σ = DropSub σ ▸ var zero

KeepSub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → KeepSub σ1 ≗ KeepSub σ2
KeepSub-ext p = ▸-ext (DropSub-ext p) refl

KeepSub-id : KeepSub var ≗ var
KeepSub-id zero = refl
KeepSub-id (suc x) = refl

KeepSub* : Sub → ℕ → Sub
KeepSub* σ zero = σ
KeepSub* σ (suc k) = KeepSub (KeepSub* σ k)

KeepSub*-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → (n : ℕ) → KeepSub* σ1 n ≗ KeepSub* σ2 n
KeepSub*-ext p zero = p
KeepSub*-ext p (suc n) = KeepSub-ext (KeepSub*-ext p n)

KeepSub*-id : (n : ℕ) → KeepSub* var n ≗ var
KeepSub*-id zero = ≗-refl
KeepSub*-id (suc n) x = KeepSub-ext (KeepSub*-id n) x ∙ KeepSub-id x

Keep•◦Drop : (ξ : Ren) (σ : Sub) → Keep ξ •◦ DropSub σ ≗ DropSub (ξ •◦ σ)
Keep•◦Drop ξ σ x =
  ren (Keep ξ) (ren suc (σ x))
    ≡⟨ ren• (Keep ξ) suc (σ x) ⟩
  ren (suc ∘ ξ) (σ x)
    ≡⟨ (sym $ ren• suc ξ (σ x)) ⟩
  ren suc (ren ξ (σ x)) ∎

Keep*•◦Drop* : (ξ : Ren) (σ : Sub) (n : ℕ) →
                Keep* ξ n •◦ DropSub* σ n ≗ DropSub* (ξ •◦ σ) n
Keep*•◦Drop* ξ σ zero = ≗-refl
Keep*•◦Drop* ξ σ (suc n) x = 
  (Keep (Keep* ξ n) •◦ DropSub (DropSub* σ n)) x
    ≡⟨ Keep•◦Drop (Keep* ξ n) (DropSub* σ n) x ⟩
  DropSub (Keep* ξ n •◦ DropSub* σ n) x
    ≡⟨ DropSub-ext (Keep*•◦Drop* ξ σ n) x ⟩
  DropSub (DropSub* (ξ •◦ σ) n) x ∎

Keep•◦Keep : (ξ : Ren) (σ : Sub) → Keep ξ •◦ KeepSub σ ≗ KeepSub (ξ •◦ σ)
Keep•◦Keep ξ σ zero = refl
Keep•◦Keep ξ σ (suc x) = Keep•◦Drop ξ σ x

Keep*•◦Keep* : (ξ : Ren) (σ : Sub) (n : ℕ) →
                Keep* ξ n •◦ KeepSub* σ n ≗ KeepSub* (ξ •◦ σ) n
Keep*•◦Keep* ξ σ zero = ≗-refl
Keep*•◦Keep* ξ σ (suc n) x = 
  (Keep (Keep* ξ n) •◦ KeepSub (KeepSub* σ n)) x
    ≡⟨ Keep•◦Keep (Keep* ξ n) (KeepSub* σ n) x ⟩
  KeepSub (Keep* ξ n •◦ KeepSub* σ n) x
    ≡⟨ KeepSub-ext (Keep*•◦Keep* ξ σ n) x ⟩
  KeepSub (KeepSub* (ξ •◦ σ) n) x ∎

Keepι : (ξ : Ren) → ι (Keep ξ) ≗ KeepSub (ι ξ)
Keepι ξ zero = refl
Keepι ξ (suc x) = refl

Dropι : (ξ : Ren) → ι (Drop ξ) ≗ DropSub (ι ξ)
Dropι ξ x = refl

Keep*ι : (ξ : Ren) (n : ℕ) → ι (Keep* ξ n) ≗ KeepSub* (ι ξ) n
Keep*ι ξ zero = ≗-refl
Keep*ι ξ (suc n) x =
  ι (Keep (Keep* ξ n)) x
    ≡⟨ Keepι (Keep* ξ n) x ⟩
  KeepSub (ι (Keep* ξ n)) x
    ≡⟨ KeepSub-ext (Keep*ι ξ n) x ⟩
  KeepSub (KeepSub* (ι ξ) n) x ∎

Drop*ι : (ξ : Ren) (n : ℕ) → ι (Drop* ξ n) ≗ DropSub* (ι ξ) n
Drop*ι ξ zero = ≗-refl
Drop*ι ξ (suc n) x =
  ι (Drop (Drop* ξ n)) x
    ≡⟨ Dropι (Drop* ξ n) x ⟩
  DropSub (ι (Drop* ξ n)) x
    ≡⟨ DropSub-ext (Drop*ι ξ n) x ⟩
  DropSub (DropSub* (ι ξ) n) x ∎

sub : Sub → Tm → Tm
subVec : Sub → TmVec → TmVec

sub σ (var x) = σ x
sub σ (constr s ts es) =
  constr s ts (subVec σ es)

subVec σ [] = []
subVec σ ((e , m , n) ∷ es) =
  (sub (KeepSub* (tyRen (Drop* id m) ∘ σ) n) e , m , n)
  ∷ subVec σ es

sub-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → sub σ1 ≗ sub σ2
subVec-ext : ∀{σ1 σ2} → σ1 ≗ σ2 → subVec σ1 ≗ subVec σ2

sub-ext p (var x) = p x
sub-ext p (constr s ts es) =
  cong (constr s ts) (subVec-ext p es)

subVec-ext p [] = refl
subVec-ext p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub-ext (KeepSub*-ext (λ x → cong (tyRen (Drop* id m)) (p x)) n) e)
    (subVec-ext p es)


sub-≈Id : ∀{σ} → σ ≗ var → sub σ ≗ id
subVec-≈Id : ∀{σ} → σ ≗ var → subVec σ ≗ id

sub-≈Id p (var x) = p x
sub-≈Id p (constr s ts es) =
  cong (constr s ts) (subVec-≈Id p es)

subVec-≈Id p [] = refl
subVec-≈Id p ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub-≈Id (λ x →
      KeepSub*-ext (λ x → cong (tyRen (Drop* id m)) (p x)) n x
        ∙ KeepSub*-id n x) e)
    (subVec-≈Id p es)

subId : sub var ≗ id
subId = sub-≈Id ≗-refl

subVecId : subVec var ≗ id
subVecId = subVec-≈Id ≗-refl

sub•◦ : (ξ : Ren) (σ : Sub) → ren ξ ∘ sub σ ≗ sub (ξ •◦ σ)
subVec•◦ : (ξ : Ren) (σ : Sub) → renVec ξ ∘ subVec σ ≗ subVec (ξ •◦ σ)

sub•◦ ξ σ (var x) = refl
sub•◦ ξ σ (constr s ts es) =
  cong (constr s ts) (subVec•◦ ξ σ es)

subVec•◦ ξ σ [] = refl
subVec•◦ ξ σ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (ren (Keep* ξ n) (sub (KeepSub* (tyRen (Drop* id m) ∘ σ) n) e)
      ≡⟨ sub•◦ (Keep* ξ n) (KeepSub* (tyRen (Drop* id m) ∘ σ) n) e ⟩
    sub (Keep* ξ n •◦ KeepSub* (tyRen (Drop* id m) ∘ σ) n) e
      ≡⟨ sub-ext (Keep*•◦Keep* ξ (tyRen (Drop* id m) ∘ σ) n) e ⟩
    sub (KeepSub* (ξ •◦ (tyRen (Drop* id m) ∘ σ)) n) e
      ≡⟨ sub-ext (KeepSub*-ext (λ x → ren-tyRen-comm ξ (Drop* id m) (σ x)) n) e ⟩
    sub (KeepSub* (tyRen (Drop* id m) ∘ (ξ •◦ σ)) n) e ∎)
    (subVec•◦ ξ σ es)

infixr 9 _◦•_
_◦•_ : Sub → Ren → Sub
(σ ◦• ξ) x = σ (ξ x)

Keep◦•Drop : (σ : Sub) (ξ : Ren) → KeepSub σ ◦• Drop ξ ≗ DropSub (σ ◦• ξ)
Keep◦•Drop σ ξ x = refl

Keep*◦•Drop* : (σ : Sub) (ξ : Ren) (n : ℕ) →
               KeepSub* σ n ◦• Drop* ξ n ≗ DropSub* (σ ◦• ξ) n
Keep*◦•Drop* σ ξ zero = ≗-refl
Keep*◦•Drop* σ ξ (suc n) x = 
  (KeepSub (KeepSub* σ n) ◦• Drop (Drop* ξ n)) x
    ≡⟨ Keep◦•Drop (KeepSub* σ n) (Drop* ξ n) x ⟩
  DropSub (KeepSub* σ n ◦• Drop* ξ n) x
    ≡⟨ DropSub-ext (Keep*◦•Drop* σ ξ n) x ⟩
  DropSub (DropSub* (σ ◦• ξ) n) x ∎

Keep◦•Keep : (σ : Sub) (ξ : Ren) → KeepSub σ ◦• Keep ξ ≗ KeepSub (σ ◦• ξ)
Keep◦•Keep σ ξ zero = refl
Keep◦•Keep σ ξ (suc x) = Keep◦•Drop σ ξ x

Keep*◦•Keep* : (σ : Sub) (ξ : Ren) (n : ℕ) →
                KeepSub* σ n ◦• Keep* ξ n ≗ KeepSub* (σ ◦• ξ) n
Keep*◦•Keep* σ ξ zero = ≗-refl
Keep*◦•Keep* σ ξ (suc n) x = 
  (KeepSub (KeepSub* σ n) ◦• Keep (Keep* ξ n)) x
    ≡⟨ Keep◦•Keep (KeepSub* σ n) (Keep* ξ n) x ⟩
  KeepSub (KeepSub* σ n ◦• Keep* ξ n) x
    ≡⟨ KeepSub-ext (Keep*◦•Keep* σ ξ n) x ⟩
  KeepSub (KeepSub* (σ ◦• ξ) n) x ∎

Id◦• : (ξ : Ren) → var ◦• ξ ≗ ι ξ
Id◦• ξ x = refl

◦•Id : (σ : Sub) → σ ◦• id ≗ σ
◦•Id σ x = refl

sub◦• : (σ : Sub) (ξ : Ren) → sub σ ∘ ren ξ ≗ sub (σ ◦• ξ)
subVec◦• : (σ : Sub) (ξ : Ren) → subVec σ ∘ renVec ξ ≗ subVec (σ ◦• ξ)

sub◦• σ ξ (var x) = refl
sub◦• σ ξ (constr s ts es) =
  cong (constr s ts) (subVec◦• σ ξ es)

subVec◦• σ ξ [] = refl
subVec◦• σ ξ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub (KeepSub* (tyRen (Drop* id m) ∘ σ) n) (ren (Keep* ξ n) e)
      ≡⟨ sub◦• (KeepSub* (tyRen (Drop* id m) ∘ σ) n) (Keep* ξ n) e ⟩
    sub (KeepSub* (tyRen (Drop* id m) ∘ σ) n ◦• Keep* ξ n) e
      ≡⟨ sub-ext (Keep*◦•Keep* (tyRen (Drop* id m) ∘ σ) ξ n) e ⟩
    sub (KeepSub* (tyRen (Drop* id m) ∘ (σ ◦• ξ)) n) e ∎)
    (subVec◦• σ ξ es)

infixr 9 _◦_ 
_◦_ : Sub → Sub → Sub
(σ1 ◦ σ2) x = sub σ1 (σ2 x)

Keep◦Keep : (σ1 σ2 : Sub) → KeepSub σ1 ◦ KeepSub σ2 ≗ KeepSub (σ1 ◦ σ2)
Keep◦Keep σ1 σ2 zero = refl
Keep◦Keep σ1 σ2 (suc x) =
  sub (KeepSub σ1) (ren suc (σ2 x))
    ≡⟨ sub◦• (KeepSub σ1) suc (σ2 x) ⟩
  sub (ren suc ∘ σ1) (σ2 x)
    ≡⟨ sym $ sub•◦ suc σ1 (σ2 x) ⟩
  ren suc (sub σ1 (σ2 x)) ∎

Keep*◦Keep* : (σ1 σ2 : Sub) (n : ℕ) →
              KeepSub* σ1 n ◦ KeepSub* σ2 n ≗ KeepSub* (σ1 ◦ σ2) n
Keep*◦Keep* σ1 σ2 zero = ≗-refl
Keep*◦Keep* σ1 σ2 (suc n) x =
  (KeepSub (KeepSub* σ1 n) ◦ KeepSub (KeepSub* σ2 n)) x
    ≡⟨ Keep◦Keep (KeepSub* σ1 n) (KeepSub* σ2 n) x ⟩
  KeepSub (KeepSub* σ1 n ◦ KeepSub* σ2 n) x
    ≡⟨ KeepSub-ext (Keep*◦Keep* σ1 σ2 n) x ⟩
  KeepSub (KeepSub* (σ1 ◦ σ2) n) x ∎

Drop-tyRen : (ξₜ : Ren) (σ : Sub) →
             DropSub (tyRen ξₜ ∘ σ) ≗ tyRen ξₜ ∘ DropSub σ
Drop-tyRen ξₜ σ x =
  ren suc (tyRen ξₜ (σ x))
    ≡⟨ ren-tyRen-comm suc ξₜ (σ x) ⟩
  tyRen ξₜ (ren suc (σ x)) ∎

Keep-tyRen : (ξₜ : Ren) (σ : Sub) →
             KeepSub (tyRen ξₜ ∘ σ) ≗ tyRen ξₜ ∘ KeepSub σ
Keep-tyRen ξₜ σ zero = refl
Keep-tyRen ξₜ σ (suc x) = Drop-tyRen ξₜ σ x

Keep*-tyRen : (ξₜ : Ren) (σ : Sub) (n : ℕ) →
              KeepSub* (tyRen ξₜ ∘ σ) n ≗ tyRen ξₜ ∘ KeepSub* σ n
Keep*-tyRen ξₜ σ zero = ≗-refl
Keep*-tyRen ξₜ σ (suc n) x =
  KeepSub (KeepSub* (tyRen ξₜ ∘ σ) n) x
    ≡⟨ KeepSub-ext (Keep*-tyRen ξₜ σ n) x ⟩
  KeepSub (tyRen ξₜ ∘ KeepSub* σ n) x
    ≡⟨ Keep-tyRen ξₜ (KeepSub* σ n) x ⟩
  tyRen ξₜ (KeepSub (KeepSub* σ n) x) ∎

sub-tyRen-comm : (ξₜ : Ren) (σ : Sub) (e : Tm) →
                sub (tyRen ξₜ ∘ σ) (tyRen ξₜ e)
                ≡ tyRen ξₜ (sub σ e)
sub-tyRenVec-comm : (ξₜ : Ren) (σ : Sub) (es : TmVec) →
                    subVec (tyRen ξₜ ∘ σ) (tyRenVec ξₜ es)
                    ≡ tyRenVec ξₜ (subVec σ es)

sub-tyRen-comm ξₜ σ (var x) = refl
sub-tyRen-comm ξₜ σ (constr s ts es) =
  cong (constr s (renTyVec ξₜ ts))
    (sub-tyRenVec-comm ξₜ σ es)

sub-tyRenVec-comm ξₜ σ [] = refl
sub-tyRenVec-comm ξₜ σ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub (KeepSub* (tyRen (Drop* id m) ∘ tyRen ξₜ ∘ σ) n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (KeepSub*-ext (λ x → tyRen• (Drop* id m) ξₜ (σ x)) n) (tyRen (Keep* ξₜ m) e) ⟩
    sub (KeepSub* (tyRen (Drop* id m • ξₜ) ∘ σ) n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (KeepSub*-ext (λ x → tyRen-ext (Drop*• id ξₜ m) (σ x)) n) (tyRen (Keep* ξₜ m) e) ⟩
    sub (KeepSub* (tyRen (Drop* ξₜ m) ∘ σ) n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (Keep*-tyRen (Drop* ξₜ m) σ n) (tyRen (Keep* ξₜ m) e) ⟩
    sub (tyRen (Drop* ξₜ m) ∘ KeepSub* σ n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (λ x → tyRen-ext (λ x → sym $ Keep*•Drop* ξₜ id m x) (KeepSub* σ n x)) (tyRen (Keep* ξₜ m) e) ⟩
    sub (tyRen (Keep* ξₜ m • Drop* id m) ∘ KeepSub* σ n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (λ x → sym $ tyRen• (Keep* ξₜ m) (Drop* id m) (KeepSub* σ n x)) (tyRen (Keep* ξₜ m) e) ⟩
    sub (tyRen (Keep* ξₜ m) ∘ tyRen (Drop* id m) ∘ KeepSub* σ n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-ext (λ x → cong (tyRen (Keep* ξₜ m)) (sym $ Keep*-tyRen (Drop* id m) σ n x))
          (tyRen (Keep* ξₜ m) e) ⟩
    sub (tyRen (Keep* ξₜ m) ∘ KeepSub* (tyRen (Drop* id m) ∘ σ) n) (tyRen (Keep* ξₜ m) e)
      ≡⟨ sub-tyRen-comm (Keep* ξₜ m) (KeepSub* (tyRen (Drop* id m) ∘ σ) n) e ⟩
    tyRen (Keep* ξₜ m)
      (sub (KeepSub* (tyRen (Drop* id m) ∘ σ) n) e) ∎)
    (sub-tyRenVec-comm ξₜ σ es)

sub◦ : (σ1 σ2 : Sub) → sub σ1 ∘ sub σ2 ≗ sub (σ1 ◦ σ2)
subVec◦ : (σ1 σ2 : Sub) → subVec σ1 ∘ subVec σ2 ≗ subVec (σ1 ◦ σ2)

sub◦ σ1 σ2 (var x) = refl
sub◦ σ1 σ2 (constr s ts es) =
  cong (constr s ts) (subVec◦ σ1 σ2 es)

subVec◦ σ1 σ2 [] = refl
subVec◦ σ1 σ2 ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub (KeepSub* (tyRen (Drop* id m) ∘ σ1) n)
      (sub (KeepSub* (tyRen (Drop* id m) ∘ σ2) n) e)
      ≡⟨ sub◦ (KeepSub* (tyRen (Drop* id m) ∘ σ1) n)
            (KeepSub* (tyRen (Drop* id m) ∘ σ2) n) e ⟩
    sub (KeepSub* (tyRen (Drop* id m) ∘ σ1) n
          ◦ KeepSub* (tyRen (Drop* id m) ∘ σ2) n)
        e
      ≡⟨ sub-ext
          (Keep*◦Keep* (tyRen (Drop* id m) ∘ σ1)
            (tyRen (Drop* id m) ∘ σ2) n)
          e ⟩
    sub (KeepSub* ((tyRen (Drop* id m) ∘ σ1) ◦ (tyRen (Drop* id m) ∘ σ2)) n) e
      ≡⟨ sub-ext (KeepSub*-ext (λ x → sub-tyRen-comm (Drop* id m) σ1 (σ2 x)) n) e ⟩
    sub (KeepSub* (tyRen (Drop* id m) ∘ (σ1 ◦ σ2)) n) e ∎)
    (subVec◦ σ1 σ2 es)

subι : (ξ : Ren) → sub (ι ξ) ≗ ren ξ
subVecι : (ξ : Ren) → subVec (ι ξ) ≗ renVec ξ

subι ξ (var x) = refl
subι ξ (constr s ts es) =
  cong (constr s ts) (subVecι ξ es)

subVecι ξ [] = refl
subVecι ξ ((e , m , n) ∷ es) =
  cong₂ (λ x y → (x , m , n) ∷ y)
    (sub (KeepSub* (ι ξ) n) e
      ≡⟨ sub-ext (λ x → sym $ Keep*ι ξ n x) e ⟩
    sub (ι (Keep* ξ n)) e
      ≡⟨ subι (Keep* ξ n) e ⟩
    ren (Keep* ξ n) e ∎)
    (subVecι ξ es)

notFreeTyInTm : ℕ → Tm → Set
notFreeTyInTmVec : ℕ → TmVec → Set

notFreeTyInTm x (var y) = ⊤
notFreeTyInTm x (constr s ts es) =
  notFreeInTyVec x ts ×
  notFreeTyInTmVec x es

notFreeTyInTmVec x [] = ⊤
notFreeTyInTmVec x ((e , m , n) ∷ es) =
  notFreeTyInTm (m + x) e × notFreeTyInTmVec x es

?notFreeTyInTm : (x : ℕ) (t : Tm) → Dec (notFreeTyInTm x t)
?notFreeTyInTmVec : (x : ℕ) (ts : TmVec) → Dec (notFreeTyInTmVec x ts)

?notFreeTyInTm x (var y) = yes tt
?notFreeTyInTm x (constr s ts es)
  with ?notFreeInTyVec x ts | ?notFreeTyInTmVec x es
... | yes p | yes q = yes (p , q)
... | yes p | no ¬q = no λ{ (_ , q) → ¬q q }
... | no ¬p | _     = no λ{ (p , _) → ¬p p }

?notFreeTyInTmVec x [] = yes tt
?notFreeTyInTmVec x ((e , m , n) ∷ es)
  with ?notFreeTyInTm (m + x) e | ?notFreeTyInTmVec x es
... | yes p | yes q = yes (p , q)
... | yes p | no ¬q = no λ{ (_ , q) → ¬q q }
... | no ¬p | _     = no λ{ (p , _) → ¬p p }
