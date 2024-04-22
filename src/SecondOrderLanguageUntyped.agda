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

URen : Set
URen = ℕ → ℕ

UIdRen : URen
UIdRen x = x

URenε : URen
URenε x = zero

UKeep : URen → URen
UKeep ξ zero = zero
UKeep ξ (suc n) = suc (ξ n)

UDrop : URen → URen
UDrop ξ = suc ∘ ξ

UKeep* : URen → ℕ → URen
UKeep* ξ zero = ξ
UKeep* ξ (suc k) = UKeep (UKeep* ξ k)

UDrop* : URen → ℕ → URen
UDrop* ξ zero = ξ
UDrop* ξ (suc k) = UDrop (UDrop* ξ k)

renUnty : URen → UTm → UTm
renVecUnty : URen → UTmVec → UTmVec

renUnty ξ (var x) = var (ξ x)
renUnty ξ (constr s es) = constr s (renVecUnty ξ es)

renVecUnty ξ [] = []
renVecUnty ξ ((e , k) ∷ es) = (renUnty (UKeep* ξ k) e , k) ∷ renVecUnty ξ es

-- The various operations respect extensional equality
UKeepExt : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → UKeep ξ1 ≗ UKeep ξ2
UKeepExt p zero = refl
UKeepExt p (suc n) = cong suc (p n)

UKeepExt* : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → ∀ k → UKeep* ξ1 k ≗ UKeep* ξ2 k
UKeepExt* p zero = p
UKeepExt* p (suc k) = UKeepExt (UKeepExt* p k)

UDropExt : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → UDrop ξ1 ≗ UDrop ξ2
UDropExt p n = cong suc (p n)

UDropExt* : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → ∀ k → UDrop* ξ1 k ≗ UDrop* ξ2 k
UDropExt* p zero = p
UDropExt* p (suc k) = UDropExt (UDropExt* p k)

renUntyExt : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renUnty ξ1 ≗ renUnty ξ2
renVecUntyExt : ∀{ξ1 ξ2} → ξ1 ≗ ξ2 → renVecUnty ξ1 ≗ renVecUnty ξ2

renUntyExt p (var x) = cong var (p x)
renUntyExt p (constr s es) = cong (constr s) (renVecUntyExt p es)

renVecUntyExt p [] = refl
renVecUntyExt p ((e , k) ∷ es) = cong₃ eraseCons
  (renUntyExt (UKeepExt* p k) e)
  refl
  (renVecUntyExt p es)

------------------
-- SUBSTITUTION --
------------------

USub : Set
USub = ℕ → UTm

UIdSub : USub
UIdSub x = var x

USubε : USub
USubε x = var zero

_▹_ : USub → UTm → USub
(σ ▹ e) zero = e
(σ ▹ e) (suc n) = σ n

URenSub : URen → USub → USub
URenSub ξ σ = renUnty ξ ∘ σ

UDropSub : USub → USub
UDropSub σ = URenSub (UDrop id) σ

UKeepSub : USub → USub
UKeepSub σ = UDropSub σ ▹ var zero

UKeepSub* : USub → ℕ → USub
UKeepSub* σ zero = σ
UKeepSub* σ (suc k) = UKeepSub (UKeepSub* σ k)

UDropSub* : USub → ℕ → USub
UDropSub* σ zero = σ
UDropSub* σ (suc k) = UDropSub (UDropSub* σ k)

subUnty : USub → UTm → UTm
subVecUnty : USub → UTmVec → UTmVec

subUnty σ (var x) = σ x
subUnty σ (constr s es) = constr s (subVecUnty σ es)

subVecUnty σ [] = []
subVecUnty σ ((e , k) ∷ es) = (subUnty (UKeepSub* σ k) e , k) ∷ subVecUnty σ es

_◦U_ : USub → USub → USub
σ1 ◦U σ2 = subUnty σ1 ∘ σ2

-- The various operations respect extensional equality
▹Ext : ∀{σ1 σ2} → σ1 ≗ σ2 → ∀ e → σ1 ▹ e ≗ σ2 ▹ e
▹Ext p e zero = refl
▹Ext p e (suc n) = p n

URenSubExt : ∀{ξ1 ξ2 σ1 σ2} → ξ1 ≗ ξ2 → σ1 ≗ σ2 → URenSub ξ1 σ1 ≗ URenSub ξ2 σ2
URenSubExt {ξ1} {ξ2} {σ1} {σ2} p q n =
  renUnty ξ1 (σ1 n) ≡⟨ renUntyExt p (σ1 n) ⟩
  renUnty ξ2 (σ1 n) ≡⟨ cong (renUnty ξ2) (q n) ⟩
  renUnty ξ2 (σ2 n) ∎

UDropSubExt : ∀{σ1 σ2} → σ1 ≗ σ2 → UDropSub σ1 ≗ UDropSub σ2
UDropSubExt p = URenSubExt ≗-refl p

UKeepSubExt : ∀{σ1 σ2} → σ1 ≗ σ2 → UKeepSub σ1 ≗ UKeepSub σ2
UKeepSubExt p = ▹Ext (UDropSubExt p) (var zero)

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
eraseRen ε = id
eraseRen (Keep ξ) = UKeep (eraseRen ξ)
eraseRen (Drop ξ) = UDrop (eraseRen ξ)

eraseSub : ∀{Γ1 Γ2} → Sub Γ1 Γ2 → USub
eraseSub ε = var
eraseSub (σ ▸ e) = eraseSub σ ▹ erase e

-- Type erasure is injective
eraseVar-inj≡ : ∀{Γ1 Γ2 t1 t2} {x : Var Γ1 t1} {y : Var Γ2 t2}
              (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
              eraseVar x ≡ eraseVar y →
              subst₂ Var p q x ≡ y
eraseVar-inj≡ {x = V0} {V0} refl refl refl = refl
eraseVar-inj≡ {x = VS x} {VS y} refl refl r =
  cong VS (eraseVar-inj≡ {x = x} {y} refl refl (suc-injective r))

erase-inj≡ : ∀{Γ1 Γ2 t1 t2} {x : Tm Γ1 t1} {y : Tm Γ2 t2} →
           (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
           erase x ≡ erase y →
           subst₂ Tm p q x ≡ y
eraseVec-inj≡ : ∀{Γ1 Γ2 Σ1 Σ2} {x : TmVec Γ1 Σ1} {y : TmVec Γ2 Σ2} →
              (p : Γ1 ≡ Γ2) (q : Σ1 ≡ Σ2) →
              eraseVec x ≡ eraseVec y →
              subst₂ TmVec p q x ≡ y

erase-inj≡ {x = var x} {var y} refl refl r = cong var (eraseVar-inj≡ refl refl (unVar-inj r))
erase-inj≡ {x = constr s1 es1} {constr s2 es2} refl q r with unConstr-inj r .fst
erase-inj≡ {x = constr s1 es1} {constr .s1 es2} refl refl r | refl =
  cong (constr s1) (eraseVec-inj≡ refl refl (unConstr-inj r .snd))

eraseVec-inj≡ {x = []} {[]} refl refl refl = refl
eraseVec-inj≡ {x = e1 ∷ es1} {e2 ∷ es2} refl refl r =
  cong₂ _∷_
  (erase-inj≡ refl refl (unCons-inj r .fst))
  (eraseVec-inj≡ refl refl (unCons-inj r .snd .snd))

eraseRen-inj≡ : ∀{Γ1 Γ1' Γ2 Γ2'} {ξ1 : Ren Γ1 Γ2} {ξ2 : Ren Γ1' Γ2'} →
              (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
              eraseRen ξ1 ≗ eraseRen ξ2 →
              subst₂ Ren p q ξ1 ≡ ξ2
eraseRen-inj≡ {ξ1 = ε} {ε} refl refl r = refl
eraseRen-inj≡ {ξ1 = Keep ξ1} {Keep ξ2} refl refl r =
  cong Keep (eraseRen-inj≡ refl refl (suc-injective ∘ r ∘ suc))
eraseRen-inj≡ {ξ1 = Keep ξ1} {Drop ξ2} refl refl r = ⊥-elim (0≢1+n (r zero))
eraseRen-inj≡ {ξ1 = Drop ξ1} {Keep ξ2} refl refl r = ⊥-elim (1+n≢0 (r zero))
eraseRen-inj≡ {ξ1 = Drop ξ1} {Drop ξ2} refl refl r =
  cong Drop (eraseRen-inj≡ refl refl (suc-injective ∘ r))

eraseSub-inj≡ : ∀{Γ1 Γ1' Γ2 Γ2'} {σ1 : Sub Γ1 Γ2} {σ2 : Sub Γ1' Γ2'} →
              (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
              eraseSub σ1 ≗ eraseSub σ2 →
              subst₂ Sub p q σ1 ≡ σ2
eraseSub-inj≡ {σ1 = ε} {ε} refl refl r = refl
eraseSub-inj≡ {σ1 = σ1 ▸ e1} {σ2 ▸ e2} refl refl r = cong₂ _▸_
  (eraseSub-inj≡ refl refl (r ∘ suc))
  (erase-inj≡ refl refl (r zero))

eraseVar-inj : ∀{Γ t} {x y : Var Γ t} → eraseVar x ≡ eraseVar y → x ≡ y
eraseVar-inj = eraseVar-inj≡ refl refl

erase-inj : ∀{Γ t} {x y : Tm Γ t} → erase x ≡ erase y → x ≡ y
erase-inj = erase-inj≡ refl refl

eraseVec-inj : ∀{Γ Σ} {x y : TmVec Γ Σ} → eraseVec x ≡ eraseVec y → x ≡ y
eraseVec-inj = eraseVec-inj≡ refl refl

eraseRen-inj : ∀{Γ1 Γ2} {ξ1 ξ2 : Ren Γ1 Γ2} → eraseRen ξ1 ≗ eraseRen ξ2 → ξ1 ≡ ξ2
eraseRen-inj = eraseRen-inj≡ refl refl

eraseSub-inj : ∀{Γ1 Γ2} {σ1 σ2 : Sub Γ1 Γ2} → eraseSub σ1 ≗ eraseSub σ2 → σ1 ≡ σ2
eraseSub-inj = eraseSub-inj≡ refl refl

-- Type erasure commutes with the Keep and Drop operations
eraseRen-Keep* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ →
                eraseRen (Keep* ξ Δ) ≗ UKeep* (eraseRen ξ) (length Δ)
eraseRen-Keep* ξ [] = ≗-refl
eraseRen-Keep* ξ (t ∷ Δ) = UKeepExt (eraseRen-Keep* ξ Δ)

eraseRen-Drop* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ →
                eraseRen (Drop* ξ Δ) ≗ UDrop* (eraseRen ξ) (length Δ)
eraseRen-Drop* ξ [] = ≗-refl
eraseRen-Drop* ξ (t ∷ Δ) = UDropExt (eraseRen-Drop* ξ Δ)

-- Type erasure distributes over renaming
eraseVar-distr-ren : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (x : Var Γ1 t) →
                    eraseVar (renVar ξ x) ≡ eraseRen ξ (eraseVar x)
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
    ≡⟨ renUntyExt (eraseRen-Keep* ξ Δ) (erase e) ⟩
  renUnty (UKeep* (eraseRen ξ) (length Δ)) (erase e) ∎)
  refl
  (eraseVec-distr-ren ξ es)

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
 