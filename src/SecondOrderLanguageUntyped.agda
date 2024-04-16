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

untyCons : UTm → ℕ → UTmVec → UTmVec
untyCons e k es = (e , k) ∷ es

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
renVecUntyExt p ((e , k) ∷ es) = cong₃ untyCons
  (renUntyExt (UKeepExt* p k) e)
  refl
  (renVecUntyExt p es)

------------------
-- SUBSTITUTION --
------------------

USub : Set
USub = ℕ → UTm

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
untyVar : ∀{Γ t} → Var Γ t → ℕ
untyVar V0 = zero
untyVar (VS x) = suc (untyVar x)

unty : ∀{Γ t} → Tm Γ t → UTm
untyVec : ∀{Γ Σ} → TmVec Γ Σ → UTmVec

unty (var x) = var (untyVar x)
unty (constr s es) = constr s (untyVec es)

untyVec [] = []
untyVec (_∷_ {Δ = Δ} e es) = (unty e , length Δ) ∷ untyVec es

untyRen : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → ℕ → ℕ
untyRen ε = id
untyRen (Keep ξ) = UKeep (untyRen ξ)
untyRen (Drop ξ) = UDrop (untyRen ξ)

-- Type erasure is injective
untyVar-inj≡ : ∀{Γ1 Γ2 t1 t2} {x : Var Γ1 t1} {y : Var Γ2 t2}
              (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
              untyVar x ≡ untyVar y →
              subst₂ Var p q x ≡ y
untyVar-inj≡ {x = V0} {V0} refl refl refl = refl
untyVar-inj≡ {x = VS x} {VS y} refl refl r =
  cong VS (untyVar-inj≡ {x = x} {y} refl refl (suc-injective r))

unty-inj≡ : ∀{Γ1 Γ2 t1 t2} {x : Tm Γ1 t1} {y : Tm Γ2 t2} →
           (p : Γ1 ≡ Γ2) (q : t1 ≡ t2) →
           unty x ≡ unty y →
           subst₂ Tm p q x ≡ y
untyVec-inj≡ : ∀{Γ1 Γ2 Σ1 Σ2} {x : TmVec Γ1 Σ1} {y : TmVec Γ2 Σ2} →
              (p : Γ1 ≡ Γ2) (q : Σ1 ≡ Σ2) →
              untyVec x ≡ untyVec y →
              subst₂ TmVec p q x ≡ y

unty-inj≡ {x = var x} {var y} refl refl r = cong var (untyVar-inj≡ refl refl (unVar-inj r))
unty-inj≡ {x = constr s1 es1} {constr s2 es2} refl q r with unConstr-inj r .fst
unty-inj≡ {x = constr s1 es1} {constr .s1 es2} refl refl r | refl =
  cong (constr s1) (untyVec-inj≡ refl refl (unConstr-inj r .snd))

untyVec-inj≡ {x = []} {[]} refl refl refl = refl
untyVec-inj≡ {x = e1 ∷ es1} {e2 ∷ es2} refl refl r =
  cong₂ _∷_
  (unty-inj≡ refl refl (unCons-inj r .fst))
  (untyVec-inj≡ refl refl (unCons-inj r .snd .snd))

untyRen-inj≡ : ∀{Γ1 Γ1' Γ2 Γ2'} {ξ1 : Ren Γ1 Γ2} {ξ2 : Ren Γ1' Γ2'} →
              (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2') →
              untyRen ξ1 ≗ untyRen ξ2 →
              subst₂ Ren p q ξ1 ≡ ξ2
untyRen-inj≡ {ξ1 = ε} {ε} refl refl r = refl
untyRen-inj≡ {ξ1 = ε} {Drop ξ2} refl refl r = ⊥-elim (0≢1+n (r zero))
untyRen-inj≡ {ξ1 = Keep ξ1} {Keep ξ2} refl refl r =
  cong Keep (untyRen-inj≡ refl refl (suc-injective ∘ r ∘ suc))
untyRen-inj≡ {ξ1 = Keep ξ1} {Drop ξ2} refl refl r = ⊥-elim (0≢1+n (r zero))
untyRen-inj≡ {ξ1 = Drop ξ1} {ε} refl refl r = ⊥-elim (1+n≢0 (r zero))
untyRen-inj≡ {ξ1 = Drop ξ1} {Keep ξ2} refl refl r = ⊥-elim (1+n≢0 (r zero))
untyRen-inj≡ {ξ1 = Drop ξ1} {Drop ξ2} refl refl r =
  cong Drop (untyRen-inj≡ refl refl (suc-injective ∘ r))

untyVar-inj : ∀{Γ t} {x y : Var Γ t} → untyVar x ≡ untyVar y → x ≡ y
untyVar-inj = untyVar-inj≡ refl refl

unty-inj : ∀{Γ t} {x y : Tm Γ t} → unty x ≡ unty y → x ≡ y
unty-inj = unty-inj≡ refl refl

untyVec-inj : ∀{Γ Σ} {x y : TmVec Γ Σ} → untyVec x ≡ untyVec y → x ≡ y
untyVec-inj = untyVec-inj≡ refl refl

untyRen-inj : ∀{Γ1 Γ2} {ξ1 ξ2 : Ren Γ1 Γ2} → untyRen ξ1 ≗ untyRen ξ2 → ξ1 ≡ ξ2
untyRen-inj = untyRen-inj≡ refl refl

-- Type erasure commutes with the extended Keep and Drop operations
untyRen-Keep* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ →
                untyRen (Keep* ξ Δ) ≗ UKeep* (untyRen ξ) (length Δ)
untyRen-Keep* ξ [] = ≗-refl
untyRen-Keep* ξ (t ∷ Δ) = UKeepExt (untyRen-Keep* ξ Δ)

untyRen-Drop* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ →
                untyRen (Drop* ξ Δ) ≗ UDrop* (untyRen ξ) (length Δ)
untyRen-Drop* ξ [] = ≗-refl
untyRen-Drop* ξ (t ∷ Δ) = UDropExt (untyRen-Drop* ξ Δ)

-- Type erasure distributes over renaming
untyVar-distr-ren : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (x : Var Γ1 t) →
                    untyVar (renVar ξ x) ≡ untyRen ξ (untyVar x)
untyVar-distr-ren (Keep ξ) V0 = refl
untyVar-distr-ren (Keep ξ) (VS x) = cong suc (untyVar-distr-ren ξ x)
untyVar-distr-ren (Drop ξ) x = cong suc (untyVar-distr-ren ξ x)

unty-distr-ren : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (e : Tm Γ1 t) →
                 unty (ren ξ e) ≡ renUnty (untyRen ξ) (unty e)
untyVec-distr-ren : ∀{Γ1 Γ2 Σ} (ξ : Ren Γ1 Γ2) (es : TmVec Γ1 Σ) →
                    untyVec (renVec ξ es) ≡ renVecUnty (untyRen ξ) (untyVec es)

unty-distr-ren ξ (var x) = cong var (untyVar-distr-ren ξ x)
unty-distr-ren ξ (constr s es) = cong (constr s) (untyVec-distr-ren ξ es)

untyVec-distr-ren ξ [] = refl
untyVec-distr-ren ξ (_∷_ {Δ = Δ} {Σ = Σ} e es) = cong₃ untyCons
  (unty (ren (Keep* ξ Δ) e)
    ≡⟨ unty-distr-ren (Keep* ξ Δ) e ⟩
  renUnty (untyRen (Keep* ξ Δ)) (unty e)
    ≡⟨ renUntyExt (untyRen-Keep* ξ Δ) (unty e) ⟩
  renUnty (UKeep* (untyRen ξ) (length Δ)) (unty e) ∎)
  refl
  (untyVec-distr-ren ξ es)

-- Type erasure is invariant under propositional equality substitution
subst₂-untyVar : ∀{Γ1 Γ2 t1 t2}
               (p : Γ1 ≡ Γ2) (q : t1 ≡ t2)
               (x : Var Γ1 t1) →
               untyVar x ≡ untyVar (subst₂ Var p q x)
subst₂-untyVar refl refl x = refl

substCtx-untyVar : ∀{Γ1 Γ2 t}
                   (p : Γ1 ≡ Γ2)
                   (x : Var Γ1 t) →
                  untyVar x ≡ untyVar (subst (flip Var t) p x)
substCtx-untyVar refl x = refl

substTy-untyVar : ∀{Γ t1 t2}
                   (p : t1 ≡ t2)
                   (x : Var Γ t1) →
                  untyVar x ≡ untyVar (subst (Var Γ) p x)
substTy-untyVar refl x = refl

subst₂-unty : ∀{Γ1 Γ2 t1 t2}
              (p : Γ1 ≡ Γ2) (q : t1 ≡ t2)
              (x : Tm Γ1 t1) →
              unty x ≡ unty (subst₂ Tm p q x)
subst₂-unty refl refl x = refl

substCtx-unty : ∀{Γ1 Γ2 t}
                (p : Γ1 ≡ Γ2)
                (x : Tm Γ1 t) →
                unty x ≡ unty (subst (flip Tm t) p x)
substCtx-unty refl x = refl

substTy-unty : ∀{Γ t1 t2}
                   (p : t1 ≡ t2)
                   (x : Tm Γ t1) →
                  unty x ≡ unty (subst (Tm Γ) p x)
substTy-unty refl x = refl

subst₂-untyVec : ∀{Γ1 Γ2 Σ1 Σ2}
                (p : Γ1 ≡ Γ2) (q : Σ1 ≡ Σ2)
                (x : TmVec Γ1 Σ1) →
                untyVec x ≡ untyVec (subst₂ TmVec p q x)
subst₂-untyVec refl refl x = refl

substCtx-untyVec : ∀{Γ1 Γ2 Σ}
                   (p : Γ1 ≡ Γ2)
                   (x : TmVec Γ1 Σ) →
                  untyVec x ≡ untyVec (subst (flip TmVec Σ) p x)
substCtx-untyVec refl x = refl

substTy-untyVec : ∀{Γ Σ1 Σ2}
                   (p : Σ1 ≡ Σ2)
                   (x : TmVec Γ Σ1) →
                  untyVec x ≡ untyVec (subst (TmVec Γ) p x)
substTy-untyVec refl x = refl
