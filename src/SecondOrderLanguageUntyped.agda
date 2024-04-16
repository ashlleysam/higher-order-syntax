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

-------------------
-- UNTYPED TERMS --
-------------------

open SecondOrderSignature ⅀
open import SecondOrderLanguage ⅀

data UTm : Set
data UTmVec : Set

-- Untyped terms
data UTm where
  var : ℕ → UTm
  constr : (s : ⅀ .TyShape) (es : UTmVec) → UTm

-- Untyped lists of terms
data UTmVec where
  [] : UTmVec
  _∷_ : (e : UTm) →
        (es : UTmVec) →
        UTmVec

-- Injectivity of constructors
unVar-inj : ∀{x y} → _≡_ {A = UTm} (var x) (var y) → x ≡ y
unVar-inj refl = refl

unConstr-inj : ∀{s1 s2 es1 es2} →
              _≡_ {A = UTm} (constr s1 es1) (constr s2 es2) →
              s1 ≡ s2 × es1 ≡ es2
unConstr-inj refl = refl , refl

unCons-inj : ∀{e1 e2 es1 es2} →
              _≡_ {A = UTmVec} (e1 ∷ es1) (e2 ∷ es2) →
              e1 ≡ e2 × es1 ≡ es2
unCons-inj refl = refl , refl

-- Convert a typed to an untyped representation
untyVar : ∀{Γ t} → Var Γ t → ℕ
untyVar V0 = zero
untyVar (VS x) = suc (untyVar x)

unty : ∀{Γ t} → Tm Γ t → UTm
untyVec : ∀{Γ Σ} → TmVec Γ Σ → UTmVec

unty (var x) = var (untyVar x)
unty (constr s es) = constr s (untyVec es)

untyVec [] = []
untyVec (e ∷ es) = unty e ∷ untyVec es

-- Removing type annotations is injective
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
  (untyVec-inj≡ refl refl (unCons-inj r .snd)) 

untyRen : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → ℕ → ℕ
untyRen ε n = n
untyRen (Keep ξ) zero = zero
untyRen (Keep ξ) (suc n) = suc (untyRen ξ n)
untyRen (Drop ξ) n = suc (untyRen ξ n)

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

-- Removing type annotations is invariant under equality substitution
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

-------------------
-- UNTYPED TERMS --
-------------------
