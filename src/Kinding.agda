{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Data.Unit hiding (_≤_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import KindSignatures

module Kinding (⅀ : KindSignature) where

open KindSignature ⅀
open import Types ⅀
open import TypeContexts ⅀

---------------------------
-- TYPE KINDING JUDGMENT --
---------------------------

KndCtx : Set
KndCtx = List (⅀ .Knd)

-- Typing judgment for variables
data _⊢ₜvar_∶_ : KndCtx → ℕ → ⅀ .Knd → Set where
  ⊢ₜ0 : ∀{Γ κ} → (κ ∷ Γ) ⊢ₜvar 0 ∶ κ
  ⊢ₜS : ∀{Γ κ1 κ2 x} →
        (⊢x : Γ ⊢ₜvar x ∶ κ1) →
        (κ2 ∷ Γ) ⊢ₜvar suc x ∶ κ1

varKinded = _⊢ₜvar_∶_

¬[]⊢ₜx : ∀{κ x} → [] ⊢ₜvar x ∶ κ → ⊥
¬[]⊢ₜx ()

⊢ₜ0-elim
  : ∀{Γ κ} →
    (⊢x : Γ ⊢ₜvar 0 ∶ κ) →
    Σ[ Γ' ∈ _ ]
    Σ[ p ∈ Γ ≡ κ ∷ Γ' ]
    subst (_⊢ₜvar 0 ∶ κ) p ⊢x ≡ ⊢ₜ0
⊢ₜ0-elim {κ ∷ Γ} {κ} ⊢ₜ0 = Γ , refl , refl

getTyVar : ∀{Γ x κ} → Γ ⊢ₜvar x ∶ κ → ℕ
getTyVar {x = x} _ = x

-- The typing judgment for variables is a proposition
⊢ₜvar-isProp : ∀{Γ x κ} → isProp (Γ ⊢ₜvar x ∶ κ)
⊢ₜvar-isProp ⊢ₜ0 ⊢ₜ0 = refl
⊢ₜvar-isProp (⊢ₜS p) (⊢ₜS q) = cong ⊢ₜS (⊢ₜvar-isProp p q)

-- Types of variables are unique
⊢ₜvar-uniq : ∀{Γ x κ1 κ2} → Γ ⊢ₜvar x ∶ κ1 → Γ ⊢ₜvar x ∶ κ2 → κ1 ≡ κ2
⊢ₜvar-uniq ⊢ₜ0 ⊢ₜ0 = refl
⊢ₜvar-uniq (⊢ₜS x) (⊢ₜS y) = ⊢ₜvar-uniq x y

-- Kinding judgment for types
data _⊢ₜ_∶_ (Γ : KndCtx) : Ty → ⅀ .Knd → Set
data _⊢ₜvec_∶_ (Γ : KndCtx) : TyVec → List (KndCtx × (⅀ .Knd)) → Set

data _⊢ₜ_∶_ Γ where
  ⊢ₜvar : ∀{x κ} (⊢x : Γ ⊢ₜvar x ∶ κ) → Γ ⊢ₜ tyVar x ∶ κ
  ⊢ₜtyConstr : ∀{ts} (s : ⅀ .TySymb) →
                (⊢ts : Γ ⊢ₜvec ts ∶ ⅀ .TySig s .fst) →
                Γ ⊢ₜ tyConstr s ts ∶ ⅀ .TySig s .snd

infixr 5 _⊢ₜ∷_
data _⊢ₜvec_∶_ Γ where
  ⊢ₜ[] : Γ ⊢ₜvec [] ∶ []
  _⊢ₜ∷_ : ∀{t ts Δ κ Σ} →
          (⊢t : (Δ ++ Γ) ⊢ₜ t ∶ κ) →
          (⊢ts : Γ ⊢ₜvec ts ∶ Σ) →
          Γ ⊢ₜvec (t , length Δ) ∷ ts ∶ ((Δ , κ) ∷ Σ)

kinded = _⊢ₜ_∶_
vecKinded = _⊢ₜvec_∶_

⊢ₜtyConstr-elim : ∀{Γ s ts κ} →
                  (⊢t : Γ ⊢ₜ tyConstr s ts ∶ κ) →
                  Σ[ ⊢ts ∈ Γ ⊢ₜvec ts ∶ ⅀ .TySig s .fst ]
                  Σ[ p ∈ κ ≡ ⅀ .TySig s .snd ]
                  subst (Γ ⊢ₜ tyConstr s ts ∶_) p ⊢t ≡ ⊢ₜtyConstr s ⊢ts
⊢ₜtyConstr-elim (⊢ₜtyConstr s ⊢ts) = ⊢ts , refl , refl

⊢ₜ∷-elim : ∀{Γ k t ts Σ} →
          (⊢t∷ts : Γ ⊢ₜvec (t , k) ∷ ts ∶ Σ) →
          Σ[ Γ' ∈ _ ]
          Σ[ κ ∈ _ ]
          Σ[ Σ' ∈ _ ]
          Σ[ ⊢t ∈ (Γ' ++ Γ) ⊢ₜ t ∶ κ ]
          Σ[ ⊢ts ∈ Γ ⊢ₜvec ts ∶ Σ' ]
          Σ[ p ∈ Σ ≡ (Γ' , κ) ∷ Σ' ]
          Σ[ q ∈ k ≡ length Γ' ]
          subst₂ (λ x y → Γ ⊢ₜvec (t , x) ∷ ts ∶ y) q p ⊢t∷ts ≡
          ⊢t ⊢ₜ∷ ⊢ts
⊢ₜ∷-elim (_⊢ₜ∷_ {Δ = Δ} {κ = κ} {Σ = Σ} ⊢t ⊢ts) =
  Δ , κ , Σ , ⊢t , ⊢ts , refl , refl , refl

⊢ₜ∷' : ∀{Γ t t' ts Δ κ Σ k Δ++Γ} →
        Δ++Γ ⊢ₜ t' ∶ κ →
        Γ ⊢ₜvec ts ∶ Σ →
        Δ++Γ ≡ Δ ++ Γ →
        k ≡ length Δ →
        t' ≡ t →
        Γ ⊢ₜvec (t , k) ∷ ts ∶ ((Δ , κ) ∷ Σ) 
⊢ₜ∷' ⊢t ⊢ts refl refl refl = ⊢t ⊢ₜ∷ ⊢ts

getTy : ∀{Γ e κ} → Γ ⊢ₜ e ∶ κ → Ty
getTy {e = e} _ = e

getTyVec : ∀{Γ es Σ} → Γ ⊢ₜvec es ∶ Σ → TyVec
getTyVec {es = es} _ = es

-- The typing judgment is a proposition
⊢ₜ-isProp : ∀{Γ e κ} → isProp (Γ ⊢ₜ e ∶ κ)
⊢ₜvec-isProp : ∀{Γ es Σ} → isProp (Γ ⊢ₜvec es ∶ Σ)

⊢ₜ-isProp (⊢ₜvar x) (⊢ₜvar y) = cong ⊢ₜvar (⊢ₜvar-isProp x y)
⊢ₜ-isProp (⊢ₜtyConstr s es1) (⊢ₜtyConstr .s es2) = cong (⊢ₜtyConstr s) (⊢ₜvec-isProp es1 es2)

⊢ₜvec-isProp ⊢ₜ[] ⊢ₜ[] = refl
⊢ₜvec-isProp (e1 ⊢ₜ∷ es1) (e2 ⊢ₜ∷ es2) = cong₂ _⊢ₜ∷_ (⊢ₜ-isProp e1 e2) (⊢ₜvec-isProp es1 es2)

-- Types of terms are unique
⊢ₜ-uniq : ∀{Γ e κ1 κ2} → Γ ⊢ₜ e ∶ κ1 → Γ ⊢ₜ e ∶ κ2 → κ1 ≡ κ2
⊢ₜ-uniq (⊢ₜvar x1) (⊢ₜvar x2) = ⊢ₜvar-uniq x1 x2
⊢ₜ-uniq (⊢ₜtyConstr s es1) (⊢ₜtyConstr .s es2) = refl

-------------------------------------------------
-- CONTEXT AND BINDER WELL-FORMEDNESS JUDGMENT --
-------------------------------------------------

_⊢typ_ : KndCtx → Typ → Set
Γ ⊢typ (κ , t) = Γ ⊢ₜ t ∶ κ

wfTyp = _⊢typ_

⊢typ-isProp : ∀{Γ t} → isProp (Γ ⊢typ t)
⊢typ-isProp = ⊢ₜ-isProp

_⊢ctx_ : KndCtx → Ctx → Set
Γ ⊢ctx Δ = AllElems (λ t → Γ ⊢typ t) Δ

wfCtx = _⊢ctx_

⊢Ctx-map-cong : ∀{a Γ Δ} {A : Set a} {f g : Typ → A} →
                (∀{t} → Γ ⊢typ t → f t ≡ g t) →
                Γ ⊢ctx Δ →
                map f Δ ≡ map g Δ
⊢Ctx-map-cong {Δ = []} f≗g tt = refl
⊢Ctx-map-cong {Δ = t ∷ Δ} f≗g (⊢t , ⊢Δ) =
  cong₂ _∷_ (f≗g ⊢t) (⊢Ctx-map-cong f≗g ⊢Δ)

⊢ctx-isProp : ∀{Γ Δ} → isProp (Γ ⊢ctx Δ)
⊢ctx-isProp {Δ = []} tt tt = refl
⊢ctx-isProp {Δ = t ∷ Δ} (p1 , q1) (p2 , q2) =
  cong₂ _,_ (⊢typ-isProp p1 p2) (⊢ctx-isProp q1 q2)

⊢ctx-++ : ∀{Γ Δ1 Δ2} → Γ ⊢ctx Δ1 → Γ ⊢ctx Δ2 → Γ ⊢ctx (Δ1 ++ Δ2)
⊢ctx-++ {Δ1 = []} ⊢Δ1 ⊢Δ2 = ⊢Δ2
⊢ctx-++ {Δ1 = t ∷ Δ1} (⊢t , ⊢Δ1) ⊢Δ2 = ⊢t , ⊢ctx-++ ⊢Δ1 ⊢Δ2

⊢ctx-++⁻ : ∀{Γ} Δ1 Δ2 → Γ ⊢ctx (Δ1 ++ Δ2) → Γ ⊢ctx Δ1 × Γ ⊢ctx Δ2
⊢ctx-++⁻ [] Δ2 ⊢Δ2 = tt , ⊢Δ2
⊢ctx-++⁻ (t ∷ Δ1) Δ2 (⊢t , ⊢Δ1++Δ2) =
  (⊢t , fst (⊢ctx-++⁻ Δ1 Δ2 ⊢Δ1++Δ2)) ,
  snd (⊢ctx-++⁻ Δ1 Δ2 ⊢Δ1++Δ2)

_⊢bnd_ : KndCtx → Binder → Set
Γ ⊢bnd (Γ' , Δ , t) =
  ((Γ' ++ Γ) ⊢ctx Δ) × ((Γ' ++ Γ) ⊢typ t)

⊢bnd-isProp : ∀{Γ B} → isProp (Γ ⊢bnd B)
⊢bnd-isProp (p1 , q1) (p2 , q2) =
  cong₂ _,_ (⊢ctx-isProp p1 p2) (⊢typ-isProp q1 q2)

wfBinder = _⊢bnd_

_⊢bnds_ : KndCtx → Binders → Set
Γ ⊢bnds Σs = AllElems (λ Σ → Γ ⊢bnd Σ) Σs

⊢bnds-isProp : ∀{Γ Bs} → isProp (Γ ⊢bnds Bs)
⊢bnds-isProp {Bs = []} = ⊤-isProp
⊢bnds-isProp {Bs = (Γ' , Δ , t) ∷ Bs} ((p1 , q1) , r1) ((p2 , q2) , r2) =
  cong₃ (λ x y z → (x , y) , z)
    (⊢ctx-isProp p1 p2)
    (⊢typ-isProp q1 q2)
    (⊢bnds-isProp r1 r2)

wfBinders = _⊢bnds_

⊢Binders-map-cong : ∀{a Γ Σ} {A : Set a} {f g : Binder → A} →
                (∀{b} → Γ ⊢bnd b → f b ≡ g b) →
                Γ ⊢bnds Σ →
                map f Σ ≡ map g Σ
⊢Binders-map-cong {Σ = []} f≗g tt = refl
⊢Binders-map-cong {Σ = b ∷ Σ} f≗g (⊢b , ⊢Σ) =
  cong₂ _∷_ (f≗g ⊢b) (⊢Binders-map-cong f≗g ⊢Σ)

---------------------------------------
-- RENAMING WELL-FORMEDNESS JUDGMENT --
---------------------------------------

TYREN : Ren → KndCtx → KndCtx → Set
TYREN ξ Γ1 Γ2 = ∀{x κ} → Γ1 ⊢ₜvar x ∶ κ → Γ2 ⊢ₜvar ξ x ∶ κ

getRen : ∀{ξ Γ1 Γ2} → TYREN ξ Γ1 Γ2 → Ren
getRen {ξ} ⊢ξ = ξ

TYREN-ext : ∀{Γ1 Γ2 ξ1 ξ2} → ξ1 ≗ ξ2 → TYREN ξ1 Γ1 Γ2 → TYREN ξ2 Γ1 Γ2
TYREN-ext {Γ2 = Γ2} p ⊢ξ {x} {κ} ⊢x =
  subst (λ y → Γ2 ⊢ₜvar y ∶ κ) (p x) (⊢ξ ⊢x)

-- Composition of renamings preserves well-formedness
⊢•ₜ : ∀{Γ1 Γ2 Γ3 ξ1 ξ2} → TYREN ξ1 Γ2 Γ3 → TYREN ξ2 Γ1 Γ2 → TYREN (ξ1 • ξ2) Γ1 Γ3
⊢•ₜ ⊢ξ1 ⊢ξ2 = ⊢ξ1 ∘ ⊢ξ2

⊢TyIdRen : ∀{Γ} → TYREN id Γ Γ
⊢TyIdRen ⊢x = ⊢x

⊢TyKeep : ∀{Γ1 Γ2 ξ κ} → TYREN ξ Γ1 Γ2 → TYREN (Keep ξ) (κ ∷ Γ1) (κ ∷ Γ2)
⊢TyKeep ⊢ξ ⊢ₜ0 = ⊢ₜ0
⊢TyKeep ⊢ξ (⊢ₜS ⊢x) = ⊢ₜS (⊢ξ ⊢x)

⊢TyKeep* : ∀{Γ1 Γ2 ξ} → TYREN ξ Γ1 Γ2 → (Γ' : KndCtx) →
            TYREN (Keep* ξ (length Γ')) (Γ' ++ Γ1) (Γ' ++ Γ2)
⊢TyKeep* ⊢ξ [] = ⊢ξ
⊢TyKeep* ⊢ξ (κ ∷ Γ') = ⊢TyKeep (⊢TyKeep* ⊢ξ Γ')

⊢TyDrop : ∀{Γ1 Γ2 ξ κ} → TYREN ξ Γ1 Γ2 → TYREN (Drop ξ) Γ1 (κ ∷ Γ2)
⊢TyDrop ⊢ξ ⊢x = ⊢ₜS (⊢ξ ⊢x)

⊢TyDrop* : ∀{Γ1 Γ2 ξ} → TYREN ξ Γ1 Γ2 → (Γ' : KndCtx) →
            TYREN (Drop* ξ (length Γ')) Γ1 (Γ' ++ Γ2)
⊢TyDrop* ⊢ξ [] = ⊢ξ
⊢TyDrop* ⊢ξ (κ ∷ Γ') = ⊢TyDrop (⊢TyDrop* ⊢ξ Γ')

-- The action of well-formed renamings preserve kinding
⊢renTy : ∀{Γ1 Γ2 ξ e κ} → TYREN ξ Γ1 Γ2 → Γ1 ⊢ₜ e ∶ κ → Γ2 ⊢ₜ renTy ξ e ∶ κ
⊢renTyVec : ∀{Γ1 Γ2 ξ es Σ} → TYREN ξ Γ1 Γ2 → Γ1 ⊢ₜvec es ∶ Σ → Γ2 ⊢ₜvec renTyVec ξ es ∶ Σ

⊢renTy ⊢ξ (⊢ₜvar ⊢x) = ⊢ₜvar (⊢ξ ⊢x)
⊢renTy ⊢ξ (⊢ₜtyConstr s ⊢es) = ⊢ₜtyConstr s (⊢renTyVec ⊢ξ ⊢es)

⊢renTyVec ⊢ξ ⊢ₜ[] = ⊢ₜ[]
⊢renTyVec ⊢ξ (_⊢ₜ∷_ {Δ = Δ} ⊢e ⊢es) =
  ⊢renTy (⊢TyKeep* ⊢ξ Δ) ⊢e ⊢ₜ∷ ⊢renTyVec ⊢ξ ⊢es

Keep-≗Below : ∀{n ξ1 ξ2} →
              ≗Below n ξ1 ξ2 →
              ≗Below (suc n) (Keep ξ1) (Keep ξ2)
Keep-≗Below ξ1≗ξ2 = refl , ∘-≗Below suc ξ1≗ξ2

Keep*-≗Below : ∀{n ξ1 ξ2} →
                ≗Below n ξ1 ξ2 →
                (k : ℕ) →
                ≗Below (k + n) (Keep* ξ1 k) (Keep* ξ2 k)
Keep*-≗Below ξ1≗ξ2 zero = ξ1≗ξ2
Keep*-≗Below ξ1≗ξ2 (suc k) =
  Keep-≗Below (Keep*-≗Below ξ1≗ξ2 k)

{-
If e is well-typed in context Γ, and
ξ1 and ξ2 are equivalent below the length of Γ,
then e⟨ξ1⟩ ≡ e⟨ξ2⟩.
I.e., all variables in e are below the length of Γ.
-}
⊢TyVar-Below : ∀{A Γ ξ1 ξ2 x κ} →
             ≗Below {A} (length Γ) ξ1 ξ2 →
             Γ ⊢ₜvar x ∶ κ →
             ξ1 x ≡ ξ2 x
⊢TyVar-Below (ξ1₀≡ξ2₀ , ξ1∘suc≗ξ2∘suc) ⊢ₜ0 = ξ1₀≡ξ2₀
⊢TyVar-Below (ξ1₀≡ξ2₀ , ξ1∘suc≗ξ2∘suc) (⊢ₜS ⊢x) = ⊢TyVar-Below ξ1∘suc≗ξ2∘suc ⊢x

⊢renTy-Below : ∀{Γ ξ1 ξ2 e κ} →
             ≗Below (length Γ) ξ1 ξ2 →
             Γ ⊢ₜ e ∶ κ →
             renTy ξ1 e ≡ renTy ξ2 e
⊢renTyVec-Below : ∀{Γ ξ1 ξ2 es Σ} →
                ≗Below (length Γ) ξ1 ξ2 →
                Γ ⊢ₜvec es ∶ Σ →
                renTyVec ξ1 es ≡ renTyVec ξ2 es

⊢renTy-Below ξ1≗ξ2 (⊢ₜvar ⊢x) =
  cong tyVar $ ⊢TyVar-Below ξ1≗ξ2 ⊢x
⊢renTy-Below ξ1≗ξ2 (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr s) $ ⊢renTyVec-Below ξ1≗ξ2 ⊢ts

⊢renTyVec-Below ξ1≗ξ2 ⊢ₜ[] = refl
⊢renTyVec-Below {Γ} {ξ1} {ξ2} ξ1≗ξ2 (_⊢ₜ∷_ {Δ = Δ} ⊢t ⊢ts) =
  cong₂ (λ x y → (x , length Δ) ∷ y)
    (⊢renTy-Below
      (subst (λ x → ≗Below x (Keep* ξ1 (length Δ)) (Keep* ξ2 (length Δ)))
          (sym $ length-++ Δ)
          (Keep*-≗Below ξ1≗ξ2 (length Δ)))
      ⊢t)
    (⊢renTyVec-Below ξ1≗ξ2 ⊢ts)

≗TyRen : (Γ : KndCtx) (ξ1 ξ2 : Ren) → Set
≗TyRen Γ ξ1 ξ2 = ∀{x κ} → Γ ⊢ₜvar x ∶ κ → ξ1 x ≡ ξ2 x

≗TyRen-refl : ∀{Γ ξ} → ≗TyRen Γ ξ ξ
≗TyRen-refl ⊢x = refl

≗TyRen-sym : ∀{Γ ξ1 ξ2} → ≗TyRen Γ ξ1 ξ2 → ≗TyRen Γ ξ2 ξ1
≗TyRen-sym p ⊢x = sym (p ⊢x)

≗TyRen-trans : ∀{Γ ξ1 ξ2 ξ3} →
              ≗TyRen Γ ξ1 ξ2 →
              ≗TyRen Γ ξ2 ξ3 →
              ≗TyRen Γ ξ1 ξ3
≗TyRen-trans p q ⊢x = p ⊢x ∙ q ⊢x

Keep-≗TyRen : ∀{Γ ξ1 ξ2 κ} →
              ≗TyRen Γ ξ1 ξ2 →
              ≗TyRen (κ ∷ Γ) (Keep ξ1) (Keep ξ2)
Keep-≗TyRen ξ1≗ξ2 ⊢ₜ0 = refl
Keep-≗TyRen ξ1≗ξ2 (⊢ₜS ⊢x) = cong suc (ξ1≗ξ2 ⊢x)

Keep*-≗TyRen : ∀{Γ ξ1 ξ2} →
                ≗TyRen Γ ξ1 ξ2 →
                (Γ' : KndCtx) →
                ≗TyRen (Γ' ++ Γ) (Keep* ξ1 (length Γ')) (Keep* ξ2 (length Γ'))
Keep*-≗TyRen ξ1≗ξ2 [] = ξ1≗ξ2
Keep*-≗TyRen {Γ} ξ1≗ξ2 (κ ∷ Γ') =
  Keep-≗TyRen {Γ' ++ Γ} (Keep*-≗TyRen {Γ} ξ1≗ξ2 Γ')

{-
If e is well-typed in context Γ, and
ξ1 and ξ2 are equivalent on variables well-typed in Γ,
then e⟨ξ1⟩ ≡ e⟨ξ2⟩.
-}
⊢renTy-≗TyRen : ∀{Γ ξ1 ξ2 e κ} →
                ≗TyRen Γ ξ1 ξ2 →
                Γ ⊢ₜ e ∶ κ →
                renTy ξ1 e ≡ renTy ξ2 e
⊢renTyVec-≗TyRen : ∀{Γ ξ1 ξ2 es Σ} →
                   ≗TyRen Γ ξ1 ξ2 →
                   Γ ⊢ₜvec es ∶ Σ →
                   renTyVec ξ1 es ≡ renTyVec ξ2 es

⊢renTy-≗TyRen ξ1≗ξ2 (⊢ₜvar ⊢x) = cong tyVar (ξ1≗ξ2 ⊢x)
⊢renTy-≗TyRen ξ1≗ξ2 (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr s) (⊢renTyVec-≗TyRen ξ1≗ξ2 ⊢ts)

⊢renTyVec-≗TyRen ξ1≗ξ2 ⊢ₜ[] = refl
⊢renTyVec-≗TyRen ξ1≗ξ2 (_⊢ₜ∷_ {Δ = Δ} ⊢t ⊢ts) =
  cong₂ (λ x y → (x , length Δ) ∷ y)
    (⊢renTy-≗TyRen (Keep*-≗TyRen ξ1≗ξ2 Δ) ⊢t)
    (⊢renTyVec-≗TyRen ξ1≗ξ2 ⊢ts)

⊢renCtx-≗TyRen : ∀{Γ ξ1 ξ2 Δ} →
                  ≗TyRen Γ ξ1 ξ2 →
                  Γ ⊢ctx Δ →
                  renCtx ξ1 Δ ≡ renCtx ξ2 Δ
⊢renCtx-≗TyRen {Δ = []} ξ1≗ξ2 tt = refl
⊢renCtx-≗TyRen {Δ = (κ , t) ∷ Δ} ξ1≗ξ2 (⊢t , ⊢Δ) =
  cong₂ (λ x y → (κ , x) ∷ y)
    (⊢renTy-≗TyRen ξ1≗ξ2 ⊢t)
    (⊢renCtx-≗TyRen ξ1≗ξ2 ⊢Δ)


{-
Well-kinded types in an empty context have no
variables, so renaming has no effect on them
-}
⊢renTyε : ∀{e κ} →
          (ξ : Ren) →
          [] ⊢ₜ e ∶ κ →
          renTy ξ e ≡ e
⊢renTyε {e} ξ ⊢e =
  ⊢renTy-Below {ξ1 = ξ} {id} tt ⊢e ∙ renTyId e

⊢renTyVecε : ∀{es Σ} →
             (ξ : Ren) →
             [] ⊢ₜvec es ∶ Σ →
             renTyVec ξ es ≡ es
⊢renTyVecε {es} ξ ⊢es =
  ⊢renTyVec-Below {ξ1 = ξ} {id} tt ⊢es ∙ renTyVecId es

⊢TyWk : ∀{Γ t κ1 κ2} → Γ ⊢ₜ t ∶ κ1 → (κ2 ∷ Γ) ⊢ₜ renTy suc t ∶ κ1
⊢TyWk ⊢t = ⊢renTy ⊢ₜS ⊢t

⊢renTyp : ∀{Γ1 Γ2 ξ t} → TYREN ξ Γ1 Γ2 → Γ1 ⊢typ t → Γ2 ⊢typ renTyp ξ t
⊢renTyp ⊢ξ ⊢t = ⊢renTy ⊢ξ ⊢t

⊢renCtx : ∀{Γ1 Γ2 ξ Δ} → TYREN ξ Γ1 Γ2 → Γ1 ⊢ctx Δ → Γ2 ⊢ctx renCtx ξ Δ
⊢renCtx {Δ = []} ⊢ξ tt = tt
⊢renCtx {Δ = t ∷ Δ} ⊢ξ (⊢t , ⊢Δ) = ⊢renTyp ⊢ξ ⊢t , ⊢renCtx ⊢ξ ⊢Δ

⊢renBnd : ∀{Γ1 Γ2 ξ B} → TYREN ξ Γ1 Γ2 → Γ1 ⊢bnd B → Γ2 ⊢bnd renBinder ξ B
⊢renBnd {B = Γ' , Δ , t} ⊢ξ (⊢Δ , ⊢t) =
  ⊢renCtx (⊢TyKeep* ⊢ξ Γ') ⊢Δ ,
  ⊢renTyp (⊢TyKeep* ⊢ξ Γ') ⊢t

⊢renBnds : ∀{Γ1 Γ2 ξ Bs} → TYREN ξ Γ1 Γ2 → Γ1 ⊢bnds Bs → Γ2 ⊢bnds renBinders ξ Bs
⊢renBnds {Bs = []} ⊢ξ tt = tt
⊢renBnds {Bs = B ∷ Bs} ⊢ξ (⊢B , ⊢Bs) =
  ⊢renBnd ⊢ξ ⊢B , ⊢renBnds ⊢ξ ⊢Bs

TYREN⁻ : Ren → KndCtx → KndCtx → Set
TYREN⁻ ξ Γ1 Γ2 = ∀{x κ} → Γ2 ⊢ₜvar ξ x ∶ κ → Γ1 ⊢ₜvar x ∶ κ

TYREN⁻-ext : ∀{Γ1 Γ2 ξ1 ξ2} → ξ1 ≗ ξ2 → TYREN⁻ ξ1 Γ1 Γ2 → TYREN⁻ ξ2 Γ1 Γ2
TYREN⁻-ext {Γ2 = Γ2} p ⊢ξ {x} {κ} ⊢ξx =
  ⊢ξ $ subst (λ y → Γ2 ⊢ₜvar y ∶ κ) (sym $ p x) ⊢ξx

⊢•ₜ⁻ : ∀{Γ1 Γ2 Γ3 ξ1 ξ2} → TYREN⁻ ξ1 Γ2 Γ3 → TYREN⁻ ξ2 Γ1 Γ2 → TYREN⁻ (ξ1 • ξ2) Γ1 Γ3
⊢•ₜ⁻ ⊢ξ1 ⊢ξ2 = ⊢ξ2 ∘ ⊢ξ1

⊢TyIdRen⁻ : ∀{Γ} → TYREN⁻ id Γ Γ
⊢TyIdRen⁻ ⊢x = ⊢x

⊢TyKeep⁻ : ∀{Γ1 Γ2 ξ κ} → TYREN⁻ ξ Γ1 Γ2 → TYREN⁻ (Keep ξ) (κ ∷ Γ1) (κ ∷ Γ2)
⊢TyKeep⁻ ⊢ξ {zero}  ⊢ₜ0 = ⊢ₜ0
⊢TyKeep⁻ ⊢ξ {suc x} {κ} (⊢ₜS ⊢ξx) = ⊢ₜS (⊢ξ ⊢ξx)

⊢TyKeep⁻* : ∀{Γ1 Γ2 ξ} → TYREN⁻ ξ Γ1 Γ2 → (Γ' : KndCtx) →
            TYREN⁻ (Keep* ξ (length Γ')) (Γ' ++ Γ1) (Γ' ++ Γ2)
⊢TyKeep⁻* ⊢ξ [] = ⊢ξ
⊢TyKeep⁻* ⊢ξ (κ ∷ Γ') = ⊢TyKeep⁻ (⊢TyKeep⁻* ⊢ξ Γ')

⊢TyDrop⁻ : ∀{Γ1 Γ2 ξ κ} → TYREN⁻ ξ Γ1 Γ2 → TYREN⁻ (Drop ξ) Γ1 (κ ∷ Γ2)
⊢TyDrop⁻ ⊢ξ (⊢ₜS ⊢ξx) = ⊢ξ ⊢ξx

⊢TyDrop⁻* : ∀{Γ1 Γ2 ξ} → TYREN⁻ ξ Γ1 Γ2 → (Γ' : KndCtx) →
            TYREN⁻ (Drop* ξ (length Γ')) Γ1 (Γ' ++ Γ2)
⊢TyDrop⁻* ⊢ξ [] = ⊢ξ
⊢TyDrop⁻* ⊢ξ (κ ∷ Γ') = ⊢TyDrop⁻ (⊢TyDrop⁻* ⊢ξ Γ')

⊢renTy⁻ : ∀{Γ1 Γ2 ξ e κ} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢ₜ renTy ξ e ∶ κ → Γ1 ⊢ₜ e ∶ κ
⊢renTyVec⁻ : ∀{Γ1 Γ2 ξ es Σ} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢ₜvec renTyVec ξ es ∶ Σ → Γ1 ⊢ₜvec es ∶ Σ

⊢renTy⁻ {e = tyVar x} ⊢ξ (⊢ₜvar ⊢x) = ⊢ₜvar (⊢ξ ⊢x)
⊢renTy⁻ {e = tyConstr s ts} ⊢ξ (⊢ₜtyConstr .s ⊢ts) =
  ⊢ₜtyConstr s (⊢renTyVec⁻ ⊢ξ ⊢ts)

⊢renTyVec⁻ {es = []} ⊢ξ ⊢ₜ[] = ⊢ₜ[]
⊢renTyVec⁻ {es = (t , .(length Γ')) ∷ ts} ⊢ξ (_⊢ₜ∷_ {Δ = Γ'} ⊢t ⊢ₜes) =
  ⊢renTy⁻ (⊢TyKeep⁻* ⊢ξ Γ') ⊢t ⊢ₜ∷ ⊢renTyVec⁻ ⊢ξ ⊢ₜes

⊢renTyp⁻ : ∀{Γ1 Γ2 ξ t} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢typ renTyp ξ t → Γ1 ⊢typ t
⊢renTyp⁻ ⊢ξ ⊢t = ⊢renTy⁻ ⊢ξ ⊢t

⊢renCtx⁻ : ∀{Γ1 Γ2 ξ Δ} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢ctx renCtx ξ Δ → Γ1 ⊢ctx Δ
⊢renCtx⁻ {Δ = []} ⊢ξ tt = tt
⊢renCtx⁻ {Δ = t ∷ Δ} ⊢ξ (⊢t , ⊢Δ) = ⊢renTyp⁻ ⊢ξ ⊢t , ⊢renCtx⁻ ⊢ξ ⊢Δ

⊢renBnd⁻ : ∀{Γ1 Γ2 ξ B} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢bnd renBinder ξ B → Γ1 ⊢bnd B
⊢renBnd⁻ {B = Γ' , Δ , t} ⊢ξ (⊢Δ , ⊢t) =
  ⊢renCtx⁻ (⊢TyKeep⁻* ⊢ξ Γ') ⊢Δ ,
  ⊢renTyp⁻ (⊢TyKeep⁻* ⊢ξ Γ') ⊢t

⊢renBnds⁻ : ∀{Γ1 Γ2 ξ Bs} → TYREN⁻ ξ Γ1 Γ2 → Γ2 ⊢bnds renBinders ξ Bs → Γ1 ⊢bnds Bs
⊢renBnds⁻ {Bs = []} ⊢ξ tt = tt
⊢renBnds⁻ {Bs = B ∷ Bs} ⊢ξ (⊢B , ⊢Bs) =
  ⊢renBnd⁻ ⊢ξ ⊢B , ⊢renBnds⁻ ⊢ξ ⊢Bs

-------------------------------------------
-- SUBSTITUTION WELL-FORMEDNESS JUDGMENT --
-------------------------------------------

TYSUB : TySub → KndCtx → KndCtx → Set
TYSUB σ Γ1 Γ2 = ∀{x κ} → Γ1 ⊢ₜvar x ∶ κ → Γ2 ⊢ₜ σ x ∶ κ

getTySub : ∀{σ Γ1 Γ2} → TYSUB σ Γ1 Γ2 → TySub
getTySub {σ} ⊢σ = σ

TYSUB-ext : ∀{Γ1 Γ2 σ1 σ2} → σ1 ≗ σ2 → TYSUB σ1 Γ1 Γ2 → TYSUB σ2 Γ1 Γ2
TYSUB-ext {Γ2 = Γ2} p ⊢σ {x} {κ} ⊢x =
  subst (λ y → Γ2 ⊢ₜ y ∶ κ) (p x) (⊢σ ⊢x)

-- Composition of renamings and substitutions preserves well-formedness
⊢•◦ₜ : ∀{Γ1 Γ2 Γ3 ξ σ} → TYREN ξ Γ2 Γ3 → TYSUB σ Γ1 Γ2 → TYSUB (ξ •◦ₜ σ) Γ1 Γ3
⊢•◦ₜ ⊢ξ ⊢σ ⊢x = ⊢renTy ⊢ξ (⊢σ ⊢x)

⊢▸ₜ : ∀{Γ1 Γ2 σ e κ} → TYSUB σ Γ1 Γ2 → Γ2 ⊢ₜ e ∶ κ → TYSUB (σ ▸ e) (κ ∷ Γ1) Γ2
⊢▸ₜ ⊢σ ⊢e ⊢ₜ0 = ⊢e
⊢▸ₜ ⊢σ ⊢e (⊢ₜS ⊢x) = ⊢σ ⊢x

⊢TyIdSub : ∀{Γ} → TYSUB tyVar Γ Γ
⊢TyIdSub ⊢x = ⊢ₜvar ⊢x

⊢TyDropSub : ∀{Γ1 Γ2 σ κ} → TYSUB σ Γ1 Γ2 → TYSUB (TyDropSub σ) Γ1 (κ ∷ Γ2)
⊢TyDropSub ⊢σ = ⊢•◦ₜ (⊢TyDrop ⊢TyIdRen) ⊢σ

⊢TyKeepSub : ∀{Γ1 Γ2 σ κ} → TYSUB σ Γ1 Γ2 → TYSUB (TyKeepSub σ) (κ ∷ Γ1) (κ ∷ Γ2)
⊢TyKeepSub ⊢σ = ⊢▸ₜ (⊢TyDropSub ⊢σ) (⊢ₜvar ⊢ₜ0)

⊢ιₜ : ∀{Γ1 Γ2 ξ} → TYREN ξ Γ1 Γ2 → TYSUB (ιₜ ξ) Γ1 Γ2
⊢ιₜ ⊢ξ ⊢x = ⊢ₜvar (⊢ξ ⊢x)

⊢TyKeepSub* : ∀{Γ1 Γ2 σ} → TYSUB σ Γ1 Γ2 → (Γ' : KndCtx) →
              TYSUB (TyKeepSub* σ (length Γ')) (Γ' ++ Γ1) (Γ' ++ Γ2)
⊢TyKeepSub* ⊢σ [] = ⊢σ
⊢TyKeepSub* ⊢σ (κ ∷ Γ') = ⊢TyKeepSub (⊢TyKeepSub* ⊢σ Γ')

⊢TyDropSub* : ∀{Γ1 Γ2 σ} → TYSUB σ Γ1 Γ2 → (Γ' : KndCtx) →
              TYSUB (TyDropSub* σ (length Γ')) Γ1 (Γ' ++ Γ2)
⊢TyDropSub* ⊢σ [] = ⊢σ
⊢TyDropSub* ⊢σ (κ ∷ Γ') = ⊢TyDropSub (⊢TyDropSub* ⊢σ Γ')

-- The action of well-formed substitutions preserve kinding
⊢subTy : ∀{Γ1 Γ2 σ e κ} → TYSUB σ Γ1 Γ2 → Γ1 ⊢ₜ e ∶ κ → Γ2 ⊢ₜ subTy σ e ∶ κ
⊢subTyVec : ∀{Γ1 Γ2 σ es Σ} → TYSUB σ Γ1 Γ2 → Γ1 ⊢ₜvec es ∶ Σ → Γ2 ⊢ₜvec subTyVec σ es ∶ Σ

⊢subTy ⊢σ (⊢ₜvar ⊢x) = ⊢σ ⊢x
⊢subTy ⊢σ (⊢ₜtyConstr s ⊢es) = ⊢ₜtyConstr s (⊢subTyVec ⊢σ ⊢es)

⊢subTyVec ⊢σ ⊢ₜ[] = ⊢ₜ[]
⊢subTyVec ⊢σ (_⊢ₜ∷_ {Δ = Δ} ⊢e ⊢es) =
  ⊢subTy (⊢TyKeepSub* ⊢σ Δ) ⊢e ⊢ₜ∷ ⊢subTyVec ⊢σ ⊢es

⊢subTyp : ∀{Γ1 Γ2 σ t} → TYSUB σ Γ1 Γ2 → Γ1 ⊢typ t → Γ2 ⊢typ subTyp σ t
⊢subTyp ⊢σ ⊢t = ⊢subTy ⊢σ ⊢t

⊢subCtx : ∀{Γ1 Γ2 σ Δ} → TYSUB σ Γ1 Γ2 → Γ1 ⊢ctx Δ → Γ2 ⊢ctx subCtx σ Δ
⊢subCtx {Δ = []} ⊢σ ⊢Δ = tt
⊢subCtx {Δ = t ∷ Δ} ⊢σ (⊢t , ⊢Δ) = ⊢subTyp ⊢σ ⊢t , ⊢subCtx ⊢σ ⊢Δ

⊢subBnd : ∀{Γ1 Γ2 σ B} → TYSUB σ Γ1 Γ2 → Γ1 ⊢bnd B → Γ2 ⊢bnd subBinder σ B
⊢subBnd {B = Γ' , Δ , t} ⊢σ (⊢Δ , ⊢t) =
  ⊢subCtx (⊢TyKeepSub* ⊢σ Γ') ⊢Δ ,
  ⊢subTyp (⊢TyKeepSub* ⊢σ Γ') ⊢t

⊢subBnds : ∀{Γ1 Γ2 σ Bs} → TYSUB σ Γ1 Γ2 → Γ1 ⊢bnds Bs → Γ2 ⊢bnds subBinders σ Bs
⊢subBnds {Bs = []} ⊢σ tt = tt
⊢subBnds {Bs = B ∷ Bs} ⊢σ (⊢B , ⊢Bs) =
  ⊢subBnd ⊢σ ⊢B , ⊢subBnds ⊢σ ⊢Bs

TyKeepSub-≗Below : ∀{n σ1 σ2} →
                  ≗Below n σ1 σ2 →
                  ≗Below (suc n) (TyKeepSub σ1) (TyKeepSub σ2)
TyKeepSub-≗Below σ1≗σ2 = refl , ∘-≗Below (renTy (Drop id)) σ1≗σ2

TyKeepSub*-≗Below : ∀{n σ1 σ2} →
                  (k : ℕ) →
                  ≗Below n σ1 σ2 →
                  ≗Below (k + n) (TyKeepSub* σ1 k) (TyKeepSub* σ2 k)
TyKeepSub*-≗Below zero σ1≗σ2 = σ1≗σ2
TyKeepSub*-≗Below (suc k) σ1≗σ2 =
  TyKeepSub-≗Below (TyKeepSub*-≗Below k σ1≗σ2)

⊢subTy-ext : ∀{Γ σ1 σ2 e κ} →
             ≗Below (length Γ) σ1 σ2 →
             Γ ⊢ₜ e ∶ κ →
             subTy σ1 e ≡ subTy σ2 e
⊢subTyVec-ext : ∀{Γ σ1 σ2 es Σ} →
                ≗Below (length Γ) σ1 σ2 →
                Γ ⊢ₜvec es ∶ Σ →
                subTyVec σ1 es ≡ subTyVec σ2 es

⊢subTy-ext σ1≗σ2 (⊢ₜvar ⊢x) = ⊢TyVar-Below σ1≗σ2 ⊢x
⊢subTy-ext σ1≗σ2 (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr s) $ ⊢subTyVec-ext σ1≗σ2 ⊢ts

⊢subTyVec-ext σ1≗σ2 ⊢ₜ[] = refl
⊢subTyVec-ext {Γ} {σ1} {σ2} σ1≗σ2 (_⊢ₜ∷_ {Δ = Δ} ⊢t ⊢ts) =
  cong₂ (λ x y → (x , length Δ) ∷ y)
    (⊢subTy-ext
      (subst (λ x → ≗Below x (TyKeepSub* σ1 (length Δ)) (TyKeepSub* σ2 (length Δ)))
          (sym $ length-++ Δ)
          (TyKeepSub*-≗Below (length Δ) σ1≗σ2))
      ⊢t)
    (⊢subTyVec-ext σ1≗σ2 ⊢ts)

≗TySub : (Γ : KndCtx) (σ1 σ2 : TySub) → Set
≗TySub Γ σ1 σ2 = ∀{x κ} → Γ ⊢ₜvar x ∶ κ → σ1 x ≡ σ2 x

Drop-≗TySub : ∀{Γ σ1 σ2} →
              ≗TySub Γ σ1 σ2 →
              ≗TySub Γ (TyDropSub σ1) (TyDropSub σ2)
Drop-≗TySub σ1≗σ2 ⊢x = cong (renTy suc) (σ1≗σ2 ⊢x)

Keep-≗TySub : ∀{Γ σ1 σ2 κ} →
              ≗TySub Γ σ1 σ2 →
              ≗TySub (κ ∷ Γ) (TyKeepSub σ1) (TyKeepSub σ2)
Keep-≗TySub σ1≗σ2 ⊢ₜ0 = refl
Keep-≗TySub σ1≗σ2 (⊢ₜS ⊢x) = Drop-≗TySub σ1≗σ2 ⊢x

Keep*-≗TySub : ∀{Γ σ1 σ2} →
                ≗TySub Γ σ1 σ2 →
                (Γ' : KndCtx) →
                ≗TySub (Γ' ++ Γ) (TyKeepSub* σ1 (length Γ')) (TyKeepSub* σ2 (length Γ'))
Keep*-≗TySub σ1≗σ2 [] = σ1≗σ2
Keep*-≗TySub {Γ} σ1≗σ2 (κ ∷ Γ') =
  Keep-≗TySub {Γ' ++ Γ} (Keep*-≗TySub {Γ} σ1≗σ2 Γ')

{-
If e is well-typed in context Γ, and
σ1 and σ2 are equivalent on variables well-typed in Γ,
then e⟨σ1⟩ ≡ e⟨σ2⟩.
-}
⊢subTy-≗TySub : ∀{Γ σ1 σ2 e κ} →
                ≗TySub Γ σ1 σ2 →
                Γ ⊢ₜ e ∶ κ →
                subTy σ1 e ≡ subTy σ2 e
⊢subTyVec-≗TySub : ∀{Γ σ1 σ2 es Σ} →
                   ≗TySub Γ σ1 σ2 →
                   Γ ⊢ₜvec es ∶ Σ →
                   subTyVec σ1 es ≡ subTyVec σ2 es

⊢subTy-≗TySub σ1≗σ2 (⊢ₜvar ⊢x) = σ1≗σ2 ⊢x
⊢subTy-≗TySub σ1≗σ2 (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr s) (⊢subTyVec-≗TySub σ1≗σ2 ⊢ts)

⊢subTyVec-≗TySub σ1≗σ2 ⊢ₜ[] = refl
⊢subTyVec-≗TySub σ1≗σ2 (_⊢ₜ∷_ {Δ = Δ} ⊢t ⊢ts) =
  cong₂ (λ x y → (x , length Δ) ∷ y)
    (⊢subTy-≗TySub (Keep*-≗TySub σ1≗σ2 Δ) ⊢t)
    (⊢subTyVec-≗TySub σ1≗σ2 ⊢ts)

{-
Well-kinded types in an empty context have no
variables, so substitution has no effect on them
-}
⊢subTyε : ∀{e κ} →
          (σ : TySub) →
          [] ⊢ₜ e ∶ κ →
          subTy σ e ≡ e
⊢subTyε {e} σ ⊢e =
  ⊢subTy-ext {σ1 = σ} {tyVar} tt ⊢e ∙ subTyId e

⊢subTyVecε : ∀{es Σ} →
             (σ : TySub) →
             [] ⊢ₜvec es ∶ Σ →
             subTyVec σ es ≡ es
⊢subTyVecε {es} σ ⊢es = 
  ⊢subTyVec-ext {σ1 = σ} {tyVar} tt ⊢es ∙ subTyVecId es

{-
squash k keeps all variables ≤ k unchanged,
and decreases by 1 all variables > k, effectively
removing the variable k
-}
squash : ℕ → Ren
squash k = Keep* pred k

Keep*-squash : ∀{i} (k : ℕ) →
               squash (k + i) ≗
               Keep* (squash i) k
Keep*-squash zero x = refl
Keep*-squash (suc k) = Keep-ext (Keep*-squash k)

-- Removes the given index of a list
removeIdx : ∀{a} {A : Set a} →
            List A → ℕ → List A
removeIdx [] i = []
removeIdx (x ∷ xs) zero = xs
removeIdx (x ∷ xs) (suc i) = x ∷ removeIdx xs i

removeIdx-++ : ∀{a i} {A : Set a} (xs : List A) {ys : List A} →
                removeIdx (xs ++ ys) (length xs + i) ≡
                xs ++ removeIdx ys i
removeIdx-++ [] = refl
removeIdx-++ (x ∷ xs) = cong (x ∷_) (removeIdx-++ xs)

{-
If a variable doesn't occur freely in a type,
then we can safely remove it from the context
-}
⊢squashTyVar
  : ∀{Γ x κ i} →
    i ≢ x →
    Γ ⊢ₜvar x ∶ κ →
    removeIdx Γ i ⊢ₜvar squash i x ∶ κ
⊢squashTyVar {κ ∷ Γ} {zero} {i = zero} 0≢0 ⊢x = ⊥-elim $ 0≢0 refl
⊢squashTyVar {κ ∷ Γ} {zero} {i = suc i} suc-i≢0 ⊢ₜ0 = ⊢ₜ0
⊢squashTyVar {κ ∷ Γ} {suc x} {i = zero} 0≢suc-x (⊢ₜS ⊢x) = ⊢x
⊢squashTyVar {κ ∷ Γ} {suc x} {i = suc i} suc-i≢suc-x (⊢ₜS ⊢x) =
  ⊢ₜS (⊢squashTyVar {Γ} {x} {i = i} (λ i≡x → suc-i≢suc-x (cong suc i≡x)) ⊢x)

⊢squashTy
  : ∀{Γ t κ i} →
    notFreeInTy i t →
    Γ ⊢ₜ t ∶ κ →
    removeIdx Γ i ⊢ₜ renTy (squash i) t ∶ κ
⊢squashTyVec
  : ∀{Γ ts κ i} →
    notFreeInTyVec i ts →
    Γ ⊢ₜvec ts ∶ κ →
    removeIdx Γ i ⊢ₜvec renTyVec (squash i) ts ∶ κ

⊢squashTy i≢x (⊢ₜvar ⊢x) = ⊢ₜvar (⊢squashTyVar i≢x ⊢x)
⊢squashTy i∉ts (⊢ₜtyConstr s ⊢ts) =
  ⊢ₜtyConstr s (⊢squashTyVec i∉ts ⊢ts)

⊢squashTyVec tt ⊢ₜ[] = ⊢ₜ[]
⊢squashTyVec (i∉t , i∉ts) (_⊢ₜ∷_ {t} {Δ = Δ} {κ} ⊢t ⊢ts) =
  subst₂ (λ x y → x ⊢ₜ y ∶ κ)
    (removeIdx-++ Δ)
    (renTy-ext (Keep*-squash (length Δ)) t)
    (⊢squashTy i∉t ⊢t)
  ⊢ₜ∷ ⊢squashTyVec i∉ts ⊢ts

