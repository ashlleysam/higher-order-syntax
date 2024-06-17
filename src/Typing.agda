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
open import KindSignatures
open import TypeSignatures

module Typing (⅀ : TypeSignature) where

open import Types (⅀ .⅀ₖ)
open import TypeContexts (⅀ .⅀ₖ)
open import Kinding (⅀ .⅀ₖ)
open import Terms ⅀

---------------------------
-- TERM TYPING JUDGMENT --
---------------------------

-- Typing judgment for variables
data _⨾_⊢var_∶_ : KndCtx → Ctx → ℕ → Typ → Set where
  ⊢0 : ∀{Γ Δ t}
        (⊢Δ : Γ ⊢ctx Δ)
        (⊢t : Γ ⊢typ t) →
        Γ ⨾ t ∷ Δ ⊢var 0 ∶ t
  ⊢S : ∀{Γ Δ t1 t2 x}
       (⊢x : Γ ⨾ Δ ⊢var x ∶ t1)
       (⊢t2 : Γ ⊢typ t2) →
       Γ ⨾ (t2 ∷ Δ) ⊢var suc x ∶ t1

varTyped = _⨾_⊢var_∶_

⊢renTypVar : ∀{ξ Γ1 Γ2 Δ t x} →
              TYREN ξ Γ1 Γ2 →
              Γ1 ⨾ Δ ⊢var x ∶ t →
              Γ2 ⨾ renCtx ξ Δ ⊢var x ∶ renTyp ξ t
⊢renTypVar ⊢ξ (⊢0 ⊢Δ ⊢t) = ⊢0 (⊢renCtx ⊢ξ ⊢Δ) (⊢renTyp ⊢ξ ⊢t)
⊢renTypVar ⊢ξ (⊢S ⊢x ⊢t2) = ⊢S (⊢renTypVar ⊢ξ ⊢x) (⊢renTyp ⊢ξ ⊢t2)

⊢subTypVar : ∀{σ Γ1 Γ2 Δ t x} →
              TYSUB σ Γ1 Γ2 →
              Γ1 ⨾ Δ ⊢var x ∶ t →
              Γ2 ⨾ subCtx σ Δ ⊢var x ∶ subTyp σ t
⊢subTypVar ⊢σ (⊢0 ⊢Δ ⊢t) = ⊢0 (⊢subCtx ⊢σ ⊢Δ) (⊢subTyp ⊢σ ⊢t)
⊢subTypVar ⊢σ (⊢S ⊢x ⊢t2) = ⊢S (⊢subTypVar ⊢σ ⊢x) (⊢subTyp ⊢σ ⊢t2)

-- The typing judgment for variables is a proposition
⊢var-isProp : ∀{Γ Δ x t} → isProp (Γ ⨾ Δ ⊢var x ∶ t)
⊢var-isProp (⊢0 ⊢Δ ⊢t) (⊢0 ⊢Δ' ⊢t') =
  cong₂ ⊢0 (⊢ctx-isProp ⊢Δ ⊢Δ') (⊢typ-isProp ⊢t ⊢t')
⊢var-isProp (⊢S ⊢x ⊢t2) (⊢S ⊢x' ⊢t2') =
  cong₂ ⊢S (⊢var-isProp ⊢x ⊢x') (⊢typ-isProp ⊢t2 ⊢t2')

-- Types of variables are unique
⊢var-uniq : ∀{Γ Δ x t1 t2} → Γ ⨾ Δ ⊢var x ∶ t1 → Γ ⨾ Δ ⊢var x ∶ t2 → t1 ≡ t2
⊢var-uniq (⊢0 ⊢Δ ⊢t1) (⊢0 ⊢Δ' ⊢t1') = refl
⊢var-uniq (⊢S ⊢x ⊢t3) (⊢S ⊢x' ⊢t3') = ⊢var-uniq ⊢x ⊢x'

-- Typing judgment for terms
data _⨾_⊢_∶_ (Γ : KndCtx) (Δ : Ctx) : (e : Tm) (t : Typ) → Set
data _⨾_⊢vec_∶_ (Γ : KndCtx) (Δ : Ctx) : (es : TmVec) (Σ : Binders) → Set

data _⨾_⊢_∶_ Γ Δ where
  ⊢var : ∀{x t} (⊢x : Γ ⨾ Δ ⊢var x ∶ t) → Γ ⨾ Δ ⊢ var x ∶ t
  ⊢constr : ∀{ts es}
            (s : ⅀ .TmSymb)
            (⊢ts : Γ ⊢ₜvec ts ∶ ⅀ .TmTySig s)
            (⊢es : Γ ⨾ Δ ⊢vec es ∶ ⅀ .TmSig s Γ ts .fst) →
            Γ ⨾ Δ ⊢ constr s ts es ∶ ⅀ .TmSig s Γ ts .snd

infixr 5 _⊢∷_
data _⨾_⊢vec_∶_ Γ Δ where
  ⊢[] : (⊢Δ : Γ ⊢ctx Δ) →
        Γ ⨾ Δ ⊢vec [] ∶ []
  _⊢∷_ : ∀{e es Γ' Δ' t Σ} →
        (⊢e : (Γ' ++ Γ) ⨾ (Δ' ++ renCtx (Drop* id (length Γ')) Δ) ⊢ e ∶ t) →
        (⊢es : Γ ⨾ Δ ⊢vec es ∶ Σ) →
        Γ ⨾ Δ ⊢vec (e , length Γ' , length Δ') ∷ es ∶ ((Γ' , Δ' , t) ∷ Σ)

typed = _⨾_⊢_∶_
vecTyped = _⨾_⊢vec_∶_

⊢∷' : ∀{Γ e e' es Δ Δ' t t' Σ Σ' m n Γ' Γ'++Γ Δ'++Δ} →
        Γ'++Γ ⨾ Δ'++Δ ⊢ e' ∶ t' →
        Γ ⨾ Δ ⊢vec es ∶ Σ' →
        Γ'++Γ ≡ Γ' ++ Γ →
        Δ'++Δ ≡ Δ' ++ renCtx (Drop* id (length Γ')) Δ →
        m ≡ length Γ' →
        n ≡ length Δ' →
        Σ' ≡ Σ →
        t' ≡ t →
        e' ≡ e →
        Γ ⨾ Δ ⊢vec (e , m , n) ∷ es ∶ ((Γ' , Δ' , t) ∷ Σ) 
⊢∷' ⊢t ⊢ts refl refl refl refl refl refl refl = ⊢t ⊢∷ ⊢ts

⊢tyRen : ∀{ξ Γ1 Γ2 Δ t e} →
            TYREN ξ Γ1 Γ2 →
            Γ1 ⨾ Δ ⊢ e ∶ t →
            Γ2 ⨾ renCtx ξ Δ ⊢ tyRen ξ e ∶ renTyp ξ t
⊢tyRenVec : ∀{ξ Γ1 Γ2 Δ Σ es} →
              TYREN ξ Γ1 Γ2 →
              Γ1 ⨾ Δ ⊢vec es ∶ Σ →
              Γ2 ⨾ renCtx ξ Δ ⊢vec tyRenVec ξ es ∶ renBinders ξ Σ

⊢tyRen ⊢ξ (⊢var ⊢x) = ⊢var (⊢renTypVar ⊢ξ ⊢x)
⊢tyRen {ξ} {Γ1} {Γ2} {Δ} ⊢ξ (⊢constr {ts = ts} {es} s ⊢ts ⊢es) =
  subst (λ x → Γ2 ⨾ renCtx ξ Δ ⊢ tyRen ξ (constr s ts es) ∶ x)
    (ren-comm-TmSig-snd ⅀ s ⊢ξ ⊢ts) $
    ⊢constr s (⊢renTyVec ⊢ξ ⊢ts) $
    subst (λ x → Γ2 ⨾ renCtx ξ Δ ⊢vec tyRenVec ξ es ∶ x)
      (sym $ ren-comm-TmSig-fst ⅀ s ⊢ξ ⊢ts)
      (⊢tyRenVec ⊢ξ ⊢es)

⊢tyRenVec ⊢ξ (⊢[] ⊢Δ) = ⊢[] (⊢renCtx ⊢ξ ⊢Δ)
⊢tyRenVec {ξ} {Γ1} {Δ = Δ} ⊢ξ (_⊢∷_ {Γ' = Γ'} {Δ'} {t} ⊢e ⊢es) =
  let eq1 : renCtx (Keep* ξ (length Γ')) (Δ' ++ renCtx (Drop* id (length Γ')) Δ)
            ≡ renCtx (Keep* ξ (length Γ')) Δ' ++ renCtx (Drop* id (length Γ')) (renCtx ξ Δ)
      eq1 =
        renCtx (Keep* ξ (length Γ')) (Δ' ++ renCtx (Drop* id (length Γ')) Δ)
          ≡⟨ map-++-commute (renTyp (Keep* ξ (length Γ'))) Δ'
              (renCtx (Drop* id (length Γ')) Δ) ⟩
        renCtx (Keep* ξ (length Γ')) Δ'
          ++ renCtx (Keep* ξ (length Γ')) (renCtx (Drop* id (length Γ')) Δ)
          ≡⟨ (cong (renCtx (Keep* ξ (length Γ')) Δ' ++_) $
              renCtx• (Keep* ξ (length Γ')) (Drop* id (length Γ')) Δ) ⟩
        renCtx (Keep* ξ (length Γ')) Δ'
          ++ renCtx (Keep* ξ (length Γ') • Drop* id (length Γ')) Δ
          ≡⟨ (cong (renCtx (Keep* ξ (length Γ')) Δ' ++_) $
                renCtx-ext (Keep*•Drop* ξ id (length Γ')) Δ) ⟩
        renCtx (Keep* ξ (length Γ')) Δ'
          ++ renCtx (Drop* ξ (length Γ')) Δ
          ≡⟨ (cong (renCtx (Keep* ξ (length Γ')) Δ' ++_) $
              renCtx-ext (λ x → sym $ Drop*• id ξ (length Γ') x) Δ) ⟩
        renCtx (Keep* ξ (length Γ')) Δ'
          ++ renCtx (Drop* id (length Γ') • ξ) Δ
          ≡⟨ (cong (renCtx (Keep* ξ (length Γ')) Δ' ++_) $
              sym $ renCtx• (Drop* id (length Γ')) ξ Δ) ⟩
        renCtx (Keep* ξ (length Γ')) Δ'
          ++ renCtx (Drop* id (length Γ')) (renCtx ξ Δ) ∎
      eq2 : length Δ' ≡ length (map (renTyp (Keep* ξ (length Γ'))) Δ')
      eq2 = sym $ length-map (renTyp (Keep* ξ (length Γ'))) Δ'
  in ⊢∷' (⊢tyRen (⊢TyKeep* ⊢ξ Γ') ⊢e)
    (⊢tyRenVec ⊢ξ ⊢es) refl eq1 refl eq2 refl refl refl

⊢tySub : ∀{σ Γ1 Γ2 Δ t e} →
            TYSUB σ Γ1 Γ2 →
            Γ1 ⨾ Δ ⊢ e ∶ t →
            Γ2 ⨾ subCtx σ Δ ⊢ tySub σ e ∶ subTyp σ t
⊢tySubVec : ∀{σ Γ1 Γ2 Δ Σ es} →
              TYSUB σ Γ1 Γ2 →
              Γ1 ⨾ Δ ⊢vec es ∶ Σ →
              Γ2 ⨾ subCtx σ Δ ⊢vec tySubVec σ es ∶ subBinders σ Σ

⊢tySub ⊢σ (⊢var ⊢x) = ⊢var (⊢subTypVar ⊢σ ⊢x)
⊢tySub {σ} {Γ1} {Γ2} {Δ} ⊢σ (⊢constr {ts = ts} {es} s ⊢ts ⊢es) =
  subst (λ x → Γ2 ⨾ subCtx σ Δ ⊢ tySub σ (constr s ts es) ∶ x)
    (sub-comm-TmSig-snd ⅀ s ⊢σ ⊢ts) $
    ⊢constr s (⊢subTyVec ⊢σ ⊢ts) $
    subst (λ x → Γ2 ⨾ subCtx σ Δ ⊢vec tySubVec σ es ∶ x)
      (sym $ sub-comm-TmSig-fst ⅀ s ⊢σ ⊢ts)
      (⊢tySubVec ⊢σ ⊢es)

⊢tySubVec ⊢σ (⊢[] ⊢Δ) = ⊢[] (⊢subCtx ⊢σ ⊢Δ)
⊢tySubVec {σ} {Γ1} {Δ = Δ} ⊢σ (_⊢∷_ {Γ' = Γ'} {Δ'} {t} ⊢e ⊢es) =
  let eq1 : subCtx (TyKeepSub* σ (length Γ')) (Δ' ++ renCtx (Drop* id (length Γ')) Δ)
            ≡ subCtx (TyKeepSub* σ (length Γ')) Δ' ++ renCtx (Drop* id (length Γ')) (subCtx σ Δ)
      eq1 = 
        subCtx (TyKeepSub* σ (length Γ')) (Δ' ++ renCtx (Drop* id (length Γ')) Δ)
          ≡⟨ map-++-commute (subTyp (TyKeepSub* σ (length Γ'))) Δ'
              (renCtx (Drop* id (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyKeepSub* σ (length Γ')) (renCtx (Drop* id (length Γ')) Δ)
          ≡⟨ (cong (λ x → subCtx (TyKeepSub* σ (length Γ')) Δ'
              ++ subCtx (TyKeepSub* σ (length Γ')) x) $
              sym $ subCtxιₜ (Drop* id (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyKeepSub* σ (length Γ')) (subCtx (ιₜ (Drop* id (length Γ'))) Δ)
          ≡⟨ (cong (λ x → subCtx (TyKeepSub* σ (length Γ')) Δ'
              ++ subCtx (TyKeepSub* σ (length Γ')) x) $
               subCtx-ext (Drop*ιₜ id (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyKeepSub* σ (length Γ')) (subCtx (TyDropSub* tyVar (length Γ')) Δ)
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
                subCtx◦ₜ (TyKeepSub* σ (length Γ')) (TyDropSub* tyVar (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyKeepSub* σ (length Γ') ◦ₜ TyDropSub* tyVar (length Γ')) Δ
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
              subCtx-ext (Keep*◦ₜDrop* σ tyVar (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyDropSub* σ (length Γ')) Δ
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
                subCtx-ext (TyDropSub*-ext (λ x → sym $ Id◦ₜ σ x) (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyDropSub* (tyVar ◦ₜ σ) (length Γ')) Δ
          ≡⟨ (sym $ cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
                subCtx-ext (Drop*◦ₜ tyVar σ (length Γ')) Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyDropSub* tyVar (length Γ') ◦ₜ σ) Δ
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
              sym $ subCtx◦ₜ (TyDropSub* tyVar (length Γ')) σ Δ) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (TyDropSub* tyVar (length Γ')) (subCtx σ Δ)
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
            subCtx-ext (λ x → sym $ Drop*ιₜ id (length Γ') x) (subCtx σ Δ)) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ subCtx (ιₜ (Drop* id (length Γ'))) (subCtx σ Δ)
          ≡⟨ (cong (subCtx (TyKeepSub* σ (length Γ')) Δ' ++_) $
                subCtxιₜ (Drop* id (length Γ')) (subCtx σ Δ)) ⟩
        subCtx (TyKeepSub* σ (length Γ')) Δ'
          ++ renCtx (Drop* id (length Γ')) (subCtx σ Δ) ∎
      eq2 : length Δ' ≡ length (subCtx (TyKeepSub* σ (length Γ')) Δ')
      eq2 = sym $ length-map (subTyp (TyKeepSub* σ (length Γ'))) Δ'
  in ⊢∷' (⊢tySub (⊢TyKeepSub* ⊢σ Γ') ⊢e)
    (⊢tySubVec ⊢σ ⊢es) refl eq1 refl eq2 refl refl refl

-- The typing judgment is a proposition
⊢-isProp : ∀{Γ Δ e t} → isProp (Γ ⨾ Δ ⊢ e ∶ t)
⊢vec-isProp : ∀{Γ Δ es Σ} → isProp (Γ ⨾ Δ ⊢vec es ∶ Σ)

⊢-isProp (⊢var ⊢x) (⊢var ⊢x') = cong ⊢var (⊢var-isProp ⊢x ⊢x')
⊢-isProp (⊢constr s ⊢ts ⊢es) (⊢constr .s ⊢ts' ⊢es') =
  cong₂ (⊢constr s) (⊢ₜvec-isProp ⊢ts ⊢ts') (⊢vec-isProp ⊢es ⊢es')

⊢vec-isProp (⊢[] ⊢Δ) (⊢[] ⊢Δ') = cong ⊢[] (⊢ctx-isProp ⊢Δ ⊢Δ')
⊢vec-isProp (⊢e ⊢∷ ⊢es) (⊢e' ⊢∷ ⊢es') =
  cong₂ _⊢∷_ (⊢-isProp ⊢e ⊢e') (⊢vec-isProp ⊢es ⊢es')

-- Types of terms are unique
⊢-uniq : ∀{Γ Δ e t1 t2} → Γ ⨾ Δ ⊢ e ∶ t1 → Γ ⨾ Δ ⊢ e ∶ t2 → t1 ≡ t2
⊢-uniq (⊢var ⊢x) (⊢var ⊢x') = ⊢var-uniq ⊢x ⊢x'
⊢-uniq (⊢constr s ⊢ts ⊢es) (⊢constr .s ⊢ts' ⊢es') = refl

-- Relations between judgments
⊢var⇒⊢ctx : ∀{Γ Δ x t} → Γ ⨾ Δ ⊢var x ∶ t → Γ ⊢ctx Δ
⊢var⇒⊢ctx (⊢0 ⊢Δ ⊢t) = ⊢t , ⊢Δ
⊢var⇒⊢ctx (⊢S ⊢x ⊢t2) = ⊢t2 , ⊢var⇒⊢ctx ⊢x

⊢var⇒⊢typ : ∀{Γ Δ x t} → Γ ⨾ Δ ⊢var x ∶ t → Γ ⊢typ t
⊢var⇒⊢typ (⊢0 ⊢Δ ⊢t) = ⊢t
⊢var⇒⊢typ (⊢S ⊢x ⊢t2) = ⊢var⇒⊢typ ⊢x

⊢vec⇒⊢ctx : ∀{Γ Δ es Σ} → Γ ⨾ Δ ⊢vec es ∶ Σ → Γ ⊢ctx Δ
⊢vec⇒⊢ctx (⊢[] ⊢Δ) = ⊢Δ
⊢vec⇒⊢ctx (⊢e ⊢∷ ⊢es) = ⊢vec⇒⊢ctx ⊢es

⊢⇒⊢ctx : ∀{Γ Δ e t} → Γ ⨾ Δ ⊢ e ∶ t → Γ ⊢ctx Δ
⊢⇒⊢ctx (⊢var ⊢x) = ⊢var⇒⊢ctx ⊢x
⊢⇒⊢ctx (⊢constr s ⊢ts ⊢es) = ⊢vec⇒⊢ctx ⊢es

⊢⇒⊢typ : ∀{Γ Δ e t} → Γ ⨾ Δ ⊢ e ∶ t → Γ ⊢typ t
⊢⇒⊢typ (⊢var ⊢x) = ⊢var⇒⊢typ ⊢x
⊢⇒⊢typ (⊢constr s ⊢ts ⊢es) = ⅀ .⊢TmSig-snd s ⊢ts

⊢vec⇒⊢bnds : ∀{Γ Δ es Σ} → Γ ⨾ Δ ⊢vec es ∶ Σ → Γ ⊢bnds Σ
⊢vec⇒⊢bnds (⊢[] ⊢Δ) = tt
⊢vec⇒⊢bnds {Δ = Δ} (_⊢∷_ {Γ' = Γ'} {Δ'} ⊢e ⊢es) =
  (⊢ctx-++⁻ Δ' (renCtx (Drop* id (length Γ')) Δ) (⊢⇒⊢ctx ⊢e) .fst
    , ⊢⇒⊢typ ⊢e) ,
  ⊢vec⇒⊢bnds ⊢es

---------------------------------------
-- RENAMING WELL-FORMEDNESS JUDGMENT --
---------------------------------------

data REN (ξ : Ren) (Γ : KndCtx) : Ctx → Ctx → Set where
  ⊢IdRen≗ : ∀{Δ} (ξ≗id : ξ ≗ id) (⊢Δ : Γ ⊢ctx Δ) → REN ξ Γ Δ Δ
  ⊢Keep≗ : ∀{Δ1 Δ2 t ξ'} (ξ≗Keep : ξ ≗ Keep ξ') (⊢ξ' : REN ξ' Γ Δ1 Δ2) (⊢t : Γ ⊢typ t) → REN ξ Γ (t ∷ Δ1) (t ∷ Δ2)
  ⊢Drop≗ : ∀{Δ1 Δ2 t ξ'} (ξ≗Drop : ξ ≗ Drop ξ') (⊢ξ' : REN ξ' Γ Δ1 Δ2) (⊢t : Γ ⊢typ t) → REN ξ Γ Δ1 (t ∷ Δ2)

REN⇒⊢ctx₁ : ∀{ξ Γ Δ1 Δ2} → REN ξ Γ Δ1 Δ2 → Γ ⊢ctx Δ1
REN⇒⊢ctx₁ (⊢IdRen≗ ξ≗id ⊢Δ) = ⊢Δ
REN⇒⊢ctx₁ (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) = ⊢t , REN⇒⊢ctx₁ ⊢ξ
REN⇒⊢ctx₁ (⊢Drop≗ ξ≗Drop ⊢ξ ⊢t) = REN⇒⊢ctx₁ ⊢ξ

REN⇒⊢ctx₂ : ∀{ξ Γ Δ1 Δ2} → REN ξ Γ Δ1 Δ2 → Γ ⊢ctx Δ2
REN⇒⊢ctx₂ (⊢IdRen≗ ξ≗id ⊢Δ) = ⊢Δ
REN⇒⊢ctx₂ (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) = ⊢t , REN⇒⊢ctx₂ ⊢ξ
REN⇒⊢ctx₂ (⊢Drop≗ ξ≗Drop ⊢ξ ⊢t) = ⊢t , REN⇒⊢ctx₂ ⊢ξ

⊢IdRen : ∀{Γ Δ} (⊢Δ : Γ ⊢ctx Δ) → REN id Γ Δ Δ
⊢IdRen ⊢Δ = ⊢IdRen≗ ≗-refl ⊢Δ

⊢Keep : ∀{ξ Γ Δ1 Δ2 t} → REN ξ Γ Δ1 Δ2 → Γ ⊢typ t → REN (Keep ξ) Γ (t ∷ Δ1) (t ∷ Δ2)
⊢Keep ⊢ξ ⊢t = ⊢Keep≗ ≗-refl ⊢ξ ⊢t

⊢Keep* : ∀{ξ Γ Δ1 Δ2 Δ'} → REN ξ Γ Δ1 Δ2 → Γ ⊢ctx Δ' → REN (Keep* ξ (length Δ')) Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
⊢Keep* {Δ' = []} ⊢ξ tt = ⊢ξ
⊢Keep* {Δ' = t ∷ Δ'} ⊢ξ (⊢t , ⊢Δ') = ⊢Keep (⊢Keep* ⊢ξ ⊢Δ') ⊢t

⊢Drop : ∀{ξ Γ Δ1 Δ2 t} → REN ξ Γ Δ1 Δ2 → Γ ⊢typ t → REN (Drop ξ) Γ Δ1 (t ∷ Δ2)
⊢Drop ⊢ξ ⊢t = ⊢Drop≗ ≗-refl ⊢ξ ⊢t

⊢Drop* : ∀{ξ Γ Δ1 Δ2 Δ'} → REN ξ Γ Δ1 Δ2 → Γ ⊢ctx Δ' → REN (Drop* ξ (length Δ')) Γ Δ1 (Δ' ++ Δ2)
⊢Drop* {Δ' = []} ⊢ξ tt = ⊢ξ
⊢Drop* {Δ' = t ∷ Δ'} ⊢ξ (⊢t , ⊢Δ') = ⊢Drop (⊢Drop* ⊢ξ ⊢Δ') ⊢t

REN-ext : ∀{Γ Δ1 Δ2 ξ1 ξ2} → ξ1 ≗ ξ2 → REN ξ1 Γ Δ1 Δ2 → REN ξ2 Γ Δ1 Δ2
REN-ext ξ1≗ξ2 (⊢IdRen≗ ξ≗id ⊢Δ) = ⊢IdRen≗ (λ x → sym (ξ1≗ξ2 x) ∙ ξ≗id x) ⊢Δ
REN-ext ξ1≗ξ2 (⊢Keep≗ ξ≗Keep ⊢ξ1' ⊢t) = ⊢Keep≗ (λ x → sym (ξ1≗ξ2 x) ∙ ξ≗Keep x) ⊢ξ1' ⊢t
REN-ext ξ1≗ξ2 (⊢Drop≗ ξ≗Drop ⊢ξ1' ⊢t) = ⊢Drop≗ (λ x → sym (ξ1≗ξ2 x) ∙ ξ≗Drop x) ⊢ξ1' ⊢t

⊢renTyREN : ∀{ξₜ ξ Γ1 Γ2 Δ1 Δ2} →
           TYREN ξₜ Γ1 Γ2 →
           REN ξ Γ1 Δ1 Δ2 →
           REN ξ Γ2 (renCtx ξₜ Δ1) (renCtx ξₜ Δ2)
⊢renTyREN ⊢ξₜ (⊢IdRen≗ ξ≗id ⊢Δ) =
  ⊢IdRen≗ ξ≗id (⊢renCtx ⊢ξₜ ⊢Δ)
⊢renTyREN ⊢ξₜ (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) =
  ⊢Keep≗ ξ≗Keep (⊢renTyREN ⊢ξₜ ⊢ξ) (⊢renTyp ⊢ξₜ ⊢t)
⊢renTyREN ⊢ξₜ (⊢Drop≗ ξ≗Drop ⊢ξ ⊢t) =
  ⊢Drop≗ ξ≗Drop (⊢renTyREN ⊢ξₜ ⊢ξ) (⊢renTyp ⊢ξₜ ⊢t)

⊢subTyREN : ∀{σₜ ξ Γ1 Γ2 Δ1 Δ2} →
            TYSUB σₜ Γ1 Γ2 →
            REN ξ Γ1 Δ1 Δ2 →
            REN ξ Γ2 (subCtx σₜ Δ1) (subCtx σₜ Δ2)
⊢subTyREN ⊢σₜ (⊢IdRen≗ ξ≗id ⊢Δ) =
  ⊢IdRen≗ ξ≗id (⊢subCtx ⊢σₜ ⊢Δ)
⊢subTyREN ⊢σₜ (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) =
  ⊢Keep≗ ξ≗Keep (⊢subTyREN ⊢σₜ ⊢ξ) (⊢subTyp ⊢σₜ ⊢t)
⊢subTyREN ⊢σₜ (⊢Drop≗ ξ≗Drop ⊢ξ ⊢t) =
  ⊢Drop≗ ξ≗Drop (⊢subTyREN ⊢σₜ ⊢ξ) (⊢subTyp ⊢σₜ ⊢t)

-- Composition of renamings preserves well-formedness
⊢• : ∀{Γ Δ1 Δ2 Δ3 ξ1 ξ2} →
     REN ξ1 Γ Δ2 Δ3 →
     REN ξ2 Γ Δ1 Δ2 →
     REN (ξ1 • ξ2) Γ Δ1 Δ3
⊢• {ξ2 = ξ2} (⊢IdRen≗ ξ1≗id ⊢Δ2) ⊢ξ2 =
  REN-ext (λ x → sym $ ξ1≗id $ ξ2 x) ⊢ξ2
⊢• {ξ2 = ξ2} (⊢Keep≗ {ξ' = ξ1'} ξ1≗Keep ⊢ξ1' ⊢t) (⊢IdRen≗ ξ2≗id ⊢Δ) =
  ⊢Keep≗ (λ x → ξ1≗Keep (ξ2 x) ∙ cong (Keep ξ1') (ξ2≗id x)) ⊢ξ1' ⊢t
⊢• {ξ1 = ξ1} {ξ2} (⊢Keep≗ {ξ' = ξ1'} ξ1≗Keep ⊢ξ1' ⊢t) (⊢Keep≗ {ξ' = ξ2'} ξ2≗Keep ⊢ξ2' ⊢t') =
  ⊢Keep≗ (λ x → ξ1≗Keep (ξ2 x) ∙ cong (Keep ξ1') (ξ2≗Keep x) ∙ Keep•Keep ξ1' ξ2' x) (⊢• ⊢ξ1' ⊢ξ2') ⊢t
⊢• {ξ1 = ξ1} {ξ2} (⊢Keep≗ {ξ' = ξ1'} ξ1≗Keep ⊢ξ1' ⊢t) (⊢Drop≗ {ξ' = ξ2'} ξ2≗Drop ⊢ξ2' ⊢t') =
  ⊢Drop≗ (λ x → ξ1≗Keep (ξ2 x) ∙ cong (Keep ξ1') (ξ2≗Drop x) ∙ Keep•Drop ξ1' ξ2' x) (⊢• ⊢ξ1' ⊢ξ2')  ⊢t
⊢• {ξ1 = ξ1} {ξ2} (⊢Drop≗ {ξ' = ξ1'} ξ1≗Drop ⊢ξ1' ⊢t) ⊢ξ2 =
  ⊢Drop≗ (λ x → ξ1≗Drop (ξ2 x) ∙ Drop• ξ1' ξ2 x) (⊢• ⊢ξ1' ⊢ξ2) ⊢t

-- The action of well-formed renamings preserve typing
⊢renVar : ∀{Γ Δ1 Δ2 ξ x t} → REN ξ Γ Δ1 Δ2 → Γ ⨾ Δ1 ⊢var x ∶ t → Γ ⨾ Δ2 ⊢var ξ x ∶ t
⊢renVar {Γ} {Δ1} {.Δ1} {ξ} {x} {t} (⊢IdRen≗ ξ≗id ⊢Δ) ⊢x =
  subst (λ y → Γ ⨾ Δ1 ⊢var y ∶ t)
    (sym $ ξ≗id x)
    ⊢x
⊢renVar {Γ} {t ∷ Δ1} {t ∷ Δ2} {ξ} {zero} {t} (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) (⊢0 ⊢Δ ⊢t') =
  subst (λ y → Γ ⨾ t ∷ Δ2 ⊢var y ∶ t)
    (sym $ ξ≗Keep zero)
    (⊢0 (REN⇒⊢ctx₂ ⊢ξ) ⊢t)
⊢renVar {Γ} {t2 ∷ Δ1} {t2 ∷ Δ2} {ξ} {suc x} {t1} (⊢Keep≗ ξ≗Keep ⊢ξ ⊢t) (⊢S ⊢x ⊢t2) =
  subst (λ y → Γ ⨾ t2 ∷ Δ2 ⊢var y ∶ t1)
    (sym $ ξ≗Keep $ suc x)
    (⊢S (⊢renVar ⊢ξ ⊢x) ⊢t2)
⊢renVar {Γ} {Δ1} {t2 ∷ Δ2} {ξ} {x} {t1} (⊢Drop≗ ξ≗Drop ⊢ξ ⊢t2) ⊢x =
  subst (λ y → Γ ⨾ t2 ∷ Δ2 ⊢var y ∶ t1)
    (sym $ ξ≗Drop x)
    (⊢S (⊢renVar ⊢ξ ⊢x) ⊢t2)

⊢ren : ∀{Γ Δ1 Δ2 ξ e t} →
        REN ξ Γ Δ1 Δ2 →
        Γ ⨾ Δ1 ⊢ e ∶ t →
        Γ ⨾ Δ2 ⊢ ren ξ e ∶ t
⊢renVec : ∀{Γ Δ1 Δ2 ξ es Σ} →
          REN ξ Γ Δ1 Δ2 →
          Γ ⨾ Δ1 ⊢vec es ∶ Σ →
          Γ ⨾ Δ2 ⊢vec renVec ξ es ∶ Σ

⊢ren ⊢ξ (⊢var ⊢x) = ⊢var (⊢renVar ⊢ξ ⊢x)
⊢ren ⊢ξ (⊢constr s ⊢ts ⊢es) = ⊢constr s ⊢ts (⊢renVec ⊢ξ ⊢es)

⊢renVec ⊢ξ (⊢[] ⊢Δ1) = ⊢[] (REN⇒⊢ctx₂ ⊢ξ)
⊢renVec {Δ1 = Δ1} ⊢ξ (_⊢∷_ {Γ' = Γ'} {Δ'} ⊢e ⊢es) =
  ⊢ren (⊢Keep* (⊢renTyREN (⊢TyDrop* ⊢TyIdRen Γ') ⊢ξ)
    (⊢ctx-++⁻ Δ' (renCtx (Drop* id (length Γ')) Δ1)
        (⊢⇒⊢ctx ⊢e) .fst)) ⊢e
  ⊢∷ ⊢renVec ⊢ξ ⊢es

data SUB (σ : Sub) (Γ : KndCtx) : Ctx → Ctx → Set where
  ⊢ε : ∀{Δ} (⊢Δ : Γ ⊢ctx Δ) → SUB σ Γ [] Δ
  ⊢▸ : ∀{Δ1 Δ2 e t σ'}
      (σ≗▸ : σ ≗ addSub σ' e) (⊢σ' : SUB σ' Γ Δ1 Δ2)
      (⊢e : Γ ⨾ Δ2 ⊢ e ∶ t) →
      SUB σ Γ (t ∷ Δ1) Δ2

SUB⇒⊢ctx₁ : ∀{σ Γ Δ1 Δ2} → SUB σ Γ Δ1 Δ2 → Γ ⊢ctx Δ1
SUB⇒⊢ctx₁ (⊢ε ⊢Δ) = tt
SUB⇒⊢ctx₁ (⊢▸ σ≗▸ ⊢σ ⊢e) = ⊢⇒⊢typ ⊢e , SUB⇒⊢ctx₁ ⊢σ

SUB⇒⊢ctx₂ : ∀{σ Γ Δ1 Δ2} → SUB σ Γ Δ1 Δ2 → Γ ⊢ctx Δ2
SUB⇒⊢ctx₂ (⊢ε ⊢Δ) = ⊢Δ
SUB⇒⊢ctx₂ (⊢▸ σ≗▸ ⊢σ ⊢e) = SUB⇒⊢ctx₂ ⊢σ

SUB-ext : ∀{Γ Δ1 Δ2 σ1 σ2} → σ1 ≗ σ2 → SUB σ1 Γ Δ1 Δ2 → SUB σ2 Γ Δ1 Δ2
SUB-ext σ1≗σ2 (⊢ε ⊢Δ) = ⊢ε ⊢Δ
SUB-ext σ1≗σ2 (⊢▸ σ≗▸ ⊢σ1' ⊢e) =
 ⊢▸ (λ x → sym (σ1≗σ2 x) ∙ σ≗▸ x) ⊢σ1' ⊢e

⊢•◦ : ∀{Γ Δ1 Δ2 Δ3 ξ σ}
      (⊢ξ : REN ξ Γ Δ2 Δ3)
      (⊢σ : SUB σ Γ Δ1 Δ2) →
      SUB (ξ •◦ σ) Γ Δ1 Δ3
⊢•◦ ⊢ξ (⊢ε ⊢Δ) = ⊢ε (REN⇒⊢ctx₂ ⊢ξ)
⊢•◦ {ξ = ξ} {σ} ⊢ξ (⊢▸ {e = e} {σ' = σ'} σ≗▸ ⊢σ ⊢e) =
  ⊢▸ (λ{ zero → cong (ren ξ) (σ≗▸ zero)
       ; (suc x) → cong (ren ξ) (σ≗▸ (suc x)) })
    (⊢•◦ ⊢ξ ⊢σ) (⊢ren ⊢ξ ⊢e)

⊢DropSub : ∀{σ Γ Δ1 Δ2 t} →
          SUB σ Γ Δ1 Δ2 →
          Γ ⊢typ t →
          SUB (DropSub σ) Γ Δ1 (t ∷ Δ2)
⊢DropSub ⊢σ ⊢t =
  ⊢•◦ (⊢Drop (⊢IdRen (SUB⇒⊢ctx₂ ⊢σ)) ⊢t) ⊢σ

⊢DropSub* : ∀{σ Γ Δ1 Δ2 Δ'} →
            SUB σ Γ Δ1 Δ2 →
            Γ ⊢ctx Δ' →
            SUB (DropSub* σ (length Δ')) Γ Δ1 (Δ' ++ Δ2)
⊢DropSub* {Δ' = []} ⊢σ ⊢Δ' = ⊢σ
⊢DropSub* {Δ' = t ∷ Δ'} ⊢σ (⊢t , ⊢Δ') =
  ⊢DropSub (⊢DropSub* ⊢σ ⊢Δ') ⊢t

⊢KeepSub : ∀{σ Γ Δ1 Δ2 t} →
          SUB σ Γ Δ1 Δ2 →
          Γ ⊢typ t →
          SUB (KeepSub σ) Γ (t ∷ Δ1) (t ∷ Δ2)
⊢KeepSub ⊢σ ⊢t =
  ⊢▸ ≗-refl (⊢DropSub ⊢σ ⊢t) (⊢var (⊢0 (SUB⇒⊢ctx₂ ⊢σ) ⊢t))

⊢KeepSub* : ∀{σ Γ Δ1 Δ2 Δ'} →
            SUB σ Γ Δ1 Δ2 →
            Γ ⊢ctx Δ' →
            SUB (KeepSub* σ (length Δ')) Γ (Δ' ++ Δ1) (Δ' ++ Δ2)
⊢KeepSub* {Δ' = []} ⊢σ ⊢Δ' = ⊢σ
⊢KeepSub* {Δ' = t ∷ Δ'} ⊢σ (⊢t , ⊢Δ') =
  ⊢KeepSub (⊢KeepSub* ⊢σ ⊢Δ') ⊢t

⊢IdSub : ∀{Γ Δ} (⊢Δ : Γ ⊢ctx Δ) → SUB var Γ Δ Δ
⊢IdSub {Γ} {Δ} ⊢Δ =
  SUB-ext (KeepSub*-id (length Δ)) $
  subst (λ x → SUB (KeepSub* var (length Δ)) Γ x x)
    (++-identityʳ Δ)
    (⊢KeepSub* (⊢ε tt) ⊢Δ)

⊢renTySUB : ∀{ξₜ σ Γ1 Γ2 Δ1 Δ2} →
            TYREN ξₜ Γ1 Γ2 →
            SUB σ Γ1 Δ1 Δ2 →
            SUB (tyRen ξₜ ∘ σ) Γ2 (renCtx ξₜ Δ1) (renCtx ξₜ Δ2)
⊢renTySUB ⊢ξₜ (⊢ε ⊢Δ) = ⊢ε (⊢renCtx ⊢ξₜ ⊢Δ)
⊢renTySUB {ξₜ} {σ} ⊢ξₜ (⊢▸ σ≗▸ ⊢σ ⊢e) =
  ⊢▸ (λ{ zero → cong (tyRen ξₜ) (σ≗▸ zero)
       ; (suc x) → cong (tyRen ξₜ) (σ≗▸ (suc x)) })
    (⊢renTySUB ⊢ξₜ ⊢σ)
    (⊢tyRen ⊢ξₜ ⊢e)

⊢subTySUB : ∀{σₜ σ Γ1 Γ2 Δ1 Δ2} →
            TYSUB σₜ Γ1 Γ2 →
            SUB σ Γ1 Δ1 Δ2 →
            SUB (tySub σₜ ∘ σ) Γ2 (subCtx σₜ Δ1) (subCtx σₜ Δ2)
⊢subTySUB ⊢σₜ (⊢ε ⊢Δ) = ⊢ε (⊢subCtx ⊢σₜ ⊢Δ)
⊢subTySUB {σₜ} {σ} ⊢σₜ (⊢▸ σ≗▸ ⊢σ ⊢e) =
  ⊢▸ (λ{ zero → cong (tySub σₜ) (σ≗▸ zero)
       ; (suc x) → cong (tySub σₜ) (σ≗▸ (suc x)) })
    (⊢subTySUB ⊢σₜ ⊢σ)
    (⊢tySub ⊢σₜ ⊢e)

-- The action of well-formed renamings preserve typing
⊢subVar : ∀{Γ Δ1 Δ2 σ x t} → SUB σ Γ Δ1 Δ2 → Γ ⨾ Δ1 ⊢var x ∶ t → Γ ⨾ Δ2 ⊢ σ x ∶ t
⊢subVar {Γ} {Δ1} {Δ2} {σ} (⊢▸ {e = e} {t} σ≗▸ ⊢σ ⊢e) (⊢0 ⊢Δ ⊢t) =
  subst (λ x → Γ ⨾ Δ2 ⊢ x ∶ t)
    (sym $ σ≗▸ zero)
    ⊢e
⊢subVar {Γ} {Δ1} {Δ2} {σ} {suc x} {t} (⊢▸ σ≗▸ ⊢σ ⊢e) (⊢S ⊢x ⊢t2) =
  subst (λ y → Γ ⨾ Δ2 ⊢ y ∶ t)
    (sym $ σ≗▸ (suc x))
    (⊢subVar ⊢σ ⊢x)

⊢sub : ∀{Γ Δ1 Δ2 σ e t} →
        SUB σ Γ Δ1 Δ2 →
        Γ ⨾ Δ1 ⊢ e ∶ t →
        Γ ⨾ Δ2 ⊢ sub σ e ∶ t
⊢subVec : ∀{Γ Δ1 Δ2 σ es Σ} →
          SUB σ  Γ Δ1 Δ2 →
          Γ ⨾ Δ1 ⊢vec es ∶ Σ →
          Γ ⨾ Δ2 ⊢vec subVec σ es ∶ Σ

⊢sub ⊢σ (⊢var ⊢x) = ⊢subVar ⊢σ ⊢x
⊢sub ⊢σ (⊢constr s ⊢ts ⊢es) =
  ⊢constr s ⊢ts (⊢subVec ⊢σ ⊢es)

⊢subVec ⊢σ (⊢[] ⊢Δ) = ⊢[] (SUB⇒⊢ctx₂ ⊢σ)
⊢subVec {Δ1 = Δ1} ⊢σ (_⊢∷_ {Γ' = Γ'} {Δ'} ⊢e ⊢es) =
  ⊢sub
    (⊢KeepSub* {Δ' = Δ'}
        (⊢renTySUB (⊢TyDrop* ⊢TyIdRen Γ') ⊢σ)
        (⊢ctx-++⁻ Δ' (renCtx (Drop* id (length Γ')) Δ1)
          (⊢⇒⊢ctx ⊢e) .fst))
    ⊢e
  ⊢∷ ⊢subVec ⊢σ ⊢es

-- Composition of substitutions preserves well-formedness
⊢◦ : ∀{Γ Δ1 Δ2 Δ3 σ1 σ2} →
     SUB σ1 Γ Δ2 Δ3 →
     SUB σ2 Γ Δ1 Δ2 →
     SUB (σ1 ◦ σ2) Γ Δ1 Δ3
⊢◦ ⊢σ1 (⊢ε ⊢Δ) = ⊢ε (SUB⇒⊢ctx₂ ⊢σ1)
⊢◦ {σ1 = σ1} {σ2} ⊢σ1 (⊢▸ {e = e} {σ' = σ2'} σ2≗▸ ⊢σ2 ⊢e) =
  ⊢▸ {e = sub σ1 e} {σ' = σ1 ◦ σ2'}
    (λ{ zero → cong (sub σ1) (σ2≗▸ zero)
      ; (suc x) → cong (sub σ1) (σ2≗▸ (suc x)) })
    (⊢◦ ⊢σ1 ⊢σ2)
    (⊢sub ⊢σ1 ⊢e)
