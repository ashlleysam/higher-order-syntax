{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common

module Pirouette
  -- Local-language types
  (Typₑ : Set)
  -- We have booleans in the local language
  (Boolₑ : Typₑ)
  -- Local-language constructors
  (Shapeₑ : Set)
  -- Local-language signatures
  (Posₑ : Shapeₑ → List (List Typₑ × Typₑ) × Typₑ)
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)
  where

open import SecondOrderSyntax Typₑ Shapeₑ Posₑ
  using ()
  renaming (Tm to Tmₑ; TmVec to TmVecₑ; Ctx to Ctxₑ;
            constr to constrₑ; [] to []ₑ; _∷_ to _∷ₑ_;
            Ren to Renₑ; ren to renₑ; renVec to renVecₑ;
            Sub to Subₑ; sub to subₑ; subVec to subVecₑ;
            Var to Varₑ; var to varₑ; V0 to V0ₑ; VS to VSₑ)

-- Choreography types
data Typ : Set where
  -- Located type t@ℓ
  At : (t : Typₑ) (ℓ : Loc) → Typ
  -- Function type τ1⇒τ2
  Arrow : (τ1 τ2 : Typ) → Typ

-- Choreography constructors
data Shape : Set where
  -- Local value ℓ.e
  Done : (ℓ : Loc) (sₑ : Shapeₑ) → Shape
  -- Choreographic function
  Fun : (τ1 τ2 : Typ) → Shape
  -- Choreographic function application
  App : (τ1 τ2 : Typ) → Shape
  -- Choreographic fixpoint
  Fix : (τ : Typ) → Shape
  -- Send operation
  Send : (ℓ₁ ℓ₂ : Loc) (t : Typₑ) → Shape
  -- Synchronization operation
  Sync : (ℓ₁ ℓ₂ : Loc) (d : Bool) (τ : Typ) → Shape
  -- Choreographic if-then-else
  IfThen : (ℓ : Loc) (τ : Typ) → Shape

-- At _ ℓ for an entire binding signature
At* : List (List Typₑ × Typₑ) → Loc → List (List Typ × Typ)
At* [] ℓ = []
At* ((Σ , t) ∷ Σs) ℓ =
  (map (flip At ℓ) Σ , At t ℓ) ∷ At* Σs ℓ

Pos : Shape → List (List Typ × Typ) × Typ
-- sₑ Σₑ : t ⊢ Done{ℓ,sₑ} Σₑ@ℓ : t@ℓ
Pos (Done ℓ sₑ) = At* (Posₑ sₑ .fst) ℓ , At (Posₑ sₑ .snd) ℓ
-- Fun{τ1,τ2} [τ1]τ2 : τ1⇒τ2
Pos (Fun τ1 τ2) = (τ1 ∷ [] , τ2) ∷ [] , Arrow τ1 τ2
-- App{τ1,τ2} τ1⇒τ2 τ1 : τ2
Pos (App τ1 τ2) = ([] , Arrow τ1 τ2) ∷ ([] , τ1) ∷ [] , τ2
-- Fix{τ} [τ]τ : τ
Pos (Fix τ) = (τ ∷ [] , τ) ∷ [] , τ
-- Send{ℓ₁,ℓ₂,t} t@ℓ₁ : t@ℓ₂
Pos (Send ℓ₁ ℓ₂ t) = ([] , At t ℓ₁) ∷ [] , At t ℓ₂
-- Sync{ℓ₁,ℓ₂,d,τ} τ : τ
Pos (Sync ℓ₁ ℓ₂ d τ) = ([] , τ) ∷ [] , τ
-- ITE{ℓ,τ} Boolₑ@ℓ τ τ : τ
Pos (IfThen ℓ τ) = ([] , At Boolₑ ℓ) ∷ ([] , τ) ∷ ([] , τ) ∷ [] , τ

open import SecondOrderSyntax Typ Shape Pos

-- Aliases for each constructor
DoneTm : ∀{Γ} (ℓ : Loc) (sₑ : Shapeₑ) →
         TmVec Γ (At* (Posₑ sₑ .fst) ℓ) →
         Tm Γ (At (Posₑ sₑ .snd) ℓ)
DoneTm ℓ sₑ es = constr (Done ℓ sₑ) es

FunTm : ∀{Γ τ1 τ2} → Tm (τ1 ∷ Γ) τ2 → Tm Γ (Arrow τ1 τ2)
FunTm {τ1 = τ1} {τ2} e = constr (Fun τ1 τ2) (e ∷ [])

AppTm : ∀{Γ τ1 τ2} → Tm Γ (Arrow τ1 τ2) → Tm Γ τ1 → Tm Γ τ2
AppTm {τ1 = τ1} {τ2} e1 e2 = constr (App τ1 τ2) (e1 ∷ e2 ∷ [])

FixTm : ∀{Γ τ} → Tm (τ ∷ Γ) τ → Tm Γ τ
FixTm {τ = τ} e = constr (Fix τ) (e ∷ [])

SendTm : ∀{Γ ℓ₁ t} → Tm Γ (At t ℓ₁) → ∀ ℓ₂ → Tm Γ (At t ℓ₂)
SendTm {ℓ₁ = ℓ₁} {t} e ℓ₂ = constr (Send ℓ₁ ℓ₂ t) (e ∷ [])

SyncTm : ∀{Γ τ} (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc) (C : Tm Γ τ) → Tm Γ τ 
SyncTm {τ = τ} ℓ₁ d ℓ₂ e = constr (Sync ℓ₁ ℓ₂ d τ) (e ∷ [])

IfThenTm : ∀{Γ ℓ τ} (e : Tm Γ (At Boolₑ ℓ)) (e1 e2 : Tm Γ τ) → Tm Γ τ
IfThenTm {ℓ = ℓ} {τ} e e1 e2 = constr (IfThen ℓ τ) (e ∷ e1 ∷ e2 ∷ [])

{-
  Context projection

  Extracts all types of the form t@ℓ from a choreographic
  context to form a local context at a specified location ℓ.
-}
_∣_ : Ctx → Loc → Ctxₑ
[] ∣ ℓ = []
(At t ℓ' ∷ Γ) ∣ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = t ∷ Γ ∣ ℓ
... | no  _ = Γ ∣ ℓ
(Arrow τ1 τ2 ∷ Γ) ∣ ℓ = Γ ∣ ℓ

-- Projection distributes over appending contexts
++∣ : ∀ Γ1 Γ2 ℓ → (Γ1 ++ Γ2) ∣ ℓ ≡ Γ1 ∣ ℓ ++ Γ2 ∣ ℓ
++∣ [] Γ2 ℓ = refl
++∣ (At t ℓ' ∷ Γ1) Γ2 ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = cong (t ∷_) (++∣ Γ1 Γ2 ℓ)
... | no  _ = ++∣ Γ1 Γ2 ℓ
++∣ (Arrow _ _ ∷ Γ1) Γ2 ℓ = ++∣ Γ1 Γ2 ℓ

{-
  Mapping a local context to a regular context by
  adding _@ℓ to every type, and then projecting back
  to a local context at ℓ has no effect.
-}
∣∘At≡Id : ∀ Γ ℓ → (map (λ x → At x ℓ) Γ ∣ ℓ) ≡ Γ
∣∘At≡Id [] ℓ = refl
∣∘At≡Id (t ∷ Γ) ℓ with ≡-dec-Loc ℓ ℓ
... | yes _ = cong (t ∷_) (∣∘At≡Id Γ ℓ)
... | no ¬p = ⊥-elim (¬p refl)

{-
  Term projection
  
  Attempts to project a choreographic term of type t@ℓ to a 
  local term of type t in the projected context.
  Will succeed only if the choreographic term is "purely local".
  That is, it only contains constructors from the local language.
  
  For instance, ℓ₁.e ⇝ ℓ₂ will fail to project, and so will
  ℓ₂.e₁ (ℓ.e₂ ⇝ ℓ₂), but ℓ₁.e₁ ℓ₁.e₂ will project to e₁ e₂.
-}
-- Variables can always project
varProj : ∀{Γ t ℓ} → Var Γ (At t ℓ) → Varₑ (Γ ∣ ℓ) t
varProj {ℓ = ℓ} V0 with ≡-dec-Loc ℓ ℓ
... | yes _ = V0ₑ
... | no ¬p = ⊥-elim (¬p refl)
varProj {ℓ = ℓ} (VS {s = At t ℓ'} x) with ≡-dec-Loc ℓ ℓ'
... | yes _ = VSₑ (varProj x)
... | no  _ = varProj x
varProj (VS {s = Arrow _ _} x) = varProj x

-- Data type to signify that a term projects
data _∣≡_ {Γ ℓ}: ∀{t} → Tm Γ (At t ℓ) → Tmₑ (Γ ∣ ℓ) t → Set
data _*∣≡_ {Γ ℓ} : ∀{Σ} → TmVec Γ (At* Σ ℓ) → TmVecₑ (Γ ∣ ℓ) Σ → Set

data _∣≡_ {Γ} {ℓ} where
  -- Only the "Done" constructor and variables are allowed to project
  projVar : ∀{t}
            (x : Var Γ (At t ℓ)) →
            var x ∣≡ varₑ (varProj x)
  projDone : ∀{sₑ es'} {es : TmVec Γ (At* (Posₑ sₑ .fst) ℓ)} →
             (es*∣≡es' : es *∣≡ es') →
             DoneTm ℓ sₑ es ∣≡ constrₑ sₑ es'

data _*∣≡_ {Γ} {ℓ} where
  -- Projection acts homomorphically on vectors of terms
  projNil : [] *∣≡ []ₑ
  projCons : ∀{Δ t Σ} {e : Tm (map (λ x → At x ℓ) (Δ ∣ ℓ) ++ Γ) (At t ℓ)} {e' : Tmₑ (Δ ∣ ℓ ++ Γ ∣ ℓ) t}
            {es : TmVec Γ (At* Σ ℓ)} {es' : TmVecₑ (Γ ∣ ℓ) Σ} →
            e ∣≡ subst (flip Tmₑ t)
                  (cong (λ x → x ++ (Γ ∣ ℓ)) (sym (∣∘At≡Id (Δ ∣ ℓ) ℓ))
                    ∙ sym (++∣ (map (λ x → At x ℓ) (Δ ∣ ℓ)) Γ ℓ))
                  e' →
            es *∣≡ es' →
            (e ∷ es) *∣≡ (e' ∷ₑ es')

module Semantics
  -- Values of the local language
  (Valueₑ : ∀{t} → Tmₑ [] t → Set)
  -- Small-step operational semantics of the local language
  (_⇒ₑ_ : ∀{t} → Tmₑ [] t → Tmₑ [] t → Set)
  -- There should be local language constants for true and false
  (ttₑ ffₑ : Tmₑ [] Boolₑ)
  where

  -- Choreographic values
  data Value : ∀{τ} → Tm [] τ → Set where
    -- If e projects to e∣ℓ, which is a value, then e is a value
    valProj : ∀{t ℓ} {e : Tm [] (At t ℓ)} {e∣ℓ : Tmₑ [] t} →
              e ∣≡ e∣ℓ →
              Valueₑ e∣ℓ →
              Value e
    -- Choreographic functions are values
    valFun : ∀{τ1 τ2}
             (e : Tm (τ1 ∷ []) τ2) →
             Value (FunTm e)

  data TraceElem : Set where
    -- Noop
    • : TraceElem
    -- Reduce a local value
    LocalStep : (ℓ : Loc) → TraceElem
    -- Send a value
    Send : ∀{t} (ℓ₁ : Loc) (e : Tmₑ [] t) (ℓ₂ : Loc) → TraceElem
    -- Send a synchronization message
    Sync : (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc) → TraceElem

  -- Choreographic trace semantics
  data _⇒[_]_ : ∀{τ} (e : Tm [] τ) (T : TraceElem) (e' : Tm [] τ) → Set where
    -- Make a local step
    stepLocal : ∀{t ℓ} {e e' : Tm [] (At t ℓ)} {e∣ℓ e'∣ℓ : Tmₑ [] t} →
                e ∣≡ e∣ℓ →
                e∣ℓ ⇒ₑ e'∣ℓ →
                e' ∣≡ e'∣ℓ →
                e ⇒[ LocalStep ℓ ] e'
    -- Reduction on the function of an application
    stepFun : ∀{T τ1 τ2} {e1 e1' : Tm [] (Arrow τ1 τ2)} →
              e1 ⇒[ T ] e1' →
              (e2 : Tm [] τ1) →
              AppTm e1 e2 ⇒[ T ] AppTm e1' e2
    -- Reduction on the argument of an application
    stepArg : ∀{T τ1 τ2} {e1 : Tm [] (Arrow τ1 τ2)} {e2 e2' : Tm [] τ1} →
              Value e1 →
              e2 ⇒[ T ] e2' →
              AppTm e1 e2 ⇒[ T ] AppTm e1 e2'
    -- Function β-reduction
    stepβ : ∀{τ1 τ2} {v : Tm [] τ1} →
            (e : Tm (τ1 ∷ []) τ2) →
            Value v →
            AppTm (FunTm e) v ⇒[ • ] sub (IdSub ▸ v) e
    -- Fixpoint β-reduction
    stepFix : ∀{τ}
              (e : Tm (τ ∷ []) τ) →
              FixTm e ⇒[ • ] sub (IdSub ▸ FixTm e) e
    -- Send a value
    stepSend : ∀{t v}
               (ℓ₁ : Loc) →
               {e : Tm [] (At t ℓ₁)} →
               e ∣≡ v →
               Valueₑ v →
               (ℓ₂ : Loc) →
               {e' : Tm [] (At t ℓ₂)} →
               e' ∣≡ v →
               SendTm e ℓ₂ ⇒[ Send ℓ₁ v ℓ₂ ] e'
    -- Send a synchronization message
    stepSync : ∀{τ}
               (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc)
               (e : Tm [] τ) →
               SyncTm ℓ₁ d ℓ₂ e ⇒[ Sync ℓ₁ d ℓ₂ ] e
    -- Reduction on the boolean argument of an if-then-else
    stepIfThen : ∀{T τ ℓ} {e e' : Tm [] (At Boolₑ ℓ)} →
                 e ⇒[ T ] e' →
                 (e1 e2 : Tm [] τ) →
                 IfThenTm e e1 e2 ⇒[ T ] IfThenTm e' e1 e2
    -- If-then-else β-reduction
    stepIfThenT : ∀{T τ ℓ} {e : Tm [] (At Boolₑ ℓ)} →
                  e ∣≡ ttₑ →
                  (e1 e2 : Tm [] τ) →
                  IfThenTm e e1 e2 ⇒[ T ] e1
    stepIfThenF : ∀{τ ℓ} {e : Tm [] (At Boolₑ ℓ)} →
                  e ∣≡ ffₑ →
                  (e1 e2 : Tm [] τ) →
                  IfThenTm e e1 e2 ⇒[ • ] e2