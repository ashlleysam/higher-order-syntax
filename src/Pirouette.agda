{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.List.Properties
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

-- Choreographic types
data ChorTyp : Set where
  -- Located type t@ℓ
  At : (t : Typₑ) (ℓ : Loc) → ChorTyp
  -- Function type τ1⇒τ2
  Arrow : (τ1 τ2 : ChorTyp) → ChorTyp

-- Program types are either choreographic, or a bound variable type
data Typ : Set where
  -- Locally bound type ℓ.t
  Bnd : (ℓ : Loc) (t : Typₑ) → Typ
  Chor : ChorTyp → Typ

-- Choreography constructors
data Shape : Set where
  -- Local value e
  Local : (ℓ : Loc) (sₑ : Shapeₑ) → Shape
  -- Done value ℓ.e
  Done : (ℓ : Loc) (t : Typₑ) → Shape
  -- Choreographic function
  Fun : (τ1 τ2 : ChorTyp) → Shape
  -- Choreographic function application
  App : (τ1 τ2 : ChorTyp) → Shape
  -- Choreographic fixpoint
  Fix : (τ : ChorTyp) → Shape
  -- Send operation
  Send : (ℓ₁ ℓ₂ : Loc) (t : Typₑ) → Shape
  -- Synchronization operation
  Sync : (ℓ₁ ℓ₂ : Loc) (d : Bool) (τ : ChorTyp) → Shape
  -- Choreographic if-then-else
  IfThen : (ℓ : Loc) (τ : ChorTyp) → Shape
  -- Local value binder
  LocalLet : (ℓ : Loc) (t : Typₑ) (τ : ChorTyp) → Shape

-- ℓ._ for an entire local binding signature
Bnd* : Loc → List (List Typₑ × Typₑ) → List (List Typ × Typ)
Bnd* ℓ [] = []
Bnd* ℓ ((Σ , t) ∷ Σs) =
  (map (Bnd ℓ) Σ , Bnd ℓ t) ∷ Bnd* ℓ Σs

-- Choreographic program signatures
Pos : Shape → List (List Typ × Typ) × Typ
-- sₑ Σₑ : t ⊢ Local{ℓ,sₑ} Σₑ@ℓ : ℓ.t
Pos (Local ℓ sₑ) = Bnd* ℓ (Posₑ sₑ .fst) , Bnd ℓ (Posₑ sₑ .snd)
-- Done{ℓ,t} ℓ.t : t@ℓ
Pos (Done ℓ t) = ([] , Bnd ℓ t) ∷ [] , Chor (At t ℓ)
-- Fun{τ1,τ2} [τ1]τ2 : τ1⇒τ2
Pos (Fun τ1 τ2) = (Chor τ1 ∷ [] , Chor τ2) ∷ [] , Chor (Arrow τ1 τ2)
-- App{τ1,τ2} τ1⇒τ2 τ1 : τ2
Pos (App τ1 τ2) = ([] , Chor (Arrow τ1 τ2)) ∷ ([] , Chor τ1) ∷ [] , Chor τ2
-- Fix{τ} [τ]τ : τ
Pos (Fix τ) = (Chor τ ∷ [] , Chor τ) ∷ [] , Chor τ
-- Send{ℓ₁,ℓ₂,t} t@ℓ₁ : t@ℓ₂
Pos (Send ℓ₁ ℓ₂ t) = ([] , Chor (At t ℓ₁)) ∷ [] , Chor (At t ℓ₂)
-- Sync{ℓ₁,ℓ₂,d,τ} τ : τ
Pos (Sync ℓ₁ ℓ₂ d τ) = ([] , Chor τ) ∷ [] , Chor τ
-- ITE{ℓ,τ} Boolₑ@ℓ τ τ : τ
Pos (IfThen ℓ τ) = ([] , Chor (At Boolₑ ℓ)) ∷ ([] , Chor τ) ∷ ([] , Chor τ) ∷ [] , Chor τ
-- LocalLet{ℓ,t} t@ℓ [ℓ.t]τ : τ
Pos (LocalLet ℓ t τ) = ([] , Chor (At t ℓ)) ∷ (Bnd ℓ t ∷ [] , Chor τ) ∷ [] , Chor τ

open import SecondOrderSyntax Typ Shape Pos

-- Aliases for each constructor
LocalTm : ∀{Γ} (ℓ : Loc) (sₑ : Shapeₑ) →
         TmVec Γ (Bnd* ℓ (Posₑ sₑ .fst)) →
         Tm Γ (Bnd ℓ (Posₑ sₑ .snd))
LocalTm ℓ sₑ Cs = constr (Local ℓ sₑ) Cs

DoneTm : ∀{Γ t} (ℓ : Loc) →
         Tm Γ (Bnd ℓ t) →
         Tm Γ (Chor (At t ℓ))
DoneTm {t = t} ℓ e = constr (Done ℓ t) (e ∷ [])

FunTm : ∀{Γ τ1 τ2} → Tm (Chor τ1 ∷ Γ) (Chor τ2) → Tm Γ (Chor (Arrow τ1 τ2))
FunTm {τ1 = τ1} {τ2} C = constr (Fun τ1 τ2) (C ∷ [])

AppTm : ∀{Γ τ1 τ2} → Tm Γ (Chor (Arrow τ1 τ2)) → Tm Γ (Chor τ1) → Tm Γ (Chor τ2)
AppTm {τ1 = τ1} {τ2} C1 C2 = constr (App τ1 τ2) (C1 ∷ C2 ∷ [])

FixTm : ∀{Γ τ} → Tm (Chor τ ∷ Γ) (Chor τ) → Tm Γ (Chor τ)
FixTm {τ = τ} C = constr (Fix τ) (C ∷ [])

SendTm : ∀{Γ ℓ₁ t} → Tm Γ (Chor (At t ℓ₁)) → ∀ ℓ₂ → Tm Γ (Chor (At t ℓ₂))
SendTm {ℓ₁ = ℓ₁} {t} C ℓ₂ = constr (Send ℓ₁ ℓ₂ t) (C ∷ [])

SyncTm : ∀{Γ τ} (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc) (C : Tm Γ (Chor τ)) → Tm Γ (Chor τ)
SyncTm {τ = τ} ℓ₁ d ℓ₂ C = constr (Sync ℓ₁ ℓ₂ d τ) (C ∷ [])

IfThenTm : ∀{Γ ℓ τ}
          (C : Tm Γ (Chor (At Boolₑ ℓ)))
          (C1 C2 : Tm Γ (Chor τ)) →
          Tm Γ (Chor τ)
IfThenTm {ℓ = ℓ} {τ} C C1 C2 = constr (IfThen ℓ τ) (C ∷ C1 ∷ C2 ∷ [])

LocalLetTm : ∀{Γ ℓ t τ}
             (C1 : Tm Γ (Chor (At t ℓ)))
             (C2 : Tm (Bnd ℓ t ∷ Γ) (Chor τ)) →
             Tm Γ (Chor τ)
LocalLetTm {ℓ = ℓ} {t} {τ} C1 C2 = constr (LocalLet ℓ t τ) (C1 ∷ C2 ∷ [])

{-
  Context projection

  Extracts all bound variables ℓ.t from a choreographic
  context to form a local context at a specified location ℓ.
-}
_∣_ : Ctx → Loc → Ctxₑ
[] ∣ ℓ = []
(Bnd ℓ' t ∷ Γ) ∣ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = t ∷ (Γ ∣ ℓ)
... | no  _ = Γ ∣ ℓ
(Chor τ ∷ Γ) ∣ ℓ = Γ ∣ ℓ

-- Projection distributes over appending contexts
++∣ : ∀ Γ1 Γ2 ℓ → (Γ1 ++ Γ2) ∣ ℓ ≡ Γ1 ∣ ℓ ++ Γ2 ∣ ℓ
++∣ [] Γ2 ℓ = refl
++∣ (Bnd ℓ' t ∷ Γ1) Γ2 ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = cong (t ∷_) (++∣ Γ1 Γ2 ℓ)
... | no  _ = ++∣ Γ1 Γ2 ℓ
++∣ (Chor τ ∷ Γ1) Γ2 ℓ = ++∣ Γ1 Γ2 ℓ

{-
  Mapping a local context to a regular context by
  adding ℓ._ to every type, and then projecting back
  to a local context at ℓ has no effect.
-}
∣∘Bnd≡Id : ∀ Γ ℓ → (map (Bnd ℓ) Γ ∣ ℓ) ≡ Γ
∣∘Bnd≡Id [] ℓ = refl
∣∘Bnd≡Id (t ∷ Γ) ℓ with ≡-dec-Loc ℓ ℓ
... | yes _ = cong (t ∷_) (∣∘Bnd≡Id Γ ℓ)
... | no ¬p = ⊥-elim (¬p refl)

{-
Project a variable of type ℓ.t to a local variable in the projected context

Extra equalities are used in the following functions to satisfy the
pattern-matcher and so that subst doesn't have to be used to switch
between equivalent contexts.
-}
varProj : ∀{Γ t ℓ} (x : Var Γ (Bnd ℓ t)) → Varₑ (Γ ∣ ℓ) t
varProj {ℓ = ℓ} V0 with ≡-dec-Loc ℓ ℓ
... | yes _ = V0ₑ
... | no ¬p = ⊥-elim (¬p refl)
varProj {ℓ = ℓ} (VS {s = Bnd ℓ' t} x) with ≡-dec-Loc ℓ ℓ'
... | yes _ = VSₑ (varProj x)
... | no  _ = varProj x
varProj {ℓ = ℓ} (VS {s = Chor τ} x) = varProj x
 
-- Project a term of type ℓ.t to a local term in the projected context.
tmProj : ∀{Γ1 Γ2 ℓ t τ} (e : Tm Γ1 τ) (p : Bnd ℓ t ≡ τ) (q : Γ1 ∣ ℓ ≡ Γ2) → Tmₑ Γ2 t
tmVecProj : ∀{Γ1 Γ2 ℓ Σ1 Σ2} (es : TmVec Γ1 Σ1) (p : Bnd* ℓ Σ2 ≡ Σ1) (q : Γ1 ∣ ℓ ≡ Γ2) → TmVecₑ Γ2 Σ2

tmProj (var x) refl refl = varₑ (varProj x)
tmProj (constr (Local ℓ sₑ) es) refl refl = constrₑ sₑ (tmVecProj es refl refl)

tmVecProj {Σ1 = []} {[]} [] refl refl = []ₑ
tmVecProj {Γ1} {Γ2} {ℓ} {Σ1 = .((map (Bnd ℓ) Δ , Bnd ℓ t) ∷ Bnd* ℓ Σ2)} {Σ2 = (Δ , t) ∷ Σ2} (e ∷ es) refl refl =
  tmProj e refl (++∣ (map (Bnd ℓ) Δ) Γ1 ℓ ∙ cong (_++ (Γ1 ∣ ℓ)) (∣∘Bnd≡Id Δ ℓ)) ∷ₑ tmVecProj es refl refl

-- Inject a local variable of type t to a variable of type ℓ.t in an injected context
varInj : ∀{Γ t ℓ} → Varₑ Γ t → Var (map (Bnd ℓ) Γ) (Bnd ℓ t)
varInj V0ₑ     = V0
varInj (VSₑ x) = VS (varInj x)

-- Inject a local term of type t to a term of type ℓ.t in an injected context
tmInj : ∀{Γ1 Γ2 ℓ t} (e : Tmₑ Γ1 t) (p : map (Bnd ℓ) Γ1 ≡ Γ2) → Tm Γ2 (Bnd ℓ t)
tmVecInj : ∀{Γ1 Γ2 ℓ Σ} (es : TmVecₑ Γ1 Σ) (p : map (Bnd ℓ) Γ1 ≡ Γ2) → TmVec Γ2 (Bnd* ℓ Σ)

tmInj (varₑ x) refl = var (varInj x) -- var (varInj x)
tmInj {ℓ = ℓ} (constrₑ sₑ es) refl = LocalTm ℓ sₑ (tmVecInj es refl)

tmVecInj []ₑ refl = []
tmVecInj {Γ1} {Γ2} {ℓ} {(Δ , t) ∷ Σ} (e ∷ₑ es) refl =
  tmInj e (map-++-commute (Bnd ℓ) Δ Γ1) ∷ tmVecInj es refl

-- How substition acts on variables
substV0 : ∀{Γ1 Γ2 t} (p : t ∷ Γ1 ≡ t ∷ Γ2) →
          subst (λ x → Varₑ x t) p V0ₑ ≡ V0ₑ
substV0 refl = refl

substVS : ∀{Γ1 Γ2 s t} (p : Γ1 ≡ Γ2) (x : Varₑ Γ1 t) →
          subst (λ x → Varₑ x t) (cong (s ∷_) p) (VSₑ x) ≡
          VSₑ (subst (λ x → Varₑ x t) p x)
substVS refl x = refl

-- Projecting after injecting a variable has no effect

varProjInj : ∀{Γ ℓ t} (x : Varₑ Γ t) (p : Γ ≡ (map (Bnd ℓ) Γ ∣ ℓ)) →
            varProj (varInj x) ≡
            subst (λ x → Varₑ x t) p x
varProjInj {t ∷ Γ} {ℓ} {t} V0ₑ p with ≡-dec-Loc ℓ ℓ
... | yes _ = sym (substV0 p)
... | no ¬p = ⊥-elim (¬p refl)
varProjInj {s ∷ Γ} {ℓ} {t} (VSₑ x) p with ≡-dec-Loc ℓ ℓ
... | yes _ =
  VSₑ (varProj (varInj x))
    ≡⟨ cong VSₑ (varProjInj x (∷-injective p .snd)) ⟩
  VSₑ (subst (λ x → Varₑ x t) (∷-injective p .snd) x)
    ≡⟨ sym (substVS (∷-injective p .snd) x) ⟩
  subst (λ x → Varₑ x t) (cong (s ∷_) (∷-injective p .snd)) (VSₑ x)
    ≡⟨ cong (λ y → subst (λ x → Varₑ x t) y (VSₑ x)) (UIP _ _) ⟩
  subst (λ x → Varₑ x t) p (VSₑ x) ∎
... | no ℓ≠ℓ = ⊥-elim (ℓ≠ℓ refl)

-- How substitution acts on terms
substVar : ∀{Γ1 Γ2 t} (p : Γ1 ≡ Γ2) (x : Varₑ Γ1 t) →
          varₑ (subst (λ x → Varₑ x t) p x) ≡
          subst (λ x → Tmₑ x t) p (varₑ x)
substVar refl x = refl

substConstr : ∀{Γ1 Γ2 sₑ} (p : Γ1 ≡ Γ2) (es : TmVecₑ Γ1 (Posₑ sₑ .fst)) →
            constrₑ sₑ (subst (λ x → TmVecₑ x (Posₑ sₑ .fst)) p es) ≡
            subst (λ x → Tmₑ x (Posₑ sₑ .snd)) p (constrₑ sₑ es)
substConstr refl es = refl

-- How substition acts on term vectors
substNil : ∀{Γ1 Γ2} (p : Γ1 ≡ Γ2) →
           []ₑ ≡ subst (λ x → TmVecₑ x []) p []ₑ
substNil refl = refl

substCons : ∀{Σ Δ Γ1 Γ2 t} (p : Γ1 ≡ Γ2) (e : Tmₑ (Δ ++ Γ1) t) (es : TmVecₑ Γ1 Σ) →
            subst (λ x → TmVecₑ x ((Δ , t) ∷ Σ)) p (e ∷ₑ es) ≡
            subst (λ x → Tmₑ x t) (cong (Δ ++_) p) e ∷ₑ subst (λ x → TmVecₑ x Σ) p es
substCons refl e es = refl

-- Projecting after an injection yields the original term
tmProjInj : ∀{Γ1 Γ2 Γ3 ℓ t} (e : Tmₑ Γ1 t) (p : map (Bnd ℓ) Γ1 ≡ Γ2) (q : (Γ2 ∣ ℓ) ≡ Γ3) (r : Γ1 ≡ Γ3) →
            tmProj (tmInj e p) refl q ≡ subst (flip Tmₑ t) r e
tmVecProjInj : ∀{Γ1 Γ2 Γ3 ℓ Σ} (es : TmVecₑ Γ1 Σ) (p : map (Bnd ℓ) Γ1 ≡ Γ2) (q : (Γ2 ∣ ℓ) ≡ Γ3) (r : Γ1 ≡ Γ3) → 
               tmVecProj (tmVecInj es p) refl q ≡ subst (flip TmVecₑ Σ) r es

tmProjInj {t = t} (varₑ x) refl refl r =
  varₑ (varProj (varInj x))
    ≡⟨ cong varₑ (varProjInj x r) ⟩
  varₑ (subst (flip Varₑ t) r x)
    ≡⟨ substVar r x ⟩
  subst (flip Tmₑ t) r (varₑ x) ∎
tmProjInj (constrₑ s es) refl refl r =
  constrₑ s (tmVecProj (tmVecInj es refl) refl refl)
    ≡⟨ cong (constrₑ s) (tmVecProjInj es refl refl r) ⟩
  constrₑ s (subst (flip TmVecₑ (Posₑ s .fst)) r es)
    ≡⟨ substConstr r es ⟩
  subst (λ x → Tmₑ x (Posₑ s .snd)) r (constrₑ s es) ∎

tmVecProjInj [] refl refl r = substNil r
tmVecProjInj {Γ1} {ℓ = ℓ} {(Δ , t) ∷ Σ} (e ∷ₑ es) refl refl r =
  tmProj (tmInj e (map-++-commute (Bnd ℓ) Δ Γ1)) refl eq1
      ∷ₑ tmVecProj (tmVecInj es refl) refl refl
    ≡⟨ cong (_∷ₑ tmVecProj (tmVecInj es refl) refl refl)
        (tmProjInj e (map-++-commute (Bnd ℓ) Δ Γ1) eq1 eq2) ⟩
  subst (flip Tmₑ t) eq2 e
      ∷ₑ tmVecProj (tmVecInj es refl) refl refl
    ≡⟨ cong₂ _∷ₑ_ refl (tmVecProjInj es refl refl r) ⟩
  subst (flip Tmₑ t) (cong (Δ ++_) r) e
      ∷ₑ subst (flip TmVecₑ Σ) r es
    ≡⟨ sym (substCons r e es) ⟩
  subst (flip TmVecₑ ((Δ , t) ∷ Σ)) r (e ∷ₑ es) ∎
  where
  eq1 : (map (Bnd ℓ) Δ ++ map (Bnd ℓ) Γ1) ∣ ℓ ≡ Δ ++ (map (Bnd ℓ) Γ1 ∣ ℓ)
  eq1 = ++∣ (map (Bnd ℓ) Δ) (map (Bnd ℓ) Γ1) ℓ
        ∙ cong (_++ (map (Bnd ℓ) Γ1 ∣ ℓ)) (∣∘Bnd≡Id Δ ℓ)

  eq2 : Δ ++ Γ1 ≡ Δ ++ (map (Bnd ℓ) Γ1 ∣ ℓ)
  eq2 = cong (_++_ Δ) r

-- We can simulate sending a bound value by replacing all occurrences of ℓ₁ with ℓ₂
sendVar : ∀{Γ ℓ₁ t} → Var (map (Bnd ℓ₁) Γ) (Bnd ℓ₁ t) →
          (ℓ₂ : Loc) → Var (map (Bnd ℓ₂) Γ) (Bnd ℓ₂ t)
sendVar {t ∷ Γ} V0 ℓ₂ = V0
sendVar {t ∷ Γ} (VS x) ℓ₂ = VS (sendVar x ℓ₂)

sendBndTm≡ : ∀{Γ Γ' ℓ₁ t τ} → Tm Γ' τ →
            Γ' ≡ map (Bnd ℓ₁) Γ → τ ≡ Bnd ℓ₁ t →
           (ℓ₂ : Loc) → Tm (map (Bnd ℓ₂) Γ) (Bnd ℓ₂ t)
sendBndTmVec≡ : ∀{Γ Γ' ℓ₁ Σ Σ'} → TmVec Γ' Σ →
              Γ' ≡ map (Bnd ℓ₁) Γ → Σ ≡ Bnd* ℓ₁ Σ' →
              (ℓ₂ : Loc) → TmVec (map (Bnd ℓ₂) Γ) (Bnd* ℓ₂ Σ')

sendBndTm≡ (var x) refl refl ℓ₂ = var (sendVar x ℓ₂)
sendBndTm≡ (constr (Local ℓ₁ sₑ) es) refl refl ℓ₂ =
  constr (Local ℓ₂ sₑ) (sendBndTmVec≡ es refl refl ℓ₂)

sendBndTmVec≡ {Γ} {.(map (Bnd ℓ₁) Γ)} {ℓ₁} {.[]} {[]} [] refl refl ℓ₂ = []
sendBndTmVec≡ {Γ} {.(map (Bnd ℓ₁) Γ)} {ℓ₁} {.((map (Bnd ℓ₁) Δ , Bnd ℓ₁ t) ∷ Bnd* ℓ₁ Σ)}
  {(Δ , t) ∷ Σ} (e ∷ es) refl refl ℓ₂ = e⇝ℓ₂' ∷ sendBndTmVec≡ es refl refl ℓ₂
  where
  eq₁ : map (Bnd ℓ₁) Δ ++ map (Bnd ℓ₁) Γ ≡ map (Bnd ℓ₁) (Δ ++ Γ)
  eq₁ = sym (map-++-commute (Bnd ℓ₁) Δ Γ)

  e⇝ℓ₂ : Tm (map (Bnd ℓ₂) (Δ ++ Γ)) (Bnd ℓ₂ t)
  e⇝ℓ₂ = sendBndTm≡ e eq₁ refl ℓ₂

  eq₂ : map (Bnd ℓ₂) (Δ ++ Γ) ≡ map (Bnd ℓ₂) Δ ++ map (Bnd ℓ₂) Γ
  eq₂ = map-++-commute (Bnd ℓ₂) Δ Γ

  e⇝ℓ₂' : Tm (map (Bnd ℓ₂) Δ ++ map (Bnd ℓ₂) Γ) (Bnd ℓ₂ t)
  e⇝ℓ₂' = subst (flip Tm (Bnd ℓ₂ t)) eq₂ e⇝ℓ₂

sendBndTm : ∀{Γ ℓ₁ t} → Tm (map (Bnd ℓ₁) Γ) (Bnd ℓ₁ t) →
            (ℓ₂ : Loc) → Tm (map (Bnd ℓ₂) Γ) (Bnd ℓ₂ t)
sendBndTm e ℓ₂ = sendBndTm≡ e refl refl ℓ₂

sendBndTmVec : ∀{Γ ℓ₁ Σ} → TmVec (map (Bnd ℓ₁) Γ) (Bnd* ℓ₁ Σ) →
               (ℓ₂ : Loc) → TmVec (map (Bnd ℓ₂) Γ) (Bnd* ℓ₂ Σ)
sendBndTmVec es ℓ₂ = sendBndTmVec≡ es refl refl ℓ₂

module Semantics
  -- Values of the local language
  (Valueₑ : ∀{t} → Tmₑ [] t → Set)
  -- Small-step operational semantics of the local language
  (_⇒ₑ_ : ∀{t} → Tmₑ [] t → Tmₑ [] t → Set)
  -- Local values cannot step
  (valNoStepₑ : ∀{t} {e e' : Tmₑ [] t} → Valueₑ e → ¬ (e ⇒ₑ e'))
  -- Progress holds for the local language
  (progressₑ : ∀{t} (e : Tmₑ [] t) →
               (Valueₑ e) ⊎ Σ[ e' ∈ Tmₑ [] t ] (e ⇒ₑ e'))
  -- There should be local language constants for true and false
  (ttₑ ffₑ : Tmₑ [] Boolₑ)
  -- Boolean values are only true or value
  (boolInvertₑ : ∀{e} → Valueₑ e → (e ≡ ttₑ) ⊎ (e ≡ ffₑ))
  where

  {-
    Functions, Done expressions whose argument projects to a value,
    and all terms of type ℓ.t are values. Terms of type ℓ.t should
    be considered as static local expressions, and placing them
    under a Done constructor allows them to be evaluated.
  -}
  data Value : ∀{τ} → Tm [] τ → Set where
    -- All terms of type ℓ.t are values
    valBnd : ∀{t ℓ} (e : Tm [] (Bnd ℓ t)) → Value e
    -- If e∣ℓ is a value, then Done e is a value
    valDone : ∀{t ℓ} {v : Tm [] (Bnd ℓ t)} →
              Valueₑ (tmProj v refl refl) →
              Value (DoneTm ℓ v)
    -- Choreographic functions are values
    valFun : ∀{τ1 τ2}
             (C : Tm (Chor τ1 ∷ []) (Chor τ2)) →
             Value (FunTm C)

  -- Trace elements
  data TraceElem : Set where
    -- Noop
    • : TraceElem
    -- Reduce a local value
    LocalStep : (ℓ : Loc) → TraceElem
    -- Send a value
    SendStep : ∀{t} (ℓ₁ : Loc) (v : Tmₑ [] t) (v-Val : Valueₑ v) (ℓ₂ : Loc) → TraceElem
    -- Send a synchronization message
    SyncStep : (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc) → TraceElem

  -- Choreographic trace semantics
  data _⇒[_]_ : ∀{τ} (C : Tm [] τ) (T : TraceElem) (C' : Tm [] τ) → Set where
    -- Make a step under a Done
    stepDone : ∀{t ℓ} {e e' : Tm [] (Bnd ℓ t)} →
                tmProj e refl refl ⇒ₑ tmProj e' refl refl →
                DoneTm ℓ e ⇒[ LocalStep ℓ ] DoneTm ℓ e'

    -- Reduction on the function of an application
    stepFun : ∀{T τ1 τ2} {C1 C1' : Tm [] (Chor (Arrow τ1 τ2))} →
              C1 ⇒[ T ] C1' →
              (C2 : Tm [] (Chor τ1)) →
              AppTm C1 C2 ⇒[ T ] AppTm C1' C2
    -- Reduction on the argument of an application
    stepArg : ∀{T τ1 τ2} {C1 : Tm [] (Chor (Arrow τ1 τ2))} {C2 C2' : Tm [] (Chor τ1)} →
              Value C1 →
              C2 ⇒[ T ] C2' →
              AppTm C1 C2 ⇒[ T ] AppTm C1 C2'
    -- Function β-reduction
    stepβ : ∀{τ1 τ2} {V : Tm [] (Chor τ1)} →
            (C : Tm (Chor τ1 ∷ []) (Chor τ2)) →
            Value V →
            AppTm (FunTm C) V ⇒[ • ] sub (IdSub ▸ V) C
    -- Fixpoint β-reduction
    stepFix : ∀{τ}
              (C : Tm (Chor τ ∷ []) (Chor τ)) →
              FixTm C ⇒[ • ] sub (IdSub ▸ FixTm C) C

    -- Step inside a send operation
    stepSend : ∀{t ℓ₁ ℓ₂ T} {C C' : Tm [] (Chor (At t ℓ₁))} →
               C ⇒[ T ] C' →
               SendTm C ℓ₂ ⇒[ T ] SendTm C' ℓ₂
    -- Send a value
    stepSendVal : ∀{t ℓ₁}
                  {e : Tm [] (Bnd ℓ₁ t)} →
                  (v-Val : Valueₑ (tmProj e refl refl)) →
                  (ℓ₂ : Loc) →
                  SendTm (DoneTm ℓ₁ e) ℓ₂
                  ⇒[ SendStep ℓ₁ (tmProj e refl refl) v-Val ℓ₂ ]
                  DoneTm ℓ₂ (sendBndTm e ℓ₂)
    -- Send a synchronization message
    stepSync : ∀{τ}
               (ℓ₁ : Loc) (d : Bool) (ℓ₂ : Loc)
               (C : Tm [] (Chor τ)) →
               SyncTm ℓ₁ d ℓ₂ C ⇒[ SyncStep ℓ₁ d ℓ₂ ] C

    -- Reduction on the boolean argument of an if-then-else
    stepIfThen : ∀{T τ ℓ} {C C' : Tm [] (Chor (At Boolₑ ℓ))} →
                 C ⇒[ T ] C' →
                 (C1 C2 : Tm [] (Chor τ)) →
                 IfThenTm C C1 C2 ⇒[ T ] IfThenTm C' C1 C2
    -- If-then-else β-reduction
    stepIfThenT : ∀{τ ℓ} {e : Tm [] (Bnd ℓ Boolₑ)} →
                  tmProj e refl refl ≡ ttₑ →
                  (C1 C2 : Tm [] (Chor τ)) →
                  IfThenTm (DoneTm ℓ e) C1 C2 ⇒[ • ] C1
    stepIfThenF : ∀{τ ℓ} {e : Tm [] (Bnd ℓ Boolₑ)} →
                  tmProj e refl refl ≡ ffₑ →
                  (C1 C2 : Tm [] (Chor τ)) →
                  IfThenTm (DoneTm ℓ e) C1 C2 ⇒[ • ] C2

    stepLocalLet : ∀{T τ t ℓ} {C1 C1' : Tm [] (Chor (At t ℓ))}
                    {C2 : Tm (Bnd ℓ t ∷ []) (Chor τ)} →
                    C1 ⇒[ T ] C1' →
                    LocalLetTm C1 C2 ⇒[ T ] LocalLetTm C1' C2
    stepLocalLetV : ∀{τ t ℓ} {v : Tm [] (Bnd ℓ t)}
                    {C2 : Tm (Bnd ℓ t ∷ []) (Chor τ)} →
                    Valueₑ (tmProj v refl refl) →
                    LocalLetTm (DoneTm ℓ v) C2 ⇒[ • ] sub (IdSub ▸ v) C2

  -- Values cannot step any further
  valNoStep : ∀{τ T} {V C : Tm [] τ} → Value V → ¬ (V ⇒[ T ] C)
  valNoStep (valBnd e) ()
  valNoStep (valDone e-Val) (stepDone e⇒e') = valNoStepₑ e-Val e⇒e'
  valNoStep (valFun C) = λ ()

  -- Progress theorem for type-soundness
  progress : ∀{τ} (C : Tm [] τ) → (Value C) ⊎ Σ[ C' ∈ Tm [] τ ] Σ[ T ∈ _ ] (C ⇒[ T ] C')
  progress (constr (Local ℓ sₑ) es) = inl (valBnd (LocalTm ℓ sₑ es))
  progress (constr (Done ℓ t) (e ∷ [])) with progressₑ (tmProj e refl refl)
  ... | inl e-Value = inl (valDone e-Value)
  ... | inr (e' , e⇒e') = inr (
    DoneTm ℓ (tmInj e' refl) ,
    LocalStep ℓ ,
    stepDone (subst (tmProj e refl refl ⇒ₑ_) (sym (tmProjInj e' refl refl refl)) e⇒e'))
  progress (constr (Fun τ1 τ2) (C ∷ [])) = inl (valFun C)
  progress (constr (App τ1 τ2) (C1 ∷ C2 ∷ [])) with progress C1
  ... | inr (C1' , T , C1⇒C1') = inr (AppTm C1' C2 , T , stepFun C1⇒C1' C2)
  ... | inl (valFun C) with progress C2
  ... | inl C2-Val = inr (sub (IdSub ▸ C2) C , • , stepβ C C2-Val)
  ... | inr (C2' , T , C2⇒C2') = inr (AppTm (FunTm C) C2' , T , stepArg (valFun C) C2⇒C2')
  progress (constr (Fix τ) (C ∷ [])) = inr (sub (IdSub ▸ (FixTm C)) C , • , stepFix C)
  progress (constr (Send ℓ₁ ℓ₂ t) (C ∷ [])) with progress C
  ... | inl (valDone {t} {ℓ} {v} v-Val) =
    inr (DoneTm ℓ₂ (sendBndTm v ℓ₂) , SendStep ℓ₁ (tmProj v refl refl) v-Val ℓ₂ , stepSendVal v-Val ℓ₂)
  ... | inr (C' , T , C⇒C') = inr (SendTm C' ℓ₂ , T , stepSend C⇒C')
  progress (constr (Sync ℓ₁ ℓ₂ d τ) (C ∷ [])) = inr (C , SyncStep ℓ₁ d ℓ₂ , stepSync ℓ₁ d ℓ₂ C)
  progress (constr (IfThen ℓ τ) (C ∷ C1 ∷ C2 ∷ [])) with progress C
  ... | inr (C' , T , C⇒C') = inr (IfThenTm C' C1 C2 , T , stepIfThen C⇒C' C1 C2)
  ... | inl (valDone e-Val) with boolInvertₑ e-Val
  ... | inl refl = inr (C1 , • , stepIfThenT refl C1 C2)
  ... | inr refl = inr (C2 , • , stepIfThenF refl C1 C2) 
  progress (constr (LocalLet ℓ t τ) (C1 ∷ C2 ∷ [])) with progress C1
  ... | inl (valDone {v = v} v-Val) = inr (sub (IdSub ▸ v) C2 , • , stepLocalLetV v-Val)
  ... | inr (C1' , T , C1⇒C1') = inr (LocalLetTm C1' C2 , T , stepLocalLet C1⇒C1')
