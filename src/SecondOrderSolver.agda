{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin renaming (zero to zeroF; suc to sucF)
open import Data.List
open import Data.List.Properties
open import Data.Unit
open import Data.String hiding (_==_) renaming (_++_ to _++ₛ_)
open import Data.Maybe hiding (_>>=_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Agda.Builtin.Reflection
open import Reflection.Argument
open import Reflection.Term using (getName; _⋯⟅∷⟆_)
open import Reflection.TypeChecking.Monad.Syntax

open ≡-Reasoning

open import Common
open import SecondOrderSignatures

module SecondOrderSolver (⅀ : SecondOrderSignature) where

open SecondOrderSignature ⅀
open import SecondOrderLanguage ⅀
open import SecondOrderLanguageUntyped ⅀

--------------------------
-- TYPE REPRESENTATIONS --
--------------------------

data TyRep : Set where
  ℕ' URen' USub' UTm' UTmVec' : TyRep
  Ren' Sub' : Ctx → Ctx → TyRep
  Var' Tm' : Ctx → ⅀ .Knd → TyRep
  TmVec' : Ctx → List (Ctx × (⅀ .Knd)) → TyRep
  Fun : TyRep → TyRep → TyRep

-- Interpret as an actual type
⟦_⟧ : TyRep → Set
⟦ ℕ' ⟧ = ℕ
⟦ URen' ⟧ = URen
⟦ USub' ⟧ = USub
⟦ UTm' ⟧ = UTm
⟦ UTmVec' ⟧ = UTmVec
⟦ Ren' Γ1 Γ2 ⟧ = Ren Γ1 Γ2
⟦ Sub' Γ1 Γ2 ⟧ = Sub Γ1 Γ2
⟦ Var' Γ t ⟧ = Var Γ t
⟦ Tm' Γ t ⟧ = Tm Γ t
⟦ TmVec' Γ Σ ⟧ = TmVec Γ Σ
⟦ Fun A B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

-----------------
-- EXPRESSIONS --
-----------------

data Expr : (A : TyRep) → Set where
  -- Pure values
  ιExpr : ∀{A} (x : ⟦ A ⟧) → Expr A

  -- Function application
  EApp : ∀{A B} (f : Expr (Fun A B)) (a : Expr A) → Expr B

  -- Renamings
  ERenε : Expr (Ren' [] [])
  ERenKeep : ∀{Γ1 Γ2 t} → Expr (Ren' Γ1 Γ2) → Expr (Ren' (t ∷ Γ1) (t ∷ Γ2))
  ERenDrop : ∀{Γ1 Γ2 t} → Expr (Ren' Γ1 Γ2) → Expr (Ren' Γ1 (t ∷ Γ2))
  ERenId : ∀{Γ} → Expr (Ren' Γ Γ)
  _•E_ : ∀{Γ1 Γ2 Γ3} → Expr (Ren' Γ2 Γ3) → Expr (Ren' Γ1 Γ2) → Expr (Ren' Γ1 Γ3)
  EKeep* : ∀{Γ1 Γ2} → Expr (Ren' Γ1 Γ2) → ∀ Δ → Expr (Ren' (Δ ++ Γ1) (Δ ++ Γ2))
  EDrop* : ∀{Γ1 Γ2} → Expr (Ren' Γ1 Γ2) → ∀ Δ → Expr (Ren' Γ1 (Δ ++ Γ2))

  -- Substitutions
  ESubε : ∀{Γ} → Expr (Sub' [] Γ)
  _▸E_ : ∀{Γ1 Γ2 t} → Expr (Sub' Γ1 Γ2) → Expr (Tm' Γ2 t) → Expr (Sub' (t ∷ Γ1) Γ2)
  ESubId : ∀{Γ} → Expr (Sub' Γ Γ)
  _•◦E_ : ∀{Γ1 Γ2 Γ3} → Expr (Ren' Γ2 Γ3) → Expr (Sub' Γ1 Γ2) → Expr (Sub' Γ1 Γ3)
  _◦•E_ : ∀{Γ1 Γ2 Γ3} → Expr (Sub' Γ2 Γ3) → Expr (Ren' Γ1 Γ2) → Expr (Sub' Γ1 Γ3)
  _◦E_ : ∀{Γ1 Γ2 Γ3} → Expr (Sub' Γ2 Γ3) → Expr (Sub' Γ1 Γ2) → Expr (Sub' Γ1 Γ3)
  ESubKeep* : ∀{Γ1 Γ2} → Expr (Sub' Γ1 Γ2) → ∀ Δ → Expr (Sub' (Δ ++ Γ1) (Δ ++ Γ2))
  ιE : ∀{Γ1 Γ2} → Expr (Ren' Γ1 Γ2) → Expr (Sub' Γ1 Γ2)

  -- Variables
  V0 : ∀{Γ t} → Expr (Var' (t ∷ Γ) t)
  VS : ∀{Γ s t} → Expr (Var' Γ t) → Expr (Var' (s ∷ Γ) t)
  renEVar : ∀{Γ1 Γ2 t} → Expr (Ren' Γ1 Γ2) → Expr (Var' Γ1 t) → Expr (Var' Γ2 t)

  -- Terms
  varE : ∀{Γ t} → Expr (Var' Γ t) → Expr (Tm' Γ t)
  constrE : ∀{Γ} (s : ⅀ .TyShape) (es : Expr (TmVec' Γ (⅀ .TyPos s .fst))) → Expr (Tm' Γ (⅀ .TyPos s .snd))
  renETm : ∀{Γ1 Γ2 t} → Expr (Ren' Γ1 Γ2) → Expr (Tm' Γ1 t) → Expr (Tm' Γ2 t)
  subETm : ∀{Γ1 Γ2 t} → Expr (Sub' Γ1 Γ2) → Expr (Tm' Γ1 t) → Expr (Tm' Γ2 t)
  subEVar : ∀{Γ1 Γ2 t} → Expr (Sub' Γ1 Γ2) → Expr (Var' Γ1 t) → Expr (Tm' Γ2 t)

  -- Term vectors
  []E : ∀{Γ} → Expr (TmVec' Γ [])
  _∷E_ : ∀{Γ Δ t Σ} →
        (e : Expr (Tm' (Δ ++ Γ) t)) →
        (es : Expr (TmVec' Γ Σ)) →
        Expr (TmVec' Γ ((Δ , t) ∷ Σ))
  renETmVec : ∀{Γ1 Γ2 Σ} → Expr (Ren' Γ1 Γ2) → Expr (TmVec' Γ1 Σ) → Expr (TmVec' Γ2 Σ)
  subETmVec : ∀{Γ1 Γ2 Σ} → Expr (Sub' Γ1 Γ2) → Expr (TmVec' Γ1 Σ) → Expr (TmVec' Γ2 Σ)

  -- Raw renamings
  EURenε : Expr URen'
  EURenKeep : Expr URen' → Expr URen'
  EURenDrop : Expr URen' → Expr URen'
  EURenId : Expr URen'
  _•U_ : Expr URen' → Expr URen' → Expr URen'
  EUKeep* : Expr URen' → Expr ℕ' → Expr URen'
  EUDrop* : Expr URen' → Expr ℕ' → Expr URen'
  untyERen : ∀{Γ1 Γ2} → Expr (Ren' Γ1 Γ2) → Expr URen'

  -- Raw substitutions
  EUSubε : Expr USub'
  _▸U_ : Expr USub' → Expr UTm' → Expr USub'
  EUSubId : Expr USub'
  _•◦U_ : Expr URen' → Expr USub' → Expr USub'
  _◦U'_ : Expr USub' → Expr USub' → Expr USub'
  untyESub : ∀{Γ1 Γ2} → Expr (Sub' Γ1 Γ2) → Expr USub'

  -- Raw variables/natural numbers
  Z : Expr ℕ'
  S : Expr ℕ' → Expr ℕ'
  renEUVar : Expr URen' → Expr ℕ' → Expr ℕ'
  untyEVar : ∀{Γ t} → Expr (Var' Γ t) → Expr ℕ'

  -- Raw terms
  varU : Expr ℕ' → Expr UTm'
  constrU : (s : ⅀ .TyShape) (es : Expr UTmVec') → Expr UTm'
  renEUTm : Expr URen' → Expr UTm' → Expr UTm'
  subEUTm : Expr USub' → Expr UTm' → Expr UTm'
  subEUVar : Expr USub' → Expr ℕ' → Expr UTm'
  untyETm : ∀{Γ t} → Expr (Tm' Γ t) → Expr UTm'

  -- Raw term vectors
  []U : Expr UTmVec'
  _∷U_ : (ek : Expr UTm' × Expr ℕ') →
         (es : Expr UTmVec') →
         Expr UTmVec'
  renEUTmVec : Expr URen' → Expr UTmVec' → Expr UTmVec'
  subEUTmVec : Expr USub' → Expr UTmVec' → Expr UTmVec'
  untyETmVec : ∀{Γ Σ} → Expr (TmVec' Γ Σ) → Expr UTmVec'

---------------------
-- INTERPRETATIONS --
---------------------

interp : ∀{A} → Expr A → ⟦ A ⟧
interp (ιExpr x) = x
interp (EApp f x) = interp f (interp x)

interp ERenε = ε
interp (ERenKeep ξ) = Keep (interp ξ)
interp (ERenDrop ξ) = Drop (interp ξ)
interp ERenId = IdRen
interp (ξ1 •E ξ2) = interp ξ1 • interp ξ2
interp (EKeep* ξ Δ) = Keep* (interp ξ) Δ
interp (EDrop* ξ Δ) = Drop* (interp ξ) Δ

interp ESubε = ε
interp (σ ▸E e) = interp σ ▸ interp e
interp ESubId = IdSub
interp (ξ •◦E σ) = interp ξ •◦ interp σ
interp (σ ◦•E ξ) = interp σ ◦• interp ξ
interp (σ1 ◦E σ2) = interp σ1 ◦ interp σ2
interp (ESubKeep* σ Δ) = KeepSub* (interp σ) Δ
interp (ιE ξ) = ι (interp ξ)

interp V0 = V0
interp (VS x) = VS (interp x)
interp (renEVar ξ x) = renVar (interp ξ) (interp x)

interp (varE x) = var (interp x)
interp (constrE s es) = constr s (interp es)
interp (renETm ξ e) = ren (interp ξ) (interp e)
interp (subETm σ e) = sub (interp σ) (interp e)
interp (subEVar σ x) = subVar (interp σ) (interp x)

interp []E = []
interp (e ∷E es) = interp e ∷ interp es
interp (renETmVec ξ es) = renVec (interp ξ) (interp es)
interp (subETmVec σ es) = subVec (interp σ) (interp es)

interp EURenε = id
interp (EURenKeep ξ) = UKeep (interp ξ)
interp (EURenDrop ξ) = UDrop (interp ξ)
interp EURenId = id
interp (ξ1 •U ξ2) = interp ξ1 ∘ interp ξ2
interp (EUKeep* ξ k) = UKeep* (interp ξ) (interp k)
interp (EUDrop* ξ k) = UDrop* (interp ξ) (interp k)
interp (untyERen e) = untyRen (interp e)

interp EUSubε = var
interp (σ ▸U e) = interp σ ▹ interp e
interp EUSubId = var
interp (ξ •◦U σ) = URenSub (interp ξ) (interp σ)
interp (σ1 ◦U' σ2) = interp σ1 ◦U interp σ2
interp (untyESub σ) = untySub (interp σ)

interp Z = zero
interp (S n) = suc (interp n)
interp (renEUVar ξ n) = interp ξ (interp n)
interp (untyEVar n) = untyVar (interp n)

interp (varU n) = var (interp n)
interp (constrU s es) = constr s (interp es)
interp (renEUTm ξ e) = renUnty (interp ξ) (interp e)
interp (subEUTm σ e) = subUnty (interp σ) (interp e)
interp (subEUVar σ x) = interp σ (interp x)
interp (untyETm e) = unty (interp e)

interp []U = []
interp ((e , k) ∷U es) = (interp e , interp k) ∷ interp es
interp (renEUTmVec ξ es) = renVecUnty (interp ξ) (interp es)
interp (subEUTmVec σ es) = subVecUnty (interp σ) (interp es)
interp (untyETmVec es) = untyVec (interp es)

-------------------------------
-- EXPRESSION SIMPLIFICATION --
-------------------------------

-- Apply Keep
simplKeep : ∀{Γ1 Γ2 t} (ξ : Expr (Ren' Γ1 Γ2)) → Σ[ ξ' ∈ Expr _ ] interp ξ' ≡ Keep {t = t} (interp ξ)
simplKeep ERenId = ERenId , refl
simplKeep ξ = ERenKeep ξ , refl

-- Fuse two renamings
simpl•≡ : ∀{Γ1 Γ2 Γ2' Γ3} (ξ1 : Expr (Ren' Γ2 Γ3)) (ξ2 : Expr (Ren' Γ1 Γ2')) →
          (p : Γ2' ≡ Γ2) →
          Σ[ ξ' ∈ Expr (Ren' Γ1 Γ3) ] interp ξ' ≡ interp ξ1 • subst (Ren Γ1) p (interp ξ2)
simpl•≡ ERenId ξ2 refl = ξ2 , sym (Id• (interp ξ2))
simpl•≡ ξ1 ERenId refl = ξ1 , sym (•Id (interp ξ1))          
simpl•≡ ERenε ERenε refl = ERenε , refl
simpl•≡ (ERenKeep ξ1) (ERenKeep ξ2) refl with simpl•≡ ξ1 ξ2 refl
... | (ξ' , q) = ERenKeep ξ' , cong Keep q
simpl•≡ (ERenKeep ξ1) (ERenDrop ξ2) refl with simpl•≡ ξ1 ξ2 refl
... | (ξ' , q) = ERenDrop ξ' , cong Drop q
simpl•≡ (ξ1 •E ξ2) ξ3 refl with simpl•≡ ξ2 ξ3 refl
... | (ξ' , p) with simpl•≡ ξ1 ξ' refl
... | (ξ'' , q) = ξ'' , q ∙ cong (interp ξ1 •_) p ∙ sym (•• (interp ξ1) (interp ξ2) (interp ξ3))
simpl•≡ {Γ1} {Γ2} {Γ2'} {Γ3} ξ1 ξ2 p = 
  J (λ Γ2 p → (ξ1 : Expr (Ren' Γ2 Γ3)) (ξ2 : Expr (Ren' Γ1 Γ2')) →
      Σ[ ξ' ∈ Expr (Ren' Γ1 Γ3) ] interp ξ' ≡ interp ξ1 • subst (Ren Γ1) p (interp ξ2))
    (λ ξ1 ξ2 → (ξ1 •E ξ2) , refl)
    Γ2 p ξ1 ξ2

simpl• : ∀{Γ1 Γ2 Γ3} (ξ1 : Expr (Ren' Γ2 Γ3)) (ξ2 : Expr (Ren' Γ1 Γ2)) →
            Σ[ ξ' ∈ Expr _ ] interp ξ' ≡ interp ξ1 • interp ξ2
simpl• ξ1 ξ2 = simpl•≡ ξ1 ξ2 refl

-- Rename a variable
simplRenVar≡ : ∀{Γ1 Γ1' Γ2 t} (ξ : Expr (Ren' Γ1 Γ2)) (x : Expr (Var' Γ1' t)) →
              (p : Γ1' ≡ Γ1) →
              Σ[ x' ∈ Expr (Var' Γ2 t) ] interp x' ≡ renVar (interp ξ) (subst (flip Var t) p (interp x))
simplRenVar≡ ERenId x refl = x , sym (renVarId (interp x))
simplRenVar≡ ERenε x refl = x , sym (renVarId (interp x))              
simplRenVar≡ (ERenKeep ξ) V0 refl = V0 , refl
simplRenVar≡ (ERenKeep ξ) (VS x) refl with simplRenVar≡ ξ x refl
... | (x' , p) = VS x' , cong VS p
simplRenVar≡ (ERenDrop ξ) x refl with simplRenVar≡ ξ x refl
... | (x' , p) = VS x' , cong VS p
simplRenVar≡ ξ1 (renEVar ξ2 x) refl with simpl• ξ1 ξ2
... | (ξ' , p) =
  renEVar ξ' x ,
  cong (flip renVar (interp x)) p
  ∙ renVar• (interp ξ1) (interp ξ2) (interp x)
simplRenVar≡ (ξ1 •E ξ2) x refl with simplRenVar≡ ξ2 x refl
... | (x' , p) with simplRenVar≡ ξ1 x' refl
... | (x'' , q) = x'' , q ∙ cong (renVar (interp ξ1)) p ∙ sym (renVar• (interp ξ1) (interp ξ2) (interp x))
simplRenVar≡ {Γ1} {Γ1'} {Γ2} {t} ξ x p =
    J (λ Γ1 p → (ξ : Expr (Ren' Γ1 Γ2)) (x : Expr (Var' Γ1' t)) →
      Σ[ x' ∈ Expr (Var' Γ2 t) ] interp x' ≡ renVar (interp ξ) (subst (flip Var t) p (interp x)))
      (λ ξ x → renEVar ξ x , refl)
      Γ1 p ξ x

simplRenVar : ∀{Γ1 Γ2 t} (ξ : Expr (Ren' Γ1 Γ2)) (x : Expr (Var' Γ1 t)) →
          Σ[ x' ∈ Expr _ ] interp x' ≡ renVar (interp ξ) (interp x)
simplRenVar ξ x = simplRenVar≡ ξ x refl

-- Convert a renaming to a substitution
simplι : ∀{Γ1 Γ2} (ξ : Expr (Ren' Γ1 Γ2)) → Σ[ σ ∈ Expr _ ] interp σ ≡ ι (interp ξ)
simplι ERenε = ESubε , refl
simplι ERenId = ESubId , refl
simplι ξ = ιE ξ , refl

-- Rename a term
simplRen : ∀{Γ1 Γ2 t} (ξ : Expr (Ren' Γ1 Γ2)) (e : Expr (Tm' Γ1 t)) →
           Σ[ e' ∈ Expr _ ] interp e' ≡ ren (interp ξ) (interp e)
-- Rename a vector of terms
simplRenVec : ∀{Γ1 Γ2 Σ} (ξ : Expr (Ren' Γ1 Γ2)) (es : Expr (TmVec' Γ1 Σ)) →
            Σ[ es' ∈ Expr _ ] interp es' ≡ renVec (interp ξ) (interp es)
-- Rename a substitution
simpl•◦ : ∀{Γ1 Γ2 Γ3} (ξ : Expr (Ren' Γ2 Γ3)) (σ : Expr (Sub' Γ1 Γ2)) →
          Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp ξ •◦ interp σ

simplRen ERenε e = e , sym (renId (interp e))
simplRen ERenId e = e , sym (renId (interp e))
simplRen ξ (varE x) with simplRenVar ξ x
... | (x' , p) = varE x' , cong var p
simplRen ξ (constrE s es) with simplRenVec ξ es
... | (es' , p) = constrE s es' , cong (constr s) p
simplRen ξ1 (renETm ξ2 e) with simpl• ξ1 ξ2
... | (ξ' , p) =
  renETm ξ' e ,
  cong (flip ren (interp e)) p
  ∙ ren• (interp ξ1) (interp ξ2) (interp e)
simplRen ξ (subETm σ e) with simpl•◦ ξ σ
... | (σ' , p) =
  subETm σ' e ,
  cong (flip sub (interp e)) p
  ∙ sub•◦ (interp ξ) (interp σ) (interp e)
simplRen ξ (subEVar σ x) with simpl•◦ ξ σ
... | (σ' , p) = subEVar σ' x ,
  cong (flip subVar (interp x)) p
  ∙ subVar•◦ (interp ξ) (interp σ) (interp x)
simplRen ξ e = renETm ξ e , refl

simplRenVec ERenε es = es , sym (renVecId (interp es))
simplRenVec ERenId es = es , sym (renVecId (interp es))
simplRenVec ξ []E = []E , refl
simplRenVec ξ (_∷E_ {Δ = Δ} e es) with simplRen (EKeep* ξ Δ) e | simplRenVec ξ es
... | (e' , p) | (es' , q) = e' ∷E es' , cong₂ _∷_ p q
simplRenVec ξ1 (renETmVec ξ2 es) with simpl• ξ1 ξ2
... | (ξ' , p) =
  renETmVec ξ' es ,
  cong (flip renVec (interp es)) p
  ∙ renVec• (interp ξ1) (interp ξ2) (interp es)
simplRenVec ξ (subETmVec σ es) with simpl•◦ ξ σ
... | (σ' , p) =
  subETmVec σ' es ,
  cong (flip subVec (interp es)) p
  ∙ subVec•◦ (interp ξ) (interp σ) (interp es)
simplRenVec ξ es = renETmVec ξ es , refl

simpl•◦≡ : ∀{Γ1 Γ2 Γ2' Γ3} (ξ : Expr (Ren' Γ2 Γ3)) (σ : Expr (Sub' Γ1 Γ2')) →
           (p : Γ2' ≡ Γ2) → Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp ξ •◦ subst (Sub Γ1) p (interp σ)
simpl•◦≡ ξ ESubId refl with simplι ξ
... | (σ , p) =
  σ , 
  p
  ∙ cong ι (sym (•Id (interp ξ)))
  ∙ sym (•◦ι (interp ξ) IdRen)
simpl•◦≡ ERenId σ refl = σ , sym (Id•◦ (interp σ))
simpl•◦≡ ξ1 (ιE ξ2) refl with simpl• ξ1 ξ2
... | (ξ' , p) with simplι ξ'
... | (σ' , q) = 
  σ' , 
  q
  ∙ cong ι p
  ∙ sym (•◦ι (interp ξ1) (interp ξ2))           
simpl•◦≡ ξ ESubε refl = ESubε , refl
simpl•◦≡ ξ (σ ▸E e) refl with simpl•◦≡ ξ σ refl | simplRen ξ e
... | (σ' , p) | (e' , q) = σ' ▸E e' , cong₂ _▸_ p q
simpl•◦≡ ξ1 (ξ2 •◦E σ) refl with simpl• ξ1 ξ2
... | (ξ' , p) with simpl•◦≡ ξ' σ refl
... | (σ' , q) = σ' ,
  q
  ∙ cong (_•◦ interp σ) p
  ∙ ••◦ (interp ξ1) (interp ξ2) (interp σ)
simpl•◦≡ ξ (σ1 ◦E σ2) refl with simpl•◦≡ ξ σ1 refl
... | (σ' , p) =
  σ' ◦E σ2 ,
  cong (_◦ interp σ2) p
  ∙ sym (•◦◦ (interp ξ) (interp σ1) (interp σ2))
simpl•◦≡ ξ1 (σ ◦•E ξ2) refl with simpl•◦≡ ξ1 σ refl
... | (σ' , p) =
  σ' ◦•E ξ2 ,
  cong (_◦• interp ξ2) p
  ∙ sym (•◦◦• (interp ξ1) (interp σ) (interp ξ2))
simpl•◦≡ {Γ1} {Γ2} {Γ2'} {Γ3} ξ σ p =
  J (λ Γ2 p → (ξ : Expr (Ren' Γ2 Γ3)) (σ : Expr (Sub' Γ1 Γ2')) →
    Σ[ σ' ∈ Expr (Sub' Γ1 Γ3) ] interp σ' ≡ interp ξ •◦ subst (Sub Γ1) p (interp σ))
    (λ ξ σ → ξ •◦E σ , refl)
    Γ2 p ξ σ

simpl•◦ ξ σ = simpl•◦≡ ξ σ refl

-- Substitute after a renaming
simpl◦•≡ : ∀{Γ1 Γ2 Γ2' Γ3} (σ : Expr (Sub' Γ2 Γ3)) (ξ : Expr (Ren' Γ1 Γ2')) →
           (p : Γ2' ≡ Γ2) →
           Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp σ ◦• subst (Ren Γ1) p (interp ξ)         
simpl◦•≡ σ ERenε refl = ESubε , refl
simpl◦•≡ σ ERenId refl = σ , sym (◦•Id (interp σ))
simpl◦•≡ ESubId ξ refl with simplι ξ
... | (σ , p) = σ , p ∙ sym (Id◦• (interp ξ))
simpl◦•≡ (ιE ξ1) ξ2 refl with simpl• ξ1 ξ2
... | (ξ' , p) with simplι ξ'
... | (σ , q) = 
  σ , 
  q
  ∙ cong ι p
  ∙ sym (ι◦• (interp ξ1) (interp ξ2))
simpl◦•≡ (σ ▸E e) (ERenDrop ξ) refl = simpl◦•≡ σ ξ refl
simpl◦•≡ (σ ▸E e) (ERenKeep ξ) refl with simpl◦•≡ σ ξ refl
... | (σ' , p) = σ' ▸E e , cong (_▸ interp e) p
simpl◦•≡ (ξ1 •◦E σ) ξ2 refl with simpl◦•≡ σ ξ2 refl
... | (σ' , p) =
  ξ1 •◦E σ' ,
  cong (interp ξ1 •◦_) p
  ∙ •◦◦• (interp ξ1) (interp σ) (interp ξ2)
simpl◦•≡ (σ ◦•E ξ1) ξ2 refl with simpl• ξ1 ξ2
... | (ξ' , p) with simpl◦•≡ σ ξ' refl
... | (σ' , q) =
  σ' ,
  q
  ∙ cong (interp σ ◦•_) p
  ∙ ◦•• (interp σ) (interp ξ1) (interp ξ2)
simpl◦•≡ (σ1 ◦E σ2) ξ refl with simpl◦•≡ σ2 ξ refl
... | (σ' , p) =
  σ1 ◦E σ'
  , cong (interp σ1 ◦_) p
  ∙ ◦◦• (interp σ1) (interp σ2) (interp ξ)
simpl◦•≡ {Γ1} {Γ2} {Γ2'} {Γ3} σ ξ p =
  J (λ Γ2 p → (σ : Expr (Sub' Γ2 Γ3)) (ξ : Expr (Ren' Γ1 Γ2')) →
    Σ[ σ' ∈ Expr (Sub' Γ1 Γ3) ] interp σ' ≡ interp σ ◦• subst (Ren Γ1) p (interp ξ))
    (λ σ ξ → σ ◦•E ξ , refl)
    Γ2 p σ ξ

simpl◦• : ∀{Γ1 Γ2 Γ3} (σ : Expr (Sub' Γ2 Γ3)) (ξ : Expr (Ren' Γ1 Γ2)) →
          Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp σ ◦• interp ξ
simpl◦• σ ξ = simpl◦•≡ σ ξ refl

-- Substitute a variable
simplSubVar : ∀{Γ1 Γ2 t} (σ : Expr (Sub' Γ1 Γ2)) (x : Expr (Var' Γ1 t)) →
              Σ[ x' ∈ Expr _ ] interp x' ≡ subVar (interp σ) (interp x)
-- Substitute a term
simplSub : ∀{Γ1 Γ2 t} (σ : Expr (Sub' Γ1 Γ2)) (e : Expr (Tm' Γ1 t)) →
         Σ[ e' ∈ Expr _ ] interp e' ≡ sub (interp σ) (interp e)
-- Substitute a vector of terms
simplSubVec : ∀{Γ1 Γ2 Σ} (σ : Expr (Sub' Γ1 Γ2)) (es : Expr (TmVec' Γ1 Σ)) →
              Σ[ es' ∈ Expr _ ] interp es' ≡ subVec (interp σ) (interp es)
-- Fuse two substitutions              
simpl◦ : ∀{Γ1 Γ2 Γ3} (σ1 : Expr (Sub' Γ2 Γ3)) (σ2 : Expr (Sub' Γ1 Γ2)) →
         Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp σ1 ◦ interp σ2

simplSubVar≡ : ∀{Γ1 Γ1' Γ2 t} (σ : Expr (Sub' Γ1 Γ2)) (x : Expr (Var' Γ1' t)) →
               (p : Γ1' ≡ Γ1) → Σ[ x' ∈ Expr _ ] interp x' ≡ subVar (interp σ) (subst (flip Var t) p (interp x))
simplSubVar≡ (σ ▸E e) V0 refl = e , refl
simplSubVar≡ (σ ▸E e) (VS x) refl = simplSubVar≡ σ x refl
simplSubVar≡ ESubId x refl = varE x , sym (subVarId (interp x))
simplSubVar≡ σ (renEVar ξ x) refl with simpl◦• σ ξ
... | (σ' , p) =
  subEVar σ' x ,
  cong (flip subVar (interp x)) p
  ∙ subVar◦• (interp σ) (interp ξ) (interp x)
simplSubVar≡ (ξ •◦E σ) x refl with simplSubVar≡ σ x refl
... | (e , p) with simplRen ξ e
... | (e' , q) =
  e' ,
  q
  ∙ cong (ren (interp ξ)) p
  ∙ sym (subVar•◦ (interp ξ) (interp σ) (interp x))
simplSubVar≡ (ιE ξ) x refl with simplRenVar ξ x
... | (x' , p) =
  varE x' ,
  cong var p
  ∙ sym (subVarι (interp ξ) (interp x))
simplSubVar≡ {Γ1} {Γ1'} {Γ2} {t} σ x p =
  J (λ Γ1 p → (σ : Expr (Sub' Γ1 Γ2)) (x : Expr (Var' Γ1' t)) →
    Σ[ e ∈ Expr (Tm' Γ2 t) ] interp e ≡ subVar (interp σ) (subst (flip Var t) p (interp x)))
    (λ σ x → subEVar σ x , refl)
    Γ1 p σ x

simplSubVar σ x = simplSubVar≡ σ x refl

simplSub ESubId e = e , sym (subId (interp e))
simplSub (ιE ξ) e with simplRen ξ e
... | (e' , p) =
  e' ,
  p
  ∙ sym (subι (interp ξ) (interp e))
simplSub σ (varE x) = simplSubVar σ x
simplSub σ (constrE s es) with simplSubVec σ es
... | (es' , p) = constrE s es' , cong (constr s) p
simplSub σ (renETm ξ e) with simpl◦• σ ξ
... | (σ' , p) with simplSub σ' e
... | (e' , q) = e' , 
  q
  ∙ cong (flip sub (interp e)) p
  ∙ sub◦• (interp σ) (interp ξ) (interp e)
simplSub σ1 (subETm σ2 e) with simpl◦ σ1 σ2
... | (σ' , p) = subETm σ' e ,
  cong (flip sub (interp e)) p
  ∙ sub◦ (interp σ1) (interp σ2) (interp e)
simplSub σ1 (subEVar σ2 x) with simpl◦ σ1 σ2
... | (σ' , p) = subEVar σ' x ,
  cong (flip subVar (interp x)) p
  ∙ subVar◦ (interp σ1) (interp σ2) (interp x)
simplSub σ e = subETm σ e , refl

simplSubVec ESubId es = es , sym (subVecId (interp es))
simplSubVec σ []E = []E , refl
simplSubVec σ (_∷E_ {Δ = Δ} e es) with simplSub (ESubKeep* σ Δ) e | simplSubVec σ es
... | (e' , p) | (es' , q) = e' ∷E es' , cong₂ _∷_ p q
simplSubVec σ (renETmVec ξ es) with simpl◦• σ ξ
... | (σ' , p) =
  subETmVec σ' es ,
  cong (flip subVec (interp es)) p
  ∙ subVec◦• (interp σ) (interp ξ) (interp es)
simplSubVec σ1 (subETmVec σ2 es) with simpl◦ σ1 σ2
... | (σ' , p) =
  subETmVec σ' es ,
  cong (flip subVec (interp es)) p
  ∙ subVec◦ (interp σ1) (interp σ2) (interp es)
simplSubVec σ es = subETmVec σ es , refl

simpl◦≡ : ∀{Γ1 Γ2 Γ2' Γ3} (σ1 : Expr (Sub' Γ2 Γ3)) (σ2 : Expr (Sub' Γ1 Γ2')) →
          (p : Γ2' ≡ Γ2) → Σ[ σ' ∈ Expr _ ] interp σ' ≡ interp σ1 ◦ subst (Sub Γ1) p (interp σ2)
simpl◦≡ ESubId σ2 refl = σ2 , sym (Id◦ (interp σ2))
simpl◦≡ σ1 ESubε refl = ESubε , refl
simpl◦≡ σ1 (σ2 ▸E e) refl with simpl◦≡ σ1 σ2 refl | simplSub σ1 e
... | (σ' , p) | (e' , q) = σ' ▸E e' , cong₂ _▸_ p q
simpl◦≡ σ1 ESubId refl = σ1 , sym (◦Id (interp σ1))
simpl◦≡ σ1 (ξ •◦E σ2) refl with simpl◦• σ1 ξ
... | (σ' , p) with simpl◦≡ σ' σ2 refl
... | (σ'' , q) = 
  σ'' , 
  q
  ∙ cong (_◦ interp σ2) p
  ∙ sym (◦•◦ (interp σ1) (interp ξ) (interp σ2))
simpl◦≡ σ1 (σ2 ◦E σ3) refl with simpl◦≡ σ1 σ2 refl
... | (σ' , p) with simpl◦≡ σ' σ3 refl
... | (σ'' , q) = 
  σ'' , 
  q
  ∙ cong (_◦ interp σ3) p
  ∙ sym (◦◦ (interp σ1) (interp σ2) (interp σ3))
simpl◦≡ σ1 (ιE ξ) refl with simpl◦• σ1 ξ
... | (σ' , p) =
  σ' ,
  p
  ∙ sym (◦ι (interp σ1) (interp ξ))
simpl◦≡ {Γ1} {Γ2} {Γ2'} {Γ3} σ1 σ2 p = J (λ Γ2 p → (σ1 : Expr (Sub' Γ2 Γ3)) (σ2 : Expr (Sub' Γ1 Γ2')) →
    Σ[ σ' ∈ Expr (Sub' Γ1 Γ3) ] interp σ' ≡ interp σ1 ◦ subst (Sub Γ1) p (interp σ2))
    (λ σ1 σ2 → σ1 ◦E σ2 , refl)
    Γ2 p σ1 σ2

simpl◦ σ1 σ2 = simpl◦≡ σ1 σ2 refl

{-
Full simplification procedure

First recursively simplify all subexpressions,
then combine the expression back together by using
the simplifying constructor implementations above
-}
simpl : ∀{A} (e : Expr A) → Σ[ e' ∈ Expr A ] interp e' ≡ interp e
simpl (ιExpr x) = ιExpr x , refl
simpl (EApp {B = B} f e) with simpl f | simpl e
... | (f' , p) | (e' , q) = EApp f' e' , cong₂ (λ x y → x y) p q
simpl ERenε = ERenε , refl
simpl (ERenKeep {t = t} ξ) with simpl ξ
... | (ξ' , p) with simplKeep {t = t} ξ'
... | (ξ'' , q) = ξ'' , q ∙ cong Keep p
simpl (ERenDrop {t = t} ξ) with simpl ξ
... | (ξ' , p) = ERenDrop ξ' , cong Drop p
simpl (ξ1 •E ξ2) with simpl ξ1 | simpl ξ2
... | (ξ1' , p) | (ξ2' , q) with simpl• ξ1' ξ2'
... | (ξ' , r) = ξ' , r ∙ cong₂ _•_ p q
simpl (EKeep* ξ Δ) with simpl ξ
... | (ξ' , p) = EKeep* ξ' Δ , cong (flip Keep* Δ) p
simpl (EDrop* ξ Δ) with simpl ξ
... | (ξ' , p) = EDrop* ξ' Δ , cong (flip Drop* Δ) p
simpl (σ ▸E e) with simpl σ | simpl e
... | (σ' , p) | (e' , q) = (σ' ▸E e') , cong₂ _▸_ p q
simpl (ξ •◦E σ) with simpl ξ | simpl σ
... | (ξ' , p) | (σ' , q) with simpl•◦ ξ' σ'
... | (σ'' , r) = σ'' , r ∙ cong₂ _•◦_ p q
simpl (σ1 ◦E σ2) with simpl σ1 | simpl σ2
... | (σ1' , p) | (σ2' , q) with simpl◦ σ1' σ2'
... | (σ' , r) = σ' , r ∙ cong₂ _◦_ p q
simpl (σ ◦•E ξ) with simpl σ | simpl ξ
... | (σ' , p) | (ξ' , q) with simpl◦• σ' ξ'
... | (σ'' , r) = σ'' , r ∙ cong₂ _◦•_ p q
simpl (ESubKeep* σ Δ) with simpl σ
... | (σ' , p) = ESubKeep* σ' Δ , cong (flip KeepSub* Δ) p
simpl (VS n) with simpl n
... | (n' , p) = VS n' , cong VS p
simpl (renEVar ξ x) with simpl ξ | simpl x
... | (ξ' , p) | (x' , q) with simplRenVar ξ' x'
... | (x'' , r) = x'' , r ∙ cong₂ renVar p q
simpl (varE x) with simpl x
... | (x' , p) = varE x' , cong var p
simpl (constrE s es) with simpl es
... | (es' , p) = constrE s es' , cong (constr s) p
simpl (renETm ξ e) with simpl ξ | simpl e
... | (ξ' , p) | (e' , q) with simplRen ξ' e'
... | (e'' , r) = e'' , r ∙ cong₂ ren p q
simpl (subETm σ e) with simpl σ | simpl e
... | (σ' , p) | (e' , q) with simplSub σ' e'
... | (e'' , r) = e'' , r ∙ cong₂ sub p q
simpl (subEVar σ x) with simpl σ | simpl x
... | (σ' , p) | (x' , q) with simplSubVar σ' x'
... | (e , r) = e , r ∙ cong₂ subVar p q
simpl (e ∷E es) with simpl e | simpl es
... | (e' , p) | (es' , q) = (e' ∷E es') , cong₂ _∷_ p q
simpl (renETmVec ξ es) with simpl ξ | simpl es
... | (ξ' , p) | (es' , q) with simplRenVec ξ' es'
... | (es'' , r) = es'' , r ∙ cong₂ renVec p q
simpl (subETmVec σ es) with simpl σ | simpl es
... | (σ' , p) | (es' , q) with simplSubVec σ' es'
... | (es'' , r) = es'' , r ∙ cong₂ subVec p q
-- simpl (EURenKeep ξ) = {!   !}
-- simpl (EURenDrop ξ) = {!   !}
-- simpl (ξ1 •U ξ2) = {!   !}
-- simpl (EUKeep* ξ Δ) = {!   !}
-- simpl (EUDrop* ξ Δ) = {!   !}
-- simpl (untyERen ξ) = {!   !}
-- simpl (σ ▸U e) = {!   !}
-- simpl (ξ •◦U σ) = {!   !}
-- simpl (σ1 ◦U' σ2) = {!   !}
-- simpl (ιE ξ) with simpl ξ
-- ... | (ξ' , p) with simplι ξ'
-- ... | (σ , q) = σ , q ∙ cong ι p
-- simpl (untyESub σ) = {!   !}
-- simpl (S n) with simpl n
-- ... | (n' , p) = S n' , cong suc p
-- simpl (renEUVar ξ x) = {!   !}
-- simpl (untyEVar x) = {!   !}
-- simpl (varU x) with simpl x
-- ... | (x' , p) = varU x' , cong var p
-- simpl (constrU s es) = {!   !}
-- simpl (renEUTm ξ e) = {!   !}
-- simpl (subEUTm σ e) = {!   !}
-- simpl (subEUVar e e₁) = {!   !}
-- simpl (untyETm e) = {!   !}
-- simpl ((e , k) ∷U es) = {!   !}
-- simpl (renEUTmVec ξ es) = {!   !}
-- simpl (subEUTmVec σ es) = {!   !}
-- simpl (untyETmVec es) = {!   !}
simpl e = e , refl
 
simplFun : ∀{A} → Expr A → Expr A
simplFun e = simpl e .fst

simpl≡ : ∀{A} (e : Expr A) → interp (simplFun e) ≡ interp e
simpl≡ e = simpl e .snd
