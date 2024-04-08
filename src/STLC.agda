{-# OPTIONS --safe #-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common

module STLC where

-- Simple types
data Typ : Set where
  Nat : Typ
  Emp : Typ
  Arrow : Typ → Typ → Typ

data Shape : Set where
  Lam : (s t : Typ) → Shape
  App : (s t : Typ) → Shape
  Zero : Shape
  Suc : Shape
  NatRec : (t : Typ) → Shape
  Fix : (t : Typ) → Shape

Pos : Shape → List (List Typ × Typ) × Typ
-- Lam (s : *) (t : *) [s]t : s⇒t
Pos (Lam s t) = (s ∷ [] , t) ∷ [] , Arrow s t
-- App (s : *) (t : *) s⇒t s : t
Pos (App s t) = ([] , Arrow s t) ∷ ([] , s) ∷ [] , t
-- Zero : Nat
Pos Zero = [] , Nat
-- Suc Nat : Nat
Pos Suc = ([] , Nat) ∷ [] , Nat
-- NatRec (t : *) t t⇒t Nat : t
Pos (NatRec t) = ([] , t) ∷ ([] , Arrow t t) ∷ ([] , Nat) ∷ [] , t
-- Fix (t : *) [t]t : t
Pos (Fix t) = (t ∷ [] , t) ∷ [] , t

open import SecondOrderSyntax Typ Shape Pos

-- Aliases for each constructor
LamTm : ∀{Γ s t} → Tm (s ∷ Γ) t → Tm Γ (Arrow s t)
LamTm {s = s} {t} e = constr (Lam s t) (e ∷ [])

AppTm : ∀{Γ s t} → Tm Γ (Arrow s t) → Tm Γ s → Tm Γ t
AppTm {s = s} {t} e1 e2 = constr (App s t) (e1 ∷ e2 ∷ [])

ZeroTm : ∀{Γ} → Tm Γ Nat
ZeroTm = constr Zero []

SucTm : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
SucTm e = constr Suc (e ∷ [])

NatRecTm : ∀{Γ t} → Tm Γ t → Tm Γ (Arrow t t) → Tm Γ Nat → Tm Γ t
NatRecTm {t = t} a f n = constr (NatRec t) (a ∷ f ∷ n ∷ [])

FixTm : ∀{Γ t} → Tm (t ∷ Γ) t → Tm Γ t
FixTm {t = t} e = constr (Fix t) (e ∷ [])

-- Values of the language
data Value : ∀{t} → Tm [] t → Set where
  valLam : ∀{s t} → (e : Tm (s ∷ []) t) → Value (LamTm e)
  valZero : Value ZeroTm
  valSuc : (n : Tm [] Nat) → Value n → Value (SucTm n)

isValue : ∀{t} (e : Tm [] t) → Dec (Value e)
isValue (constr (Lam s t) (e ∷ [])) = yes (valLam e)
isValue (constr (App s t) (e1 ∷ e2 ∷ [])) = no λ ()
isValue (constr Zero []) = yes valZero
isValue (constr Suc (n ∷ [])) with isValue n
... | yes n-Value = yes (valSuc n n-Value)
... | no ¬n-Value = no λ{ (valSuc .n n-Value) → ¬n-Value n-Value }
isValue (constr (NatRec t) (a ∷ f ∷ n ∷ [])) = no λ ()
isValue (constr (Fix t) (e ∷ [])) = no λ ()

-- Operational semantics
data _⇒_ : ∀{t} → Tm [] t → Tm [] t → Set where
  stepFun : ∀{s t} (e1 e1' : Tm [] (Arrow s t)) (e2 : Tm [] s) →
            e1 ⇒ e1' → AppTm e1 e2 ⇒ AppTm e1' e2
  stepArg : ∀{s t} (e1 : Tm [] (Arrow s t)) (e2 e2' : Tm [] s) →
            Value e1 → e2 ⇒ e2' → AppTm e1 e2 ⇒ AppTm e1 e2'
  stepβ : ∀{s t} (e1 : Tm (s ∷ []) t) (e2 : Tm [] s) →
          AppTm (LamTm e1) e2 ⇒ sub (IdSub ▸ e2) e1
  stepSuc : ∀ n n' → n ⇒ n' → SucTm n ⇒ SucTm n'
  stepRec : ∀{t} (a : Tm [] t) f n n' → n ⇒ n' → NatRecTm a f n ⇒ NatRecTm a f n'
  stepRecZero : ∀{t} (a : Tm [] t) f → NatRecTm a f ZeroTm ⇒ a
  stepRecSuc : ∀{t} (a : Tm [] t) f n → NatRecTm a f (SucTm n) ⇒ AppTm f (NatRecTm a f n)
  stepFix : ∀{t} (e : Tm (t ∷ []) t) → FixTm e ⇒ sub (IdSub ▸ FixTm e) e

-- Values cannot step
valNoStep : ∀{t} {e e' : Tm [] t} → Value e → ¬ (e ⇒ e')
valNoStep (valLam e) = λ ()
valNoStep valZero = λ ()
valNoStep (valSuc n n-Val) (stepSuc .n n' n⇒n') = valNoStep n-Val n⇒n'

-- Inclusion from natural numbers to terms
ιℕ : ∀{Γ} → ℕ → Tm Γ Nat
ιℕ zero = ZeroTm
ιℕ (suc n) = SucTm (ιℕ n)

-- Each ground natural number value corresponds to an actual natural
natInvert : (n : Tm [] Nat) →
            Value n →
            Σ[ x ∈ ℕ ] (n ≡ ιℕ x)
natInvert .ZeroTm valZero = zero , refl
natInvert .(SucTm n) (valSuc n n-Val) with natInvert n n-Val
... | (x , refl) = suc x , refl

progress : ∀{t} (e : Tm [] t) →
           (Value e) ⊎ Σ[ e' ∈ Tm [] t ] (e ⇒ e')
progress (constr (Lam s t) (e ∷ [])) = inl (valLam e)
progress (constr (App s t) (e1 ∷ e2 ∷ [])) with progress e1
... | inr (e1' , e1⇒e1') = inr (AppTm e1' e2 , stepFun e1 e1' e2 e1⇒e1')
... | inl (valLam e1) = inr (sub (IdSub ▸ e2) e1 , stepβ e1 e2)
progress (constr Zero []) = inl valZero
progress (constr Suc (n ∷ [])) with progress n
... | inl n-Val = inl (valSuc n n-Val)
... | inr (n' , n⇒n') = inr (SucTm n' , stepSuc n n' n⇒n')
progress (constr (NatRec t) (a ∷ f ∷ n ∷ [])) with progress n
... | inr (n' , n⇒n') = inr (NatRecTm a f n' , stepRec a f n n' n⇒n')
... | inl valZero = inr (a , stepRecZero a f)
... | inl (valSuc n n-Val) = inr (AppTm f (NatRecTm a f n) , stepRecSuc a f n)
progress (constr (Fix t) (e ∷ [])) = inr (sub (IdSub ▸ FixTm e) e , stepFix e)

infixr 5 _∷_
data _⇒*[_]_ : ∀{t} → Tm [] t → ℕ → Tm [] t → Set where
  [] : ∀{t} {e : Tm [] t} → e ⇒*[ zero ] e
  _∷_ : ∀{t n} {e1 e2 e3 : Tm [] t} → e1 ⇒ e2 → e2 ⇒*[ n ] e3 → e1 ⇒*[ suc n ] e3

_⇓_ : ∀{t} (e e' : Tm [] t) → Set
e ⇓ e' = Σ[ n ∈ ℕ ] (e ⇒*[ n ] e') × (Value e')

runFor : ∀{t} (gas : ℕ) (e : Tm [] t) →
         Σ[ e' ∈ Tm [] t ] (e ⇒*[ gas ] e' ⊎ e ⇓ e')
runFor zero e with isValue e
... | yes e-Value = e , inr (zero , [] , e-Value)
... | no ¬e-Value = e , inl []
runFor (suc gas) e with progress e
... | inl e-Val = e , inr (zero , [] , e-Val)
... | inr (e' , e⇒e') with runFor gas e'
... | e'' , inl e'⇒*e'' = e'' , inl (e⇒e' ∷ e'⇒*e'') 
... | e'' , inr (n , e'⇒e'' , e''-Value) = e'' , inr (suc n , e⇒e' ∷ e'⇒e'' , e''-Value)
