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
open import SecondOrderLanguage
open import SecondOrderLanguageUntyped
open import SecondOrderSolver

module SecondOrderSolverMacro where

_==_ = primQNameEquality
{-# INLINE _==_ #-}

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

buildExpr : Term → Term → Term
buildExpr ⅀ (def (quote ren) (⅀' ∷ Γ1 ∷ Γ2 ∷ t ∷ arg _ ξ ∷ arg _ e ∷ [])) =
  con (quote Expr.renETm) (buildExpr ⅀ ξ ⟨∷⟩ buildExpr ⅀ e ⟨∷⟩ [])
buildExpr ⅀ (def (quote IdRen) (⅀' ∷ Γ ∷ [])) =
  con (quote Expr.ERenId) []
buildExpr ⅀ (con (quote Ren.ε) (⅀' ∷ [])) =
  con (quote Expr.ERenε) []
buildExpr ⅀ (def (quote sub) (⅀' ∷ Γ1 ∷ Γ2 ∷ t ∷ arg _ σ ∷ arg _ e ∷ [])) =
  con (quote Expr.subETm) (buildExpr ⅀ σ ⟨∷⟩ buildExpr ⅀ e ⟨∷⟩ [])
buildExpr ⅀ (def (quote IdSub) (⅀' ∷ Γ ∷ [])) =
  con (quote Expr.ESubId) []
buildExpr ⅀ (def (quote ι) (⅀' ∷ Γ1 ∷ Γ2 ∷ arg _ ξ ∷ [])) =
  con (quote Expr.ιE) (buildExpr ⅀ ξ ⟨∷⟩ [])   
buildExpr ⅀ t = con (quote ιExpr) (t ⟨∷⟩ [])

buildSoln : Term → Term → Term → Term
buildSoln ⅀ lhs rhs =
  def (quote trans)
    (def (quote sym) ((def (quote simpl≡) (⅀ ⟨∷⟩ buildExpr ⅀ lhs ⟨∷⟩ [])) ⟨∷⟩ [])
    ⟨∷⟩ (def (quote simpl≡) (⅀ ⟨∷⟩ buildExpr ⅀ rhs ⟨∷⟩ []))
    ⟨∷⟩ []
    )

solve-macro : Term → Term → TC ⊤
solve-macro ⅀ hole = do
  _ ← checkType ⅀ (def (quote SecondOrderSignature) [])
  hole′ ← inferType hole >>= normalise
  just (lhs , rhs) ← returnTC (getArgs hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = buildSoln ⅀ lhs rhs
  unify hole soln

macro
  solve : Term → Term → TC ⊤
  solve ⅀ = solve-macro ⅀

⅀' : SecondOrderSignature
Knd ⅀' = ⊤
TyShape ⅀' = ⊥
TyPos ⅀' ()

module _ where
  test1 : (e : Tm ⅀' [] tt) → e ≡ e
  test1 e = solve ⅀'

  test2 : (e : Tm ⅀' [] tt) → ren ⅀' (IdRen ⅀') e ≡ e
  test2 e = solve ⅀'

  test3 : ∀{Γ t} (e : Tm ⅀' Γ t) → ren ⅀' (IdRen ⅀') e ≡ e
  test3 e = solve ⅀'

  test4 : ∀{Γ t} (e : Tm ⅀' Γ t) → sub ⅀' (IdSub ⅀') e ≡ e
  test4 e = solve ⅀'
