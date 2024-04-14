{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.List
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures

-- The algebra defined by a second-order binding signature
module SecondOrderLanguage (⅀ : SecondOrderSignature) where

open SecondOrderSignature ⅀

-- Contexts
Ctx : Set
Ctx = List (⅀ .Knd)

-- In-context variables
data Var : Ctx → (⅀ .Knd) → Set where
  V0 : ∀{Γ t} → Var (t ∷ Γ) t
  VS : ∀{Γ s t} → Var Γ t → Var (s ∷ Γ) t

data Tm (Γ : Ctx) : (⅀ .Knd) → Set
data TmVec (Γ : Ctx) : List (Ctx × (⅀ .Knd)) → Set

-- Terms
data Tm Γ where
  var : ∀{t} → Var Γ t → Tm Γ t
  constr : (s : ⅀ .TyShape) (es : TmVec Γ (⅀ .TyPos s .fst)) → Tm Γ (⅀ .TyPos s .snd)

-- Lists of terms
infixr 5 _∷_
data TmVec Γ where
  [] : TmVec Γ []
  _∷_ : ∀{Δ t Σ} →
        (e : Tm (Δ ++ Γ) t) →
        (es : TmVec Γ Σ) →
        TmVec Γ ((Δ , t) ∷ Σ)

----------------------
-- BASIC PROPERTIES --
----------------------

-- Injectivity of constructors
VS-inj : ∀{Γ s t x y} → VS {Γ} {s} {t} x ≡ VS y → x ≡ y
VS-inj refl = refl

var-inj : ∀{Γ t x y} → var {Γ} {t} x ≡ var y → x ≡ y 
var-inj refl = refl

constr-inj : ∀{Γ s es1 es2} → constr {Γ} s es1 ≡ constr s es2 → es1 ≡ es2
constr-inj refl = refl

cons-inj : ∀{Γ Δ t Σ e1 e2 es1 es2} →
           _≡_ {A = TmVec Γ ((Δ , t) ∷ Σ)} (e1 ∷ es1) (e2 ∷ es2) →  
           e1 ≡ e2 × es1 ≡ es2
cons-inj refl = refl , refl

-- How substitution acts on variables
substV0 : ∀{Γ1 Γ2 t} (p : t ∷ Γ1 ≡ t ∷ Γ2) →
           V0 ≡ subst (flip Var t) p V0
substV0 refl = refl

substVS : ∀{Γ1 Γ2 t t'} (p : Γ1 ≡ Γ2) (x : Var Γ1 t) →
          VS (subst (flip Var t) p x) ≡
          subst (flip Var t) (cong (t' ∷_) p) (VS x)
substVS refl x = refl

-- How substitution acts on terms
substVar : ∀{Γ1 Γ2 t} (p : Γ1 ≡ Γ2) (x : Var Γ1 t) →
          var (subst (flip Var t) p x) ≡
           subst (flip Tm t) p (var x)
substVar refl x = refl

substConstr : ∀{Γ1 Γ2 s} (p : Γ1 ≡ Γ2) (ts : TmVec Γ1 (⅀ .TyPos s .fst)) →
              constr s (subst (flip TmVec (⅀ .TyPos s .fst)) p ts) ≡
              subst (flip Tm (⅀ .TyPos s .snd)) p (constr s ts)
substConstr refl ts = refl

-- How substitution acts on term vectors
substNil : ∀{Γ1 Γ2} (p : Γ1 ≡ Γ2) →
           [] ≡ subst (flip TmVec []) p []
substNil refl = refl

substCons : ∀{Σ Δ Γ1 Γ2 t} (p : Γ1 ≡ Γ2) (e : Tm (Δ ++ Γ1) t) (es : TmVec Γ1 Σ) →
              subst (flip Tm t) (cong (Δ ++_) p) e ∷ subst (flip TmVec Σ) p es ≡
              subst (flip TmVec ((Δ , t) ∷ Σ)) p (e ∷ es)
substCons refl e es = refl

--------------
-- RENAMING --
--------------

data Ren : Ctx → Ctx → Set where
  ε : ∀{Γ} → Ren [] Γ
  Keep : ∀{Γ1 Γ2 t} → Ren Γ1 Γ2 → Ren (t ∷ Γ1) (t ∷ Γ2)
  Drop : ∀{Γ1 Γ2 t} → Ren Γ1 Γ2 → Ren Γ1 (t ∷ Γ2)

IdRen : ∀{Γ} → Ren Γ Γ
IdRen {[]} = ε
IdRen {t ∷ Γ} = Keep IdRen

Keep* : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → ∀ Δ → Ren (Δ ++ Γ1) (Δ ++ Γ2)
Keep* ξ [] = ξ
Keep* ξ (t ∷ Δ) = Keep (Keep* ξ Δ)

KeepId* : ∀{Γ} Δ → Keep* (IdRen {Γ}) Δ ≡ IdRen
KeepId* [] = refl
KeepId* (t ∷ Δ) = cong Keep (KeepId* Δ)

Drop* : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → ∀ Δ → Ren Γ1 (Δ ++ Γ2)
Drop* ξ [] = ξ
Drop* ξ (t ∷ Δ) = Drop (Drop* ξ Δ)

infixr 9 _•_ 
_•_ : ∀{Γ1 Γ2 Γ3} → Ren Γ2 Γ3 → Ren Γ1 Γ2 → Ren Γ1 Γ3
ε • ε = ε
Keep ξ1 • ε = ε
Keep ξ1 • Keep ξ2 = Keep (ξ1 • ξ2)
Keep ξ1 • Drop ξ2 = Drop (ξ1 • ξ2)
Drop ξ1 • ξ2 = Drop (ξ1 • ξ2)

Id• : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → IdRen • ξ ≡ ξ
Id• {Γ2 = []} ε = refl
Id• {Γ2 = x ∷ Γ2} ε = refl
Id• (Keep ξ) = cong Keep (Id• ξ)
Id• (Drop ξ) = cong Drop (Id• ξ)

•Id : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ξ • IdRen ≡ ξ
•Id ε = refl
•Id (Keep ξ) = cong Keep (•Id ξ)
•Id (Drop ξ) = cong Drop (•Id ξ)

Keep*•Keep* : ∀{Γ1 Γ2 Γ3} {ξ1 : Ren Γ2 Γ3} {ξ2 : Ren Γ1 Γ2}
          (Δ : Ctx) →
          Keep* (ξ1 • ξ2) Δ ≡ Keep* ξ1 Δ • Keep* ξ2 Δ
Keep*•Keep* [] = refl
Keep*•Keep* (t ∷ Δ) = cong Keep (Keep*•Keep* Δ)

Keep*•Drop* : ∀{Γ1 Γ2 Γ3} {ξ1 : Ren Γ2 Γ3} {ξ2 : Ren Γ1 Γ2}
              (Δ : Ctx) →
              Drop* (ξ1 • ξ2) Δ ≡ Keep* ξ1 Δ • Drop* ξ2 Δ
Keep*•Drop* [] = refl
Keep*•Drop* (t ∷ Δ) = cong Drop (Keep*•Drop* Δ)

Drop*• : ∀{Γ1 Γ2 Γ3} {ξ1 : Ren Γ2 Γ3} {ξ2 : Ren Γ1 Γ2}
          (Δ : Ctx) →
          Drop* (ξ1 • ξ2) Δ ≡ Drop* ξ1 Δ • ξ2
Drop*• [] = refl
Drop*• (t ∷ Δ) = cong Drop (Drop*• Δ)

-- Variable renaming
renVar : ∀{Γ1 Γ2 t} → Ren Γ1 Γ2 → Var Γ1 t → Var Γ2 t
renVar (Keep ξ) V0 = V0
renVar (Keep ξ) (VS x) = VS (renVar ξ x)
renVar (Drop ξ) x = VS (renVar ξ x)

-- Term renaming
ren : ∀{Γ1 Γ2 t} → Ren Γ1 Γ2 → Tm Γ1 t → Tm Γ2 t
renVec : ∀{Γ1 Γ2 Σ} → Ren Γ1 Γ2 → TmVec Γ1 Σ → TmVec Γ2 Σ

ren ξ (var x) = var (renVar ξ x)
ren ξ (constr s ts) = constr s (renVec ξ ts)

renVec ξ [] = []
renVec {Σ = (Δ , t) ∷ Σ} ξ (e ∷ es) = ren (Keep* ξ Δ) e ∷ renVec ξ es

renVarId : ∀{Γ t} (x : Var Γ t) → renVar IdRen x ≡ x
renVarId V0 = refl
renVarId (VS x) = cong VS (renVarId x)

renId : ∀{Γ t} (t : Tm Γ t) → ren IdRen t ≡ t
renVecId : ∀{Γ Σ} (ts : TmVec Γ Σ) → renVec IdRen ts ≡ ts

renId (var x) = cong var (renVarId x)
renId (constr s ts) = cong (constr s) (renVecId ts)

renVecId [] = refl
renVecId {Σ = (Δ , t) ∷ Σ} (e ∷ es) =
  cong₂ _∷_ (cong (flip ren e) (KeepId* Δ) ∙ renId e) (renVecId es)

renVar• : ∀{Γ1 Γ2 Γ3 t} (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
          (x : Var Γ1 t) → renVar (ξ1 • ξ2) x ≡ renVar ξ1 (renVar ξ2 x)
renVar• ε ε ()
renVar• (Keep ξ1) (Keep ξ2) V0 = refl
renVar• (Keep ξ1) (Keep ξ2) (VS x) = cong VS (renVar• ξ1 ξ2 x)
renVar• (Keep ξ1) (Drop ξ2) x = cong VS (renVar• ξ1 ξ2 x)
renVar• (Drop ξ1) ξ2 x = cong VS (renVar• ξ1 ξ2 x)

ren• : ∀{Γ1 Γ2 Γ3 t} (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
      (e : Tm Γ1 t) → ren (ξ1 • ξ2) e ≡ ren ξ1 (ren ξ2 e)
renVec• : ∀{Γ1 Γ2 Γ3 Σ} (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
          (es : TmVec Γ1 Σ) → renVec (ξ1 • ξ2) es ≡ renVec ξ1 (renVec ξ2 es)

ren• ξ1 ξ2 (var x) = cong var (renVar• ξ1 ξ2 x)
ren• ξ1 ξ2 (constr c es) = cong (constr c) (renVec• ξ1 ξ2 es)

renVec• ξ1 ξ2 [] = refl
renVec• {Σ = (Δ , t) ∷ Σ} ξ1 ξ2 (e ∷ es) =
  cong₂ _∷_
    (ren (Keep* (ξ1 • ξ2) Δ) e
      ≡⟨ cong (flip ren e) (Keep*•Keep* Δ) ⟩
    ren (Keep* ξ1 Δ • Keep* ξ2 Δ) e
      ≡⟨ ren• (Keep* ξ1 Δ) (Keep* ξ2 Δ) e ⟩
    ren (Keep* ξ1 Δ) (ren (Keep* ξ2 Δ) e) ∎)
    (renVec• ξ1 ξ2 es)

------------------
-- SUBSTITUTION --
------------------

data Sub : Ctx → Ctx → Set where
  ε : ∀{Γ} → Sub [] Γ
  _▸_ : ∀{Γ1 Γ2 t} (σ : Sub Γ1 Γ2) (e : Tm Γ2 t) → Sub (t ∷ Γ1) Γ2

infixr 9 _•◦_ 
_•◦_ : ∀{Γ1 Γ2 Γ3} → Ren Γ2 Γ3 → Sub Γ1 Γ2 → Sub Γ1 Γ3
ξ •◦ ε = ε
ξ •◦ (σ ▸ e) = (ξ •◦ σ) ▸ ren ξ e

Id•◦ : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) → IdRen •◦ σ ≡ σ
Id•◦ ε = refl
Id•◦ (σ ▸ e) = cong₂ _▸_ (Id•◦ σ) (renId e)

••◦ : ∀{Γ1 Γ2 Γ3 Γ4} (ξ1 : Ren Γ3 Γ4) (ξ2 : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
    (ξ1 • ξ2) •◦ σ ≡ ξ1 •◦ (ξ2 •◦ σ)
••◦ ξ1 ξ2 ε = refl
••◦ ξ1 ξ2 (σ ▸ e) = cong₂ _▸_ (••◦ ξ1 ξ2 σ) (ren• ξ1 ξ2 e)

DropSub : ∀{Γ1 Γ2 t} → Sub Γ1 Γ2 → Sub Γ1 (t ∷ Γ2)
DropSub σ = Drop IdRen •◦ σ

KeepSub : ∀{Γ1 Γ2 t} → Sub Γ1 Γ2 → Sub (t ∷ Γ1) (t ∷ Γ2)
KeepSub σ = DropSub σ ▸ var V0

KeepSub* : ∀{Γ1 Γ2} → Sub Γ1 Γ2 → ∀ Δ → Sub (Δ ++ Γ1) (Δ ++ Γ2)
KeepSub* σ [] = σ
KeepSub* σ (t ∷ Δ) = KeepSub (KeepSub* σ Δ)

DropSub* : ∀{Γ1 Γ2} → Sub Γ1 Γ2 → ∀ Δ → Sub Γ1 (Δ ++ Γ2)
DropSub* σ [] = σ
DropSub* σ (t ∷ Δ) = DropSub (DropSub* σ Δ)

Drop•◦ : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
        DropSub {t = t} (ξ •◦ σ) ≡ Drop ξ •◦ σ
Drop•◦ ξ σ =
  Drop IdRen •◦ (ξ •◦ σ)
    ≡⟨ sym (••◦ (Drop IdRen) ξ σ) ⟩
  Drop (IdRen • ξ) •◦ σ
    ≡⟨ cong (λ x → Drop x •◦ σ) (Id• ξ) ⟩
  Drop ξ •◦ σ ∎

Drop*•◦ : ∀{Γ1 Γ2 Γ3} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
          ∀ Δ → DropSub* (ξ •◦ σ) Δ ≡ Drop* ξ Δ •◦ σ
Drop*•◦ ξ σ [] = refl
Drop*•◦ ξ σ (t ∷ Δ) =
  DropSub (DropSub* (ξ •◦ σ) Δ)
    ≡⟨ cong DropSub (Drop*•◦ ξ σ Δ) ⟩
  DropSub (Drop* ξ Δ •◦ σ)
    ≡⟨ Drop•◦ (Drop* ξ Δ) σ ⟩
  Drop (Drop* ξ Δ) •◦ σ ∎

Keep•◦Drop : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
            DropSub {t = t} (ξ •◦ σ) ≡ Keep ξ •◦ DropSub σ
Keep•◦Drop ξ ε = refl
Keep•◦Drop ξ (σ ▸ e) =
  cong₂ _▸_
  (Drop IdRen •◦ ξ •◦ σ
    ≡⟨ sym (••◦ (Drop IdRen) ξ σ) ⟩
  Drop (IdRen • ξ) •◦ σ
    ≡⟨ cong (λ x → Drop x •◦ σ) (Id• ξ) ⟩
  Drop ξ •◦ σ
    ≡⟨ cong (λ x → Drop x •◦ σ) (sym (•Id ξ)) ⟩
  Drop (ξ • IdRen) •◦ σ
    ≡⟨ ••◦ (Keep ξ) (Drop IdRen) σ ⟩
  Keep ξ •◦ Drop IdRen •◦ σ ∎)
  (ren (Drop IdRen) (ren ξ e)
    ≡⟨ sym (ren• (Drop IdRen) ξ e) ⟩
  ren (Drop (IdRen • ξ)) e
    ≡⟨ cong (λ x → ren (Drop x) e) (Id• ξ) ⟩
  ren (Drop ξ) e
    ≡⟨ cong (λ x → ren (Drop x) e) (sym (•Id ξ)) ⟩
  ren (Drop (ξ • IdRen)) e
    ≡⟨ ren• (Keep ξ) (Drop IdRen) e ⟩ 
  ren (Keep ξ) (ren (Drop IdRen) e) ∎)

Keep•◦ : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
        KeepSub {t = t} (ξ •◦ σ) ≡ Keep ξ •◦ KeepSub σ
Keep•◦ ξ σ = cong (_▸ var V0) (Keep•◦Drop ξ σ)

Keep•◦* : ∀{Γ1 Γ2 Γ3} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
        ∀ Δ → KeepSub* (ξ •◦ σ) Δ ≡ Keep* ξ Δ •◦ KeepSub* σ Δ
Keep•◦* ξ σ [] = refl
Keep•◦* ξ σ (t ∷ Δ) =
  KeepSub (KeepSub* (ξ •◦ σ) Δ)
    ≡⟨ cong KeepSub (Keep•◦* ξ σ Δ) ⟩
  KeepSub (Keep* ξ Δ •◦ KeepSub* σ Δ)
    ≡⟨ Keep•◦ (Keep* ξ Δ) (KeepSub* σ Δ) ⟩
  Keep (Keep* ξ Δ) •◦ KeepSub (KeepSub* σ Δ) ∎

ι : ∀{Γ1 Γ2} → Ren Γ1 Γ2 → Sub Γ1 Γ2
ι ε = ε
ι (Keep ξ) = KeepSub (ι ξ)
ι (Drop ξ) = DropSub (ι ξ)

Drop*ι : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ → DropSub* (ι ξ) Δ ≡ ι (Drop* ξ Δ)
Drop*ι ξ [] = refl
Drop*ι ξ (t ∷ Δ) = cong DropSub (Drop*ι ξ Δ)

Keep*ι : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ∀ Δ → KeepSub* (ι ξ) Δ ≡ ι (Keep* ξ Δ)
Keep*ι ξ [] = refl
Keep*ι ξ (t ∷ Δ) = cong KeepSub (Keep*ι ξ Δ)


•◦ι : ∀{Γ1 Γ2 Γ3} (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
    ξ1 •◦ ι ξ2 ≡ ι (ξ1 • ξ2)
•◦ι ε ε = refl
•◦ι (Keep ξ1) ε = refl
•◦ι (Keep ξ1) (Keep ξ2) = cong (_▸ var V0) (
  Keep ξ1 •◦ (Drop IdRen •◦ ι ξ2)
    ≡⟨ sym (••◦ (Keep ξ1) (Drop IdRen) (ι ξ2)) ⟩
  Drop (ξ1 • IdRen) •◦ ι ξ2
    ≡⟨ cong (λ x → Drop x •◦ ι ξ2) (•Id ξ1) ⟩
  Drop ξ1 •◦ ι ξ2
    ≡⟨ cong (λ x → Drop x •◦ ι ξ2) (sym (Id• ξ1)) ⟩
  Drop (IdRen • ξ1) •◦ ι ξ2
    ≡⟨ ••◦ (Drop IdRen) ξ1 (ι ξ2) ⟩
  Drop IdRen •◦ (ξ1 •◦ ι ξ2)
    ≡⟨ cong (Drop IdRen •◦_) (•◦ι ξ1 ξ2) ⟩
  Drop IdRen •◦ ι (ξ1 • ξ2) ∎)
•◦ι (Keep ξ1) (Drop ξ2) =
  Keep ξ1 •◦ (Drop IdRen •◦ ι ξ2)
    ≡⟨ sym (••◦ (Keep ξ1) (Drop IdRen) (ι ξ2)) ⟩
  Drop (ξ1 • IdRen) •◦ ι ξ2
    ≡⟨ cong (λ x → Drop x •◦ ι ξ2) (•Id ξ1) ⟩
  Drop ξ1 •◦ ι ξ2
    ≡⟨ cong (λ x → Drop x •◦ ι ξ2) (sym (Id• ξ1)) ⟩
  Drop (IdRen • ξ1) •◦ ι ξ2
    ≡⟨ ••◦ (Drop IdRen) ξ1 (ι ξ2) ⟩
  Drop IdRen •◦ (ξ1 •◦ ι ξ2)
    ≡⟨ cong (Drop IdRen •◦_) (•◦ι ξ1 ξ2) ⟩
  Drop IdRen •◦ ι (ξ1 • ξ2) ∎
•◦ι (Drop ξ1) ξ2 =
  Drop ξ1 •◦ ι ξ2
    ≡⟨ cong (λ x → Drop x •◦ ι ξ2) (sym (Id• ξ1)) ⟩
  Drop (IdRen • ξ1) •◦ ι ξ2
    ≡⟨ ••◦ (Drop IdRen) ξ1 (ι ξ2) ⟩
  Drop IdRen •◦ (ξ1 •◦ ι ξ2)
    ≡⟨ cong (Drop IdRen •◦_) (•◦ι ξ1 ξ2) ⟩
  Drop IdRen •◦ ι (ξ1 • ξ2) ∎

IdSub : ∀{Γ} → Sub Γ Γ
IdSub = ι IdRen

•◦Id : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → ξ •◦ IdSub ≡ ι ξ
•◦Id ξ =
  ξ •◦ ι IdRen   ≡⟨ •◦ι ξ IdRen ⟩
  ι (ξ • IdRen) ≡⟨ cong ι (•Id ξ) ⟩
  ι ξ           ∎

Keepι* : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) (Δ : Ctx) →
          KeepSub* (ι ξ) Δ ≡ ι (Keep* ξ Δ)
Keepι* ξ [] = refl
Keepι* ξ (t ∷ Δ) = cong KeepSub (Keepι* ξ Δ)

-- Variable substitution
subVar : ∀{Γ1 Γ2 t} → Sub Γ1 Γ2 → Var Γ1 t → Tm Γ2 t
subVar (σ ▸ e) V0 = e
subVar (σ ▸ e) (VS x) = subVar σ x

-- Term substitution
sub : ∀{Γ1 Γ2 t} → Sub Γ1 Γ2 → Tm Γ1 t → Tm Γ2 t
subVec : ∀{Γ1 Γ2 Σ} → Sub Γ1 Γ2 → TmVec Γ1 Σ → TmVec Γ2 Σ

sub σ (var x) = subVar σ x
sub σ (constr c es) = constr c (subVec σ es)

subVec σ [] = []
subVec {Σ = (Δ , t) ∷ Σ} σ (e ∷ es) = sub (KeepSub* σ Δ) e ∷ subVec σ es

subVar•◦ : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
          (x : Var Γ1 t) → subVar (ξ •◦ σ) x ≡ ren ξ (subVar σ x)
subVar•◦ ξ (σ ▸ e) V0 = refl
subVar•◦ ξ (σ ▸ e) (VS x) = subVar•◦ ξ σ x

sub•◦ : ∀{Γ1 Γ2 Γ3 t} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
        (e : Tm Γ1 t) → sub (ξ •◦ σ) e ≡ ren ξ (sub σ e)
subVec•◦ : ∀{Γ1 Γ2 Γ3 Σ} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
        (es : TmVec Γ1 Σ) → subVec (ξ •◦ σ) es ≡ renVec ξ (subVec σ es)

sub•◦ ξ σ (var x) = subVar•◦ ξ σ x
sub•◦ ξ σ (constr c es) = cong (constr c) (subVec•◦ ξ σ es)

subVec•◦ ξ σ [] = refl
subVec•◦ {Σ = (Δ , t) ∷ Σ} ξ σ (e ∷ es) =
  cong₂ _∷_
    (sub (KeepSub* (ξ •◦ σ) Δ) e
      ≡⟨ cong (flip sub e) (Keep•◦* ξ σ Δ) ⟩
    sub (Keep* ξ Δ •◦ KeepSub* σ Δ) e
      ≡⟨ sub•◦ (Keep* ξ Δ) (KeepSub* σ Δ) e ⟩
    ren (Keep* ξ Δ) (sub (KeepSub* σ Δ) e) ∎)
    (subVec•◦ ξ σ es)

subVarι : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (x : Var Γ1 t) → subVar (ι ξ) x ≡ var (renVar ξ x)
subVarι (Keep ξ) V0 = refl
subVarι (Keep ξ) (VS x) = subVarι (Drop ξ) x
subVarι (Drop ξ) x =
  subVar (Drop IdRen •◦ ι ξ) x
    ≡⟨ subVar•◦ (Drop IdRen) (ι ξ) x ⟩
  ren (Drop IdRen) (subVar (ι ξ) x)
    ≡⟨ cong (ren (Drop IdRen)) (subVarι ξ x) ⟩
  var (VS (renVar IdRen (renVar ξ x)))
    ≡⟨ cong (var ∘ VS) (sym (renVar• IdRen ξ x)) ⟩
  var (VS (renVar (IdRen • ξ) x))
    ≡⟨ cong (var ∘ VS) (cong (flip renVar x) (Id• ξ)) ⟩
  var (VS (renVar ξ x)) ∎

subι : ∀{Γ1 Γ2 t} (ξ : Ren Γ1 Γ2) (e : Tm Γ1 t) → sub (ι ξ) e ≡ ren ξ e
subVecι : ∀{Γ1 Γ2 Σ} (ξ : Ren Γ1 Γ2) (es : TmVec Γ1 Σ) → subVec (ι ξ) es ≡ renVec ξ es

subι ξ (var x) = subVarι ξ x
subι ξ (constr c es) = cong (constr c) (subVecι ξ es)

subVecι ξ [] = refl
subVecι {Σ = (Δ , t) ∷ Σ} ξ (e ∷ es) =
  cong₂ _∷_
    (sub (KeepSub* (ι ξ) Δ) e
      ≡⟨ cong (flip sub e) (Keepι* ξ Δ) ⟩
    sub (ι (Keep* ξ Δ)) e
      ≡⟨ subι (Keep* ξ Δ) e ⟩
    ren (Keep* ξ Δ) e ∎)
    (subVecι ξ es)

subVarId : ∀{Γ t} (x : Var Γ t) → subVar IdSub x ≡ var x
subVarId x = subVarι IdRen x ∙ cong var (renVarId x)

subId : ∀{Γ t} (e : Tm Γ t) → sub IdSub e ≡ e
subId e = subι IdRen e ∙ renId e

subVecId : ∀{Γ Σ} (es : TmVec Γ Σ) → subVec IdSub es ≡ es
subVecId es = subVecι IdRen es ∙ renVecId es

infixr 9 _◦•_ 
_◦•_ : ∀{Γ1 Γ2 Γ3} → Sub Γ2 Γ3 → Ren Γ1 Γ2 → Sub Γ1 Γ3
σ ◦• ε = ε
(σ ▸ e) ◦• Keep ξ = (σ ◦• ξ) ▸ e
(σ ▸ e) ◦• Drop ξ = σ ◦• ξ

◦•• : ∀{Γ1 Γ2 Γ3 Γ4} (σ : Sub Γ3 Γ4) (ξ1 : Ren Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
      σ ◦• (ξ1 • ξ2) ≡ (σ ◦• ξ1) ◦• ξ2
◦•• σ ε ε = refl
◦•• (σ ▸ e) (Keep ξ1) ε = refl
◦•• (σ ▸ e) (Keep ξ1) (Keep ξ2) = cong (_▸ e) (◦•• σ ξ1 ξ2)
◦•• (σ ▸ e) (Keep ξ1) (Drop ξ2) = ◦•• σ ξ1 ξ2
◦•• (σ ▸ e) (Drop ξ1) ξ2 = ◦•• σ ξ1 ξ2

•◦◦• : ∀{Γ1 Γ2 Γ3 Γ4} (ξ1 : Ren Γ3 Γ4) (σ : Sub Γ2 Γ3) (ξ2 : Ren Γ1 Γ2) →
      ξ1 •◦ (σ ◦• ξ2) ≡ (ξ1 •◦ σ) ◦• ξ2
•◦◦• ξ1 σ ε = refl
•◦◦• ξ1 (σ ▸ e) (Keep ξ2) = cong (_▸ ren ξ1 e) (•◦◦• ξ1 σ ξ2)
•◦◦• ξ1 (σ ▸ e) (Drop ξ2) = •◦◦• ξ1 σ ξ2

Drop◦• : ∀{Γ1 Γ2 Γ3 t} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
        DropSub {t = t} (σ ◦• ξ) ≡ DropSub σ ◦• ξ
Drop◦• σ ε = refl
Drop◦• (σ ▸ e) (Keep ξ) =
  cong (_▸ ren (Drop IdRen) e) (•◦◦• (Drop IdRen) σ ξ)
Drop◦• (σ ▸ e) (Drop ξ) = •◦◦• (Drop IdRen) σ ξ

Keep◦• : ∀{Γ1 Γ2 Γ3 t} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
        KeepSub {t = t} (σ ◦• ξ) ≡ KeepSub σ ◦• Keep ξ
Keep◦• σ ε = refl
Keep◦• (σ ▸ e) (Keep ξ) =
  cong (_▸ var V0)
  (cong (_▸ ren (Drop IdRen) e)
  (Drop◦• σ ξ))
Keep◦• (σ ▸ e) (Drop ξ) = cong (_▸ var V0) (Drop◦• σ ξ)

Keep*◦• : ∀{Γ1 Γ2 Γ3} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
          ∀ Δ → KeepSub* (σ ◦• ξ) Δ ≡ KeepSub* σ Δ ◦• Keep* ξ Δ
Keep*◦• σ ξ [] = refl
Keep*◦• σ ξ (t ∷ Δ) =
  KeepSub (KeepSub* (σ ◦• ξ) Δ)
    ≡⟨ cong KeepSub (Keep*◦• σ ξ Δ) ⟩
  KeepSub (KeepSub* σ Δ ◦• Keep* ξ Δ)
    ≡⟨ Keep◦• (KeepSub* σ Δ) (Keep* ξ Δ) ⟩
  KeepSub (KeepSub* σ Δ) ◦• Keep (Keep* ξ Δ) ∎

Id◦• : ∀{Γ1 Γ2} (ξ : Ren Γ1 Γ2) → IdSub ◦• ξ ≡ ι ξ
Id◦• ε = refl
Id◦• (Keep ξ) = cong (_▸ var V0)
  (DropSub IdSub ◦• ξ
    ≡⟨ sym (Drop◦• IdSub ξ) ⟩
  DropSub (IdSub ◦• ξ)
    ≡⟨ cong DropSub (Id◦• ξ) ⟩
  DropSub (ι ξ) ∎)
Id◦• (Drop ξ) =
  DropSub IdSub ◦• ξ
    ≡⟨ sym (Drop◦• IdSub ξ) ⟩
  DropSub (IdSub ◦• ξ)
    ≡⟨ cong DropSub (Id◦• ξ) ⟩
  DropSub (ι ξ) ∎

◦•Id : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) → σ ◦• IdRen ≡ σ
◦•Id ε = refl
◦•Id (σ ▸ e) = cong (_▸ e) (◦•Id σ)

subVar◦• : ∀{Γ1 Γ2 Γ3 t} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
          (x : Var Γ1 t) → subVar (σ ◦• ξ) x ≡ subVar σ (renVar ξ x)
subVar◦• (σ ▸ e) (Keep ξ) V0 = refl
subVar◦• (σ ▸ e) (Keep ξ) (VS x) = subVar◦• σ ξ x
subVar◦• (σ ▸ e) (Drop ξ) x = subVar◦• σ ξ x

sub◦• : ∀{Γ1 Γ2 Γ3 t} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
        (e : Tm Γ1 t) → sub (σ ◦• ξ) e ≡ sub σ (ren ξ e)
subVec◦• : ∀{Γ1 Γ2 Γ3 Σ} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
          (es : TmVec Γ1 Σ) → subVec (σ ◦• ξ) es ≡ subVec σ (renVec ξ es)

sub◦• σ ξ (var x) = subVar◦• σ ξ x
sub◦• σ ξ (constr c es) = cong (constr c) (subVec◦• σ ξ es)

subVec◦• ξ σ [] = refl
subVec◦• {Σ = (Δ , t) ∷ Σ} ξ σ (e ∷ es) =
  cong₂ _∷_
    (sub (KeepSub* (ξ ◦• σ) Δ) e
      ≡⟨ cong (flip sub e) (Keep*◦• ξ σ Δ) ⟩
    sub (KeepSub* ξ Δ ◦• Keep* σ Δ) e
      ≡⟨ sub◦• (KeepSub* ξ Δ) (Keep* σ Δ) e ⟩
    sub (KeepSub* ξ Δ) (ren (Keep* σ Δ) e) ∎)
    (subVec◦• ξ σ es)

infixr 9 _◦_ 
_◦_ : ∀{Γ1 Γ2 Γ3} → Sub Γ2 Γ3 → Sub Γ1 Γ2 → Sub Γ1 Γ3
σ1 ◦ ε = ε
σ1 ◦ (σ2 ▸ e) = (σ1 ◦ σ2) ▸ sub σ1 e

•◦◦ : ∀{Γ1 Γ2 Γ3 Γ4} (ξ : Ren Γ3 Γ4) (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
      ξ •◦ (σ1 ◦ σ2) ≡ (ξ •◦ σ1) ◦ σ2
•◦◦ ξ σ1 ε = refl
•◦◦ ξ σ1 (σ2 ▸ e) = cong₂ _▸_ (•◦◦ ξ σ1 σ2) (sym (sub•◦ ξ σ1 e))

◦•◦ : ∀{Γ1 Γ2 Γ3 Γ4} (σ1 : Sub Γ3 Γ4) (ξ : Ren Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
      σ1 ◦ (ξ •◦ σ2) ≡ (σ1 ◦• ξ) ◦ σ2
◦•◦ σ1 ξ ε = refl
◦•◦ σ1 ξ (σ2 ▸ e) = cong₂ _▸_ (◦•◦ σ1 ξ σ2) (sym (sub◦• σ1 ξ e))  

◦ι : ∀{Γ1 Γ2 Γ3} (σ : Sub Γ2 Γ3) (ξ : Ren Γ1 Γ2) →
      σ ◦ ι ξ ≡ σ ◦• ξ
◦ι σ ε = refl
◦ι (σ ▸ e) (Keep ξ) = cong (_▸ e) (
  (σ ▸ e) ◦ Drop IdRen •◦ ι ξ
    ≡⟨ ◦•◦ (σ ▸ e) (Drop IdRen) (ι ξ) ⟩
  (σ ◦• IdRen) ◦ ι ξ
    ≡⟨ cong (_◦ ι ξ) (◦•Id σ) ⟩
  σ ◦ ι ξ
    ≡⟨ ◦ι σ ξ ⟩
  σ ◦• ξ ∎)
◦ι (σ ▸ e) (Drop ξ) =
  (σ ▸ e) ◦ Drop IdRen •◦ ι ξ
    ≡⟨ ◦•◦ (σ ▸ e) (Drop IdRen) (ι ξ) ⟩
  (σ ◦• IdRen) ◦ ι ξ
    ≡⟨ cong (_◦ ι ξ) (◦•Id σ) ⟩
  σ ◦ ι ξ
    ≡⟨ ◦ι σ ξ ⟩
  σ ◦• ξ ∎

ι◦ : ∀{Γ1 Γ2 Γ3} (ξ : Ren Γ2 Γ3) (σ : Sub Γ1 Γ2) →
    ι ξ ◦ σ ≡ ξ •◦ σ
ι◦ ξ ε = refl
ι◦ ξ (σ ▸ e) = cong₂ _▸_ (ι◦ ξ σ) (subι ξ e)

◦Id : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) → σ ◦ IdSub ≡ σ
◦Id σ =
  σ ◦ ι IdRen ≡⟨ ◦ι σ IdRen ⟩
  σ ◦• IdRen  ≡⟨ ◦•Id σ ⟩
  σ           ∎

Id◦ : ∀{Γ1 Γ2} (σ : Sub Γ1 Γ2) → IdSub ◦ σ ≡ σ
Id◦ σ =
  ι IdRen ◦ σ ≡⟨ ι◦ IdRen σ ⟩
  IdRen •◦ σ  ≡⟨ Id•◦ σ ⟩
  σ           ∎

Keep◦Drop : ∀{Γ1 Γ2 Γ3 t} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
            DropSub {t = t} (σ1 ◦ σ2) ≡ KeepSub σ1 ◦ DropSub σ2
Keep◦Drop σ1 ε = refl
Keep◦Drop σ1 (σ2 ▸ e) = cong₂ _▸_ (Keep◦Drop σ1 σ2)
  (ren (Drop IdRen) (sub σ1 e)
    ≡⟨ sym (sub•◦ (Drop IdRen) σ1 e) ⟩
  sub (DropSub σ1) e
    ≡⟨ cong (flip sub e) (sym (◦•Id (DropSub σ1))) ⟩
  sub (DropSub σ1 ◦• IdRen) e
    ≡⟨ sub◦• (KeepSub σ1) (Drop IdRen) e ⟩
  sub (KeepSub σ1) (ren (Drop IdRen) e) ∎)

Keep*◦Drop* : ∀{Γ1 Γ2 Γ3} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
              ∀ Δ → DropSub* (σ1 ◦ σ2) Δ ≡ KeepSub* σ1 Δ ◦ DropSub* σ2 Δ
Keep*◦Drop* σ1 σ2 [] = refl
Keep*◦Drop* σ1 σ2 (t ∷ Δ) =
  DropSub (DropSub* (σ1 ◦ σ2) Δ)
    ≡⟨ cong DropSub (Keep*◦Drop* σ1 σ2 Δ) ⟩
  DropSub (KeepSub* σ1 Δ ◦ DropSub* σ2 Δ) 
    ≡⟨ Keep◦Drop (KeepSub* σ1 Δ) (DropSub* σ2 Δ) ⟩
  KeepSub (KeepSub* σ1 Δ) ◦ DropSub (DropSub* σ2 Δ) ∎

Keep◦ : ∀{Γ1 Γ2 Γ3 t} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
        KeepSub {t = t} (σ1 ◦ σ2) ≡ KeepSub σ1 ◦ KeepSub σ2
Keep◦ σ1 ε = refl
Keep◦ σ1 (σ2 ▸ e) = cong (_▸ var V0) (cong₂ _▸_
  (Drop IdRen •◦ σ1 ◦ σ2
    ≡⟨ •◦◦ (Drop IdRen) σ1 σ2 ⟩
  (Drop IdRen •◦ σ1) ◦ σ2
    ≡⟨ sym (•◦◦ (Drop IdRen) σ1 σ2) ⟩
  Drop IdRen •◦ σ1 ◦ σ2
    ≡⟨ Keep◦Drop σ1 σ2 ⟩
  KeepSub σ1 ◦ DropSub σ2 ∎)
  (ren (Drop IdRen) (sub σ1 e)
    ≡⟨ sym (sub•◦ (Drop IdRen) σ1 e) ⟩
  sub (DropSub σ1) e
    ≡⟨ cong (flip sub e) (sym (◦•Id (DropSub σ1))) ⟩
  sub (DropSub σ1 ◦• IdRen) e
    ≡⟨ sub◦• (KeepSub σ1) (Drop IdRen) e ⟩
  sub (KeepSub σ1) (ren (Drop IdRen) e) ∎))

Keep*◦ : ∀{Γ1 Γ2 Γ3} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
        ∀ Δ → KeepSub* (σ1 ◦ σ2) Δ ≡ KeepSub* σ1 Δ ◦ KeepSub* σ2 Δ
Keep*◦ σ1 σ2 [] = refl
Keep*◦ σ1 σ2 (t ∷ Δ) =
  KeepSub (KeepSub* (σ1 ◦ σ2) Δ)
    ≡⟨ cong KeepSub (Keep*◦ σ1 σ2 Δ) ⟩
  KeepSub (KeepSub* σ1 Δ ◦ KeepSub* σ2 Δ)
    ≡⟨ Keep◦ (KeepSub* σ1 Δ) (KeepSub* σ2 Δ) ⟩
  KeepSub (KeepSub* σ1 Δ) ◦ KeepSub (KeepSub* σ2 Δ) ∎

Drop◦ : ∀{Γ1 Γ2 Γ3 t} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
        DropSub {t = t} (σ1 ◦ σ2) ≡ DropSub σ1 ◦ σ2
Drop◦ σ1 ε = refl
Drop◦ σ1 (σ2 ▸ e) =
  cong₂ _▸_
    (Drop◦ σ1 σ2)
    (sym (sub•◦ (Drop IdRen) σ1 e))

Drop*◦ : ∀{Γ1 Γ2 Γ3} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
        ∀ Δ → DropSub* (σ1 ◦ σ2) Δ ≡ DropSub* σ1 Δ ◦ σ2
Drop*◦ σ1 σ2 [] = refl
Drop*◦ σ1 σ2 (t ∷ Δ) = 
  DropSub (DropSub* (σ1 ◦ σ2) Δ)
    ≡⟨ cong DropSub (Drop*◦ σ1 σ2 Δ) ⟩
  DropSub (DropSub* σ1 Δ ◦ σ2)
    ≡⟨ Drop◦ (DropSub* σ1 Δ) σ2 ⟩
  DropSub (DropSub* σ1 Δ) ◦ σ2 ∎

subVar◦ : ∀{Γ1 Γ2 Γ3 t} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
        subVar {t = t} (σ1 ◦ σ2) ≗ sub σ1 ∘ subVar σ2
subVar◦ σ1 (σ2 ▸ e) V0 = refl
subVar◦ σ1 (σ2 ▸ e) (VS x) = subVar◦ σ1 σ2 x

sub◦ : ∀{Γ1 Γ2 Γ3 t} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
      sub {t = t} (σ1 ◦ σ2) ≗ sub σ1 ∘ sub σ2
subVec◦ : ∀{Γ1 Γ2 Γ3 Σ} (σ1 : Sub Γ2 Γ3) (σ2 : Sub Γ1 Γ2) →
      subVec {Σ = Σ} (σ1 ◦ σ2) ≗ subVec σ1 ∘ subVec σ2

sub◦ σ1 σ2 (var x) = subVar◦ σ1 σ2 x
sub◦ σ1 σ2 (constr c es) = cong (constr c) (subVec◦ σ1 σ2 es)

subVec◦ σ1 σ2 [] = refl 
subVec◦ {Σ = (Δ , t) ∷ Σ} σ1 σ2 (e ∷ es) =
  cong₂ _∷_
    (sub (KeepSub* (σ1 ◦ σ2) Δ) e
      ≡⟨ cong (flip sub e) (Keep*◦ σ1 σ2 Δ) ⟩
    sub (KeepSub* σ1 Δ ◦ KeepSub* σ2 Δ) e
      ≡⟨ sub◦ (KeepSub* σ1 Δ) (KeepSub* σ2 Δ) e ⟩ 
    sub (KeepSub* σ1 Δ) (sub (KeepSub* σ2 Δ) e) ∎)
    (subVec◦ σ1 σ2 es)

----------------
-- META-TERMS --
----------------

MTyp : Set
MTyp = Ctx × ⅀ .Knd

MCtx : Set
MCtx = List MTyp

data MVar : MCtx → MTyp → Set where
  MV0 : ∀{Γ t} → MVar (t ∷ Γ) t
  MVS : ∀{Γ s t} (x : MVar Γ t) → MVar (s ∷ Γ) t

data MTm (Γ : MCtx) : MTyp → Set
data MTmVec (Γ : MCtx) : List (Ctx × (⅀ .Knd)) → Set

data MTm Γ where
  mvar : ∀{t} (x : MVar Γ t) → MTm Γ t
  mconstr : (c : ⅀ .TyShape) (es : MTmVec Γ (⅀ .TyPos c .fst)) → MTm Γ ([] , ⅀ .TyPos c .snd)
  inst : ∀{Δ s t} (e : MTm Γ ((s ∷ Δ) , t)) (v : MTm Γ ([] , s)) → MTm Γ (Δ , t)

_⟨_⟩ : ∀{Γ Δ s t} (e : MTm Γ ((s ∷ Δ) , t)) (v : MTm Γ ([] , s)) → MTm Γ (Δ , t)
_⟨_⟩ = inst

data MTmVec Γ where
  [] : MTmVec Γ []
  _∷_ : ∀{Δ t Σ} →
        (e : MTm (map (λ x → [] , x) Δ ++ Γ) ([] , t)) →
        (es : MTmVec Γ Σ) →
        MTmVec Γ ((Δ , t) ∷ Σ)


tmVec++ : ∀{Σ Γ} (η : TmVec Γ Σ) (Δ : Ctx) → TmVec (Δ ++ Γ) (map (λ x → [] , x) Δ ++ Σ)
tmVec++ η [] = η
tmVec++ η (t ∷ Δ) = var V0 ∷ renVec (Drop IdRen) (tmVec++ η Δ)

tmVec++∘subVec : ∀{Σ Γ1 Γ2} (η : TmVec Γ1 Σ) (Δ : Ctx) (σ : Sub Γ1 Γ2) →
            tmVec++ (subVec σ η) Δ ≡ subVec (KeepSub* σ Δ) (tmVec++ η Δ)
tmVec++∘subVec η [] σ = refl
tmVec++∘subVec η (t ∷ Δ) σ = cong (var V0 ∷_) (
  renVec (Drop IdRen) (tmVec++ (subVec σ η) Δ)
    ≡⟨ cong (renVec (Drop IdRen) ) (tmVec++∘subVec η Δ σ) ⟩
  renVec (Drop IdRen) (subVec (KeepSub* σ Δ) (tmVec++ η Δ))
    ≡⟨ sym (subVec•◦ (Drop IdRen) ((KeepSub* σ Δ)) (tmVec++ η Δ)) ⟩
  subVec (DropSub (KeepSub* σ Δ)) (tmVec++ η Δ)
    ≡⟨ cong (λ x → subVec x (tmVec++ η Δ)) (sym (◦•Id (DropSub (KeepSub* σ Δ)))) ⟩
  subVec (DropSub (KeepSub* σ Δ) ◦• IdRen) (tmVec++ η Δ)
    ≡⟨ subVec◦• (KeepSub (KeepSub* σ Δ)) (Drop IdRen) (tmVec++ η Δ) ⟩
  subVec (KeepSub (KeepSub* σ Δ)) (renVec (Drop IdRen) (tmVec++ η Δ)) ∎)

interpVar : ∀{Σ Δ Γ t} → MVar Σ (Δ , t) → TmVec Γ Σ → Sub (Δ ++ Γ) Γ → Tm Γ t
interpVar MV0 (e ∷ η) σ = sub σ e
interpVar (MVS x) (e ∷ η) σ = interpVar x η σ

interpTm : ∀{Σ Δ Γ t} → MTm Σ (Δ , t) → TmVec Γ Σ → Sub (Δ ++ Γ) Γ → Tm Γ t
interpVec : ∀{Σ Δ Γ} → MTmVec Σ Δ → TmVec Γ Σ → TmVec Γ Δ

interpTm (mvar x) η σ = interpVar x η σ
interpTm (mconstr c es) η σ = constr c (interpVec es η)
interpTm (inst e v) η σ = interpTm e η (σ ▸ interpTm v η IdSub)

interpVec [] η = []
interpVec (_∷_ {Δ} e es) η =
  interpTm e (tmVec++ η Δ) IdSub ∷
  interpVec es η

interpVarSub : ∀{Σ Δ Γ1 Γ2 t} (x : MVar Σ (Δ , t)) (η : TmVec Γ1 Σ) (σ : Sub Γ1 Γ2)
              (σ1 : Sub (Δ ++ Γ2) Γ2) (σ2 : Sub (Δ ++ Γ1) Γ1) →
              σ1 ◦ KeepSub* σ Δ ≡ σ ◦ σ2 →
              interpVar x (subVec σ η) σ1 ≡ sub σ (interpVar x η σ2)
interpVarSub {Δ = Δ} MV0 (e ∷ η) σ σ1 σ2 eq =
  sub σ1 (sub (KeepSub* σ Δ) e) ≡⟨ sym (sub◦ σ1 (KeepSub* σ Δ) e) ⟩
  sub (σ1 ◦ KeepSub* σ Δ) e     ≡⟨ cong (flip sub e) eq ⟩
  sub (σ ◦ σ2) e                ≡⟨ sub◦ σ σ2 e ⟩
  sub σ (sub σ2 e)              ∎
interpVarSub (MVS x) (e ∷ η) σ σ1 σ2 eq = interpVarSub x η σ σ1 σ2 eq

interpTmSub : ∀{Σ Δ Γ1 Γ2 t} (e : MTm Σ (Δ , t)) (η : TmVec Γ1 Σ) (σ : Sub Γ1 Γ2)
              (σ1 : Sub (Δ ++ Γ2) Γ2) (σ2 : Sub (Δ ++ Γ1) Γ1) →
              σ1 ◦ KeepSub* σ Δ ≡ σ ◦ σ2 →
              interpTm e (subVec σ η) σ1 ≡ sub σ (interpTm e η σ2)
interpVecSub : ∀{Σ Γ1 Γ2 Δ} (es : MTmVec Σ Δ) (η : TmVec Γ1 Σ) (σ : Sub Γ1 Γ2) →
              interpVec es (subVec σ η) ≡ subVec σ (interpVec es η)

interpTmSub (mvar x) η σ σ1 σ2 eq = interpVarSub x η σ σ1 σ2 eq
interpTmSub (mconstr c es) η σ σ1 σ2 eq = cong (constr c) (interpVecSub es η σ)
interpTmSub (inst {Δ} e v) η σ σ1 σ2 eq =
  interpTmSub e η σ
    (σ1 ▸ interpTm v (subVec σ η) IdSub)
    (σ2 ▸ interpTm v η IdSub)
    (cong₂ _▸_
      ((σ1 ▸ interpTm v (subVec σ η) IdSub) ◦ Drop IdRen •◦ KeepSub* σ Δ
          ≡⟨ ◦•◦ (σ1 ▸ interpTm v (subVec σ η) IdSub) (Drop IdRen) (KeepSub* σ Δ) ⟩
      (σ1 ◦• IdRen) ◦ KeepSub* σ Δ
          ≡⟨ cong (_◦ KeepSub* σ Δ) (◦•Id σ1) ⟩
        σ1 ◦ KeepSub* σ Δ
          ≡⟨ eq ⟩
        σ ◦ σ2 ∎)
      (interpTmSub v η σ IdSub IdSub (Id◦ σ ∙ sym (◦Id σ))))

interpVecSub [] η σ = refl
interpVecSub (_∷_ {Δ} e es) η σ =
  cong₂ _∷_
    (cong (λ x → interpTm e x IdSub) (tmVec++∘subVec η Δ σ)
      ∙ interpTmSub e (tmVec++ η Δ) (KeepSub* σ Δ) IdSub IdSub (Id◦ (KeepSub* σ Δ) ∙ sym (◦Id (KeepSub* σ Δ))))
    (interpVecSub es η σ)
