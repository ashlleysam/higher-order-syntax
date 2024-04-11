{-# OPTIONS --safe #-}

open import Data.Product
open import Data.List

open import Common

module SecondOrderSignatures where

-- A second-order binding signature
record SecondOrderSignature : Set₁ where
  field
    
    -- Kinds
    Knd : Set

    -- Type constructor shape
    TyShape : Set

    -- Constructor signature
    TyPos : TyShape → List (List Knd × Knd) × Knd

open SecondOrderSignature public