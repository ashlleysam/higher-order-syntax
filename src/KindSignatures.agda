{-# OPTIONS --safe #-}

open import Data.Product
open import Data.List

open import Common

module KindSignatures where

-- A kinding signature
record KindSignature : Set₁ where
  field
    
    -- Kinds
    Knd : Set

    -- Type constructor symbols
    TySymb : Set

    -- Type constructor signatures
    TySig : TySymb → List (List Knd × Knd) × Knd

open KindSignature public