{-# OPTIONS --safe --without-K #-}

-- Simple type/object encodings

module Ty where

infixr 2 _`×_
infixr 0 _`⇛_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : Ty → Ty → Ty
  _`⇛_  : Ty → Ty → Ty

open import Data.Nat

-- Cardinality of a type
card : Ty → ℕ
card `⊤ = 1
card `Bool = 2
card (a `× b) = card a * card b
card (a `⇛ b) = card b ^ card a

-- # of bits in a value of a given type (maybe rename to "#bits").
-- Log₂ of cardinality.
size : Ty → ℕ
size `⊤       = 0
size `Bool    = 1
size (a `× b) = size a + size b
size (a `⇛ b) = size b * card a

-- See Ty.Properties for proof of 

module ty-instances where

  open import Categorical.Raw
  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    exponentials : Exponentials Ty
    exponentials = record { _⇛_ = _`⇛_ }
