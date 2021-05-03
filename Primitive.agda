{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives with mapping to another category

open import Level
open import Categorical.Raw

module Primitive
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Primitive.Raw _↠_ public
open import Primitive.Homomorphism _↠_ q public

