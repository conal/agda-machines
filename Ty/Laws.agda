{-# OPTIONS --safe --without-K #-}

module Ty.Laws where

open import Level using (0ℓ)

open import Miscellany using (Function)
open import Categorical.Laws
open import Categorical.MakeLawful

open import Categorical.Instances.Function
open import Ty.Raw
open import Ty.Homomorphism

module ty-laws where

  open ty-hom
  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ Function

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
