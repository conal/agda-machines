{-# OPTIONS --safe --without-K #-}

module Symbolic.Laws where

open import Level using (0ℓ)

open import Categorical.Laws
open import Categorical.MakeLawful

open import Symbolic.Raw using (_⇨_)
open import Symbolic.Homomorphism
open import Ty renaming (_⇨_ to _⇨ₜ_)

module symbolic-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ _⇨ₜ_

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
