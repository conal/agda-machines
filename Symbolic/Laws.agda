{-# OPTIONS --safe --without-K #-}

module Symbolic.Laws where

open import Level using (0ℓ)

open import Categorical.Laws
open import Categorical.MakeLawful

open import Symbolic.Raw using (_⇨_)
open import Symbolic.Homomorphism
import Ty

module ty-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ categoryH

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
