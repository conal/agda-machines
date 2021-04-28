{-# OPTIONS --safe --without-K #-}

module Routing.Laws where

open import Level using (0ℓ)

open import Categorical.Laws
open import Categorical.MakeLawful

open import Categorical.Instances.Function

open import Ty renaming (_⇨_ to _⇨ₜ_)

open import Routing.Raw
open import Routing.Homomorphism

module routing-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ _⇨ₜ_

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
