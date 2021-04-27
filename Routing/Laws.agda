{-# OPTIONS --safe --without-K #-}

module Routing.Laws where

open import Level using (0ℓ)

open import Categorical.Laws
open import Categorical.MakeLawful

open import Categorical.Instances.Function

-- TODO: Replace these three imports with "open import Ty hiding (_⇨_)"
open import Ty.Raw using (module ty-instances)
open import Ty.Homomorphism
open import Ty.Laws

open import Routing.Raw
open import Routing.Homomorphism

module routing-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ categoryH

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
