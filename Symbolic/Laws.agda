{-# OPTIONS --safe --without-K #-}

module Symbolic.Laws where

open import Level using (Level; 0ℓ)

open import Miscellany using (Function)

open import Categorical

open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws

private
  _↠_ : Set → Set → Set
  _↠_ = Function {0ℓ}

  q : Level
  q = 0ℓ

open import Symbolic.Raw using (_⇨_)
open import Symbolic.Homomorphism

open import Typed _↠_ q renaming (_⇨_ to _⇨ₜ_)

module symbolic-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ _⇨ₜ_

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
