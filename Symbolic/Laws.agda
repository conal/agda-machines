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

-- TODO: Replace with single import
open import Typed.Raw          _↠_ renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism _↠_ q
open import Typed.Laws         _↠_ q

module symbolic-laws where

  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ _⇨ₜ_

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
