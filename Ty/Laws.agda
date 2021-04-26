{-# OPTIONS --safe --without-K #-}

module Ty.Laws where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
  renaming (false to false′; true to true′)
open import Data.Bool.Show as BS
open import Data.Product using (_,_; uncurry)
open import Data.Nat
open import Data.String using (String; parens; _++_)
open import Relation.Binary.PropositionalEquality

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws
open import Categorical.MakeLawful

open import Miscellany
open import Categorical.Instances.Function
open import Ty.Raw
open import Ty.Homomorphism

module ty-laws where

  open ty-hom
  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = LawfulCategoryᶠ categoryH

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
