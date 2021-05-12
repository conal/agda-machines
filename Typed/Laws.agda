{-# OPTIONS --safe --without-K #-}

open import Level using (Level)
open import Categorical.Raw
open import Categorical.Laws
open import Categorical.MakeLawful

module Typed.Laws
    {o ℓ} {obj : Set o}
    ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ)
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Level using (0ℓ)

open import Miscellany using (Function)
open import Categorical.Laws
open import Categorical.MakeLawful
open import Categorical.Instances.Function

open import Typed.Raw          _↠_
open import Typed.Homomorphism _↠_ q

module typed-laws where

  open typed-hom
  instance

    lawful-category : ⦃ _ : Category _↠_ ⦄ ⦃ _ : LawfulCategory _↠_ q ⦄
                    → LawfulCategory _⇨_ q ⦃ equiv = equivalent ⦄
    lawful-category = LawfulCategoryᶠ _↠_

    -- lawful-monoidal : LawfulMonoidal _⇨_ q
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
