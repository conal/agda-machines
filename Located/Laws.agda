{-# OPTIONS --safe --without-K #-}

open import Level using (Level)
open import Categorical.Raw
open import Categorical.Laws
open import Categorical.MakeLawful

module Located.Laws
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
    {p} (pos : Set p)
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Level using (0ℓ)

open import Miscellany using (Function)
open import Categorical.Laws
open import Categorical.MakeLawful
open import Categorical.Instances.Function

open import Located.Raw          _↠_ pos
open import Located.Homomorphism _↠_ pos q

module located-laws where

  open located-hom
  instance

    lawful-category : ⦃ _ : Category _↠_ ⦄ ⦃ _ : LawfulCategory _↠_ q ⦄
                    → LawfulCategory _⇨_ q ⦃ equiv = equivalent ⦄
    lawful-category = LawfulCategoryᶠ _↠_

    -- lawful-monoidal : LawfulMonoidal _⇨_ q
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
