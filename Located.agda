{-# OPTIONS --safe --without-K #-}

open import Level using (Level)

open import Categorical.Raw

module Located
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
    {p} (pos : Set p)  -- type of positions (e.g., space-time locations)
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Located.Raw          _↠_
open import Located.Homomorphism _↠_ pos q
open import Located.Laws         _↠_ pos q
