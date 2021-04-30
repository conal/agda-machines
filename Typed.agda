{-# OPTIONS --safe --without-K #-}

open import Level using (Level)

open import Categorical.Raw

module Typed
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Typed.Raw          _↠_
open import Typed.Homomorphism _↠_ q
open import Typed.Laws         _↠_ q
