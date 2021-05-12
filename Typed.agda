{-# OPTIONS --safe --without-K #-}

open import Level using (Level)

open import Categorical.Raw

module Typed
    {o ℓ} {obj : Set o}
    ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ)
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Typed.Raw          _↠_    public
open import Typed.Homomorphism _↠_ q  public
open import Typed.Laws         _↠_ q  public
