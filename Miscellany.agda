{-# OPTIONS --safe --without-K #-}

module Miscellany where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality

private
  variable
    o : Level
    A B : Set o


_≡,≡_ : {a a′ : A}{b b′ : B} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
refl ≡,≡ refl = refl
