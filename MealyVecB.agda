-- Mealy machines indexed by the vector functions they denote

{-# OPTIONS --safe --without-K #-}
{-# OPTIONS --copatterns --guardedness #-}  -- to drop

module MealyVecB where

open import Data.Sum     hiding (map)
open import Data.Product hiding (map) renaming (map₁ to map×₁; swap to swap×)
open import Data.Unit

import VecFun as ◇
import Mealy  as □

open ◇ using (_↠_; _≗_)
-- open □.AsVecFun

private
  variable
    A B C D : Set

infix 0 _⇨_

record _⇨_ {A B : Set} (f : A ↠ B) : Set₁ where
  constructor mealy
  field
    { State } : Set
    start : State
    transition : A × State → B × State
  μ : A ↠ B
  μ [] = []
  μ (a ∷ as) = let b , s′ = f (a , s) in b ∷ ⟦ mealy s′ f ⟧ as

  field
    asVec : ⟦ mealy ⟧ ≗ f
    
