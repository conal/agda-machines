{-# OPTIONS --safe --without-K #-}
-- Specialized version of Linearize.Raw.

module Linearize.Simple where

open import Level using (Level; 0ℓ)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.String hiding (toList; show)
open import Data.List using (List; []; _∷_)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw

private

  _↠_ : Set → Set → Set
  _↠_ = Function {0ℓ}

  q : Level
  q = 0ℓ

import Typed.Raw _↠_ as t
open t using (Ty; size) renaming (_⇨_ to _⇨ₜ_) public

-- import Primitive _↠_ q as p
-- open p using () renaming (_⇨_ to _⇨ₚ_) public

import Primitive.Raw _↠_ as p
open p using () renaming (_⇨_ to _⇨ₚ_) public

import Routing.Raw as r
open r using (TyIx) renaming (_⇨_ to _⇨ᵣ_) public
open import Routing.Functor renaming (map to mapᵀ) public

open import Linearize.Raw _⇨ₜ_ _⇨ₚ_ _⇨ᵣ_ 0ℓ as k
  using (_∘·first_∘_; ⌞_⌟) renaming (_⇨_ to _⇨ₖ_) public

module instances where
  open import Categorical.Instances.Function.Laws
  open import Categorical.Homomorphism

  open import Routing.Homomorphism public
  open import Typed.Homomorphism _↠_ q public
  open import Typed.Laws _↠_ q public
  open import Primitive.Homomorphism _↠_ q
  open t public hiding (_⇨_)
  open p public hiding (_⇨_)
  open r public hiding (_⇨_)
