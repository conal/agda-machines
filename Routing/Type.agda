{-# OPTIONS --safe --without-K #-}

module Routing.Type where

open import Level using (0ℓ)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw

open import Ty
open import Typed.Raw (Function {0ℓ}) hiding (_⇨_)

private variable a b c d : Ty

-- Index of a bit in a type
data TyIx : Ty → Set where
  here : TyIx Bool
  left  : TyIx a → TyIx (a × b)
  right : TyIx b → TyIx (a × b)

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    f : TyIx b → TyIx a
