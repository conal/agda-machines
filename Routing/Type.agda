{-# OPTIONS --safe --without-K #-}

module Routing.Type where

open import Level using (0ℓ)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw 0ℓ
-- open import Categorical.Instances.Setoid.Raw 0ℓ

import Relation.Binary.Bundles as BB
open BB.Setoid using (Carrier)

open import Ty
-- open import Typed.Raw _⟶_ hiding (_⇨_)
open import Typed.Raw (Function {0ℓ}) hiding (_⇨_)

private variable a b c d : Ty

-- Index of a bit in a type
data TyIx : Ty → Set where
  here : TyIx Bool
  left : TyIx a → TyIx (a × b)
  right : TyIx b → TyIx (a × b)
  arg : ⟦ a ⟧ → TyIx b → TyIx (a ⇛ b)

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set where
  constructor mk
  field
    f : TyIx b → TyIx a


-- TODO: Redefine TyIx as a family of types:

open import Data.Empty
open import Data.Sum

TyIx′ : Ty → Set
TyIx′ `⊤ = ⊥
TyIx′ `Bool = ⊤
TyIx′ (a `× b) = TyIx′ a ⊎ TyIx′ b
TyIx′ (a `⇛ b) = ⟦ a ⟧ × TyIx′ b
