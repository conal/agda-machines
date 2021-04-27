{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Categorical.Instances.Equivalence.Raw
       {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} (equiv : IsEquivalence _∼_) where

-- TODO: Maybe pass in bundle instead

open import Function using (flip)

open IsEquivalence equiv renaming (refl to refl∼; trans to trans∼)

open import Miscellany using (Function)
open import Categorical.Raw

module equiv-raw-instances where

  instance

    category : Category _∼_
    category = record { id = refl∼ ; _∘_ = flip trans∼ }
