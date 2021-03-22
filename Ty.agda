{-# OPTIONS --safe --without-K #-}

module Ty where

open import Data.Unit renaming (⊤ to ⊤ᵗ) public
open import Data.Bool using () renaming (Bool to Boolᵗ) public
open import Data.Product using (_,_; uncurry) renaming (_×_ to _×ᵗ_) public

infixr 2 _×_
data Ty : Set where
  ⊤    : Ty
  Bool : Ty
  _×_  : Ty → Ty → Ty

private variable A B C D : Ty

⟦_⟧ᵗ : Ty → Set
⟦ ⊤ ⟧ᵗ     = ⊤ᵗ
⟦ σ × τ ⟧ᵗ = ⟦ σ ⟧ᵗ ×ᵗ ⟦ τ ⟧ᵗ
⟦ Bool ⟧ᵗ  = Boolᵗ

infix 0 _→ᵗ_
_→ᵗ_ : Ty → Ty → Set
A →ᵗ B = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

-- Index of a bit in a type
data BitIx : Ty → Set where
  here : BitIx Bool
  left  : BitIx A → BitIx (A × B)
  right : BitIx B → BitIx (A × B)

-- Extract a bit
⟦_⟧ᵇ : ∀ {A} → BitIx A → A →ᵗ Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

-- TODO: phase out BitIx and ⟦_⟧ᵇ

-- Index of a subvalue in a type
infix 1 _∈ᵗ_
data _∈ᵗ_ : Ty → Ty → Set where
  here  : A ∈ᵗ A
  left  : A ∈ᵗ B → A ∈ᵗ B × C
  right : A ∈ᵗ C → A ∈ᵗ B × C

-- Extract a subvalue
⟦_∈ᵗ⟧ : ∀ {A} → B ∈ᵗ A → A →ᵗ B
⟦ here    ∈ᵗ⟧ x = x
⟦ left  i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ x
⟦ right i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ y
