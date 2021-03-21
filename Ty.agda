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

⟦_⟧ᵗ : Ty → Set
⟦ ⊤ ⟧ᵗ     = ⊤ᵗ
⟦ Bool ⟧ᵗ  = Boolᵗ
⟦ σ × τ ⟧ᵗ = ⟦ σ ⟧ᵗ ×ᵗ ⟦ τ ⟧ᵗ

infix 0 _→ᵗ_
_→ᵗ_ : Ty → Ty → Set
A →ᵗ B = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

-- Index of a bit in a type
data BitIx : Ty → Set where
  here : BitIx Bool
  left  : ∀ {A B} → BitIx A → BitIx (A × B)
  right : ∀ {A B} → BitIx B → BitIx (A × B)

-- Extract a bit
⟦_⟧ᵇ : ∀ {A} → BitIx A → A →ᵗ Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y
