{-# OPTIONS --safe --without-K #-}
-- Symbolic category

module Symbolic where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
open import Function using (_on_) renaming (const to const′)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Category
open import Ty
import Primitive as p

private variable A B C D : Ty

infix  0 _⇨_
infixr 7 _`⊗_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set where
  `route : (A r.⇨ B) → (A ⇨ B)
  `prim  : (A p.⇨ B) → (A ⇨ B)
  _`∘_   : (B ⇨ C) → (A ⇨ B) → (A ⇨ C)
  _`⊗_   : (A ⇨ C) → (B ⇨ D) → (A × B ⇨ C × D)

instance

  meaningful : Meaningful (A ⇨ B)
  meaningful = record { ⟦_⟧ = ⟦_⟧′ }
   where
     ⟦_⟧′ : (A ⇨ B) → (A ty.⇨ B)
     ⟦ `route f ⟧′ = ⟦ f ⟧
     ⟦ `prim  p ⟧′ = ⟦ p ⟧
     ⟦  g `∘ f  ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
     ⟦  f `⊗ g  ⟧′ = ⟦ f ⟧′ ⊗ ⟦ g ⟧′

  category : Category _⇨_
  category = record { id = `route id ; _∘_ = _`∘_ }

  ⟦⟧-Hₒ : Homomorphismₒ Ty Ty
  ⟦⟧-Hₒ = record { Fₒ = id }

  ⟦⟧-H : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-H = record { Fₘ = ⟦_⟧ }

  ⟦⟧-categoryH : CategoryH _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-categoryH = record
    { F-id = λ x → swizzle-id
    ; F-∘  = λ g f x → refl   -- direct from _∘_ definition
    }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = H-equiv ⟦⟧-H

  lawful-category : LawfulCategory _⇨_ 0ℓ
  lawful-category = LawfulCategoryᶠ ⟦⟧-categoryH

  monoidal : Monoidal _⇨_
  monoidal = record { _⊗_ = _`⊗_
                    ; !        = `route !
                    ; unitorᵉˡ = `route unitorᵉˡ
                    ; unitorᵉʳ = `route unitorᵉʳ
                    ; unitorⁱˡ = `route unitorⁱˡ
                    ; unitorⁱʳ = `route unitorⁱʳ
                    ; assocʳ   = `route assocʳ
                    ; assocˡ   = `route assocˡ
                    }

  ⟦⟧-productsH : ProductsH
  ⟦⟧-productsH = id-productsH

  ⟦⟧-monoidalH : MonoidalH _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-monoidalH = record
                   { F-!        = λ _ → refl
                   ; F-⊗        = λ f g _ → refl
                   ; F-unitorᵉˡ = λ _ → swizzle-id
                   ; F-unitorⁱˡ = λ _ → swizzle-id
                   ; F-unitorᵉʳ = λ _ → swizzle-id
                   ; F-unitorⁱʳ = λ _ → swizzle-id
                   ; F-assocʳ   = λ _ → swizzle-id
                   ; F-assocˡ   = λ _ → swizzle-id
                   }

  braided : Braided _⇨_
  braided = record { swap = `route swap }

  ⟦⟧-braidedH : BraidedH _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-braidedH = record { F-swap = λ _ → swizzle-id }

  cartesian : Cartesian _⇨_
  cartesian = record { exl = `route exl ; exr = `route exr ; dup = `route dup }

  ⟦⟧-cartesianH : CartesianH _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-cartesianH = record
    { F-exl = λ _ → swizzle-id
    ; F-exr = λ _ → swizzle-id
    ; F-dup = λ _ → swizzle-id
    }

  logic : Logic _⇨_
  logic = record
     { false = `prim false
     ; true  = `prim true
     ; not   = `prim not
     ; ∧     = `prim ∧
     ; ∨     = `prim ∨
     ; xor   = `prim xor
     ; cond  = `prim cond
     }

module m where open import Mealy _⇨_ public
