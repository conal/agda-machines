{-# OPTIONS --safe --without-K #-}
-- Symbolic category

open import Category
open import Ty

module Symbolic {oᵖ}{objᵖ : Set oᵖ}
         ⦃ prodsᵒ : Products objᵖ ⦄ ⦃ booleanᵒ : Boolean objᵖ ⦄
         (_⇨ᵖ′_ : objᵖ → objᵖ → Set) (let private infix 0 _⇨ᵖ_; _⇨ᵖ_ = _⇨ᵖ′_)
         ⦃ primH : Homomorphism _⇨ᵖ_ ty._⇨_ ⦄
         ⦃ prodsH : ProductsH {obj₁ = objᵖ}{obj₂ = Ty}  ⦄
  where

module Symbolic where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
open import Function using (_on_) renaming (const to const′)
import Relation.Binary.Reasoning.Setoid as SetoidR

private
  variable
    a b : objᵖ
    A B C D : Ty

⟦_⟧ᵒ : objᵖ → Ty
⟦_⟧ᵒ = Homomorphism.Fₒ primH

⟦_⟧ᵖ : ∀ {a b : objᵖ} → (a ⇨ᵖ b) → (⟦ a ⟧ᵒ ty.⇨ ⟦ b ⟧ᵒ)
⟦_⟧ᵖ = Homomorphism.Fₘ primH

infix  0 _⇨_
infixr 7 _`⊗_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set oᵖ where
  `route : (A r.⇨ B) → (A ⇨ B)
  `prim  : (a ⇨ᵖ b) → (⟦ a ⟧ᵒ ⇨ ⟦ b ⟧ᵒ)
  _`∘_   : (B ⇨ C) → (A ⇨ B) → (A ⇨ C)
  _`⊗_   : (A ⇨ C) → (B ⇨ D) → (A × B ⇨ C × D)

instance

  meaningful : Meaningful (A ⇨ B)
  meaningful = record { ⟦_⟧ = ⟦_⟧′ }
   where
     ⟦_⟧′ : (A ⇨ B) → (A ty.⇨ B)
     ⟦ `route f ⟧′ = ⟦ f ⟧
     ⟦ `prim  p ⟧′ = ⟦ p ⟧ᵖ
     ⟦  g `∘ f  ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
     ⟦  f `⊗ g  ⟧′ = ⟦ f ⟧′ ⊗ ⟦ g ⟧′

  category : Category _⇨_
  category = record { id = `route id ; _∘_ = _`∘_ }

  ⟦⟧-homomorphismₒ : Homomorphismₒ Ty Ty
  ⟦⟧-homomorphismₒ = record { Fₒ = id }

  ⟦⟧-homomorphism : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-homomorphism = record { Fₘ = ⟦_⟧ }

  ⟦⟧-categoryH : CategoryH _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-categoryH = record
    { F-id = λ x → swizzle-id
    ; F-∘  = λ g f x → refl   -- direct from _∘_ definition
    }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = F-equiv ⟦⟧-categoryH

  lawful-category : LawfulCategory 0ℓ _⇨_
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
  ⟦⟧-monoidalH = record { F-! = λ _ → refl ; F-⊗ = λ _ → refl }

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

  logic : ⦃ _ : Logic _⇨ᵖ_ ⦄ → ⦃ logicH : LogicH _⇨ᵖ_ ty._⇨_ 0ℓ ⦄ → Logic _⇨_
  logic ⦃ logicH = logicH ⦄ = record
     { false = p₀ false
     ; true  = p₀ true
     ; not   = p₁ not
     ; ∧     = p₂ ∧
     ; ∨     = p₂ ∨
     ; xor   = p₂ xor
     }
    where
     open LogicH logicH

     -- TODO: Fix F-n⇨1′ etc in LogicH to replace p₀ etc
     p₀ : (⊤ ⇨ᵖ Bool) → (⊤ ⇨ Bool)
     p₀ f = subst₂ _⇨_ F-⊤ F-Bool (`prim f)
     p₁ : (Bool ⇨ᵖ Bool) → (Bool ⇨ Bool)
     p₁ f = subst₂ _⇨_ F-Bool F-Bool (`prim f)
     p₂ : (Bool × Bool ⇨ᵖ Bool) → (Bool × Bool ⇨ Bool)
     p₂ f = subst₂ _⇨_ (trans F-× (cong₂ _×_ F-Bool F-Bool)) F-Bool (`prim f)

module m where open import Mealy _⇨_ public
