{-# OPTIONS --safe --without-K #-}
-- Symbolic category

open import Category
open import Ty

module Symbolic (_↠′_ : Ty → Ty → Set) (let private infix 0 _↠_; _↠_ = _↠′_)
  ⦃ _ : ∀ {A B} → Meaningful {μ = A ty.⇨ B} (A ↠ B) ⦄ where

module Symbolic where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
open import Function using (_on_) renaming (const to const′)
import Relation.Binary.Reasoning.Setoid as SetoidR

private variable A B C D : Ty

infix  0 _⇨_
infixr 7 _`⊗_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set where
  `route : (A r.⇨ B) → (A ⇨ B)
  `prim  : (A ↠ B) → (A ⇨ B)
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

  ⟦⟧-homomorphismₒ : Homomorphismₒ Ty Ty
  ⟦⟧-homomorphismₒ = record { Fₒ = id }

  ⟦⟧-homomorphism : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-homomorphism = record { Fₘ = ⟦_⟧ }

  ⟦⟧-functor : Functor _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-functor = record
    { F-id = λ x → swizzle-id
    ; F-∘  = λ g f x → refl   -- direct from _∘_ definition
    }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = F-equiv ⟦⟧-functor

  lawful-category : LawfulCategory 0ℓ _⇨_
  lawful-category = LawfulCategoryᶠ ⟦⟧-functor

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

  ⟦⟧-monoidalFunctor : MonoidalFunctor _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-monoidalFunctor = record { F-! = λ _ → refl ; F-⊗ = λ _ → refl }

  braided : Braided _⇨_
  braided = record { swap = `route swap }

  ⟦⟧-braided-functor : BraidedFunctor _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-braided-functor = record { F-swap = λ _ → swizzle-id }

  cartesian : Cartesian _⇨_
  cartesian = record { exl = `route exl ; exr = `route exr ; dup = `route dup }

  ⟦⟧-cartesian-functor : CartesianFunctor _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-cartesian-functor = record
    { F-exl = λ _ → swizzle-id
    ; F-exr = λ _ → swizzle-id
    ; F-dup = λ _ → swizzle-id
    }

  logic : ⦃ Logic _↠_ ⦄ → Logic _⇨_
  logic = record { ∧ = `prim ∧ ; ∨ = `prim ∨ ; xor = `prim xor ; not = `prim not
                 ; false = `prim false ; true = `prim true }

  -- ⟦⟧-logicH : ⦃ Logic _↠_ ⦄ → LogicH _⇨_ ty._⇨_ 0ℓ
  -- ⟦⟧-logicH = ?

module m where open import Mealy _⇨_ public
