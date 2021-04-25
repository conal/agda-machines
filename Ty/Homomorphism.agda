{-# OPTIONS --safe --without-K #-}

module Ty.Homomorphism where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
  renaming (false to false′; true to true′)
open import Data.Bool.Show as BS
open import Data.Product using (_,_; uncurry)
open import Data.Nat
open import Data.String using (String; parens; _++_)
open import Relation.Binary.PropositionalEquality

open import Categorical.Raw
open import Categorical.Homomorphism

open import Ty.Raw

module ty-hom-instances where

  instance

    H : Homomorphism _⇨_ (Function {0ℓ})
    H = record { Fₘ = _⇨_.⟦_⟧ }

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = H-equiv H

    categoryH : CategoryH _⇨_ Function 0ℓ
    categoryH = record { F-id = λ x → refl ; F-∘ = λ f g x → refl }

    -- lawful-category : LawfulCategory _⇨_ 0ℓ
    -- lawful-category = LawfulCategoryᶠ ⟦⟧-categoryH

    productsH : ProductsH _⇨_ Function 0ℓ
    productsH = record
                  { ε     = id
                  ; μ     = id
                  ; ε⁻¹   = id
                  ; μ⁻¹   = id
                  ; ε∘ε⁻¹ = λ x → refl
                  ; ε⁻¹∘ε = λ x → refl
                  ; μ∘μ⁻¹ = λ x → refl
                  ; μ⁻¹∘μ = λ x → refl
                  }

    monoidalH : MonoidalH _⇨_ Function 0ℓ
    monoidalH = record
                  { F-unitorᵉˡ = λ x → refl
                  ; F-unitorⁱˡ = λ x → refl
                  ; F-unitorᵉʳ = λ x → refl
                  ; F-unitorⁱʳ = λ x → refl
                  ; F-assocˡ   = λ x → refl
                  ; F-assocʳ   = λ x → refl
                  ; F-!        = λ x → refl
                  ; F-⊗        = λ f g x → refl
                  }

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ ⟦⟧-monoidalH

    -- ⟦⟧-braidedH : BraidedH _⇨_ Function 0ℓ
    -- ⟦⟧-braidedH = record { F-swap = λ x → refl }

    -- ⟦⟧-cartesianH : CartesianH _⇨_ Function 0ℓ
    -- ⟦⟧-cartesianH = record
    --   { F-exl = λ _ → refl ; F-exr = λ _ → refl ; F-dup = λ _ → refl }

    -- ⟦⟧-logicH : LogicH _⇨_ Function 0ℓ
    -- ⟦⟧-logicH = record
    --    { F-Bool  = refl
    --    ; F-false = λ _ → refl
    --    ; F-true  = λ _ → refl
    --    ; F-not   = λ _ → refl
    --    ; F-∧     = λ _ → refl
    --    ; F-∨     = λ _ → refl
    --    ; F-xor   = λ _ → refl
    --    }


