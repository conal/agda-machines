{-# OPTIONS --safe --without-K #-}

-- Symbolic category

module Symbolic.Raw where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Data.String using (String)
-- open import Relation.Binary.PropositionalEquality
open import Function using (_on_) renaming (const to const′)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categorical.Raw
open import Categorical.Homomorphism
open import Ty renaming (_⇨_ to _⇨ₜ_)
import Routing.Raw as r
import Routing.Homomorphism as rh
import Primitive as p

open Homomorphism rh.H renaming (Fₘ to ⟦_⟧ᵣ)
open Homomorphism p.H  renaming (Fₘ to ⟦_⟧ₚ)

private variable A B C D : Ty

infix  0 _⇨_
infixr 7 _`⊗_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set where
  `route : (A r.⇨ B) → (A ⇨ B)
  `prim  : (A p.⇨ B) → (A ⇨ B)
  _`∘_   : (B ⇨ C) → (A ⇨ B) → (A ⇨ C)
  _`⊗_   : (A ⇨ C) → (B ⇨ D) → (A × B ⇨ C × D)

module symbolic-raw-instances where

  instance

  --   meaningful : Meaningful (A ⇨ B)
  --   meaningful = record { ⟦_⟧ = ⟦_⟧′ }
  --    where
  --      ⟦_⟧′ : (A ⇨ B) → (A ty.⇨ B)
  --      ⟦ `route f ⟧′ = ⟦ f ⟧
  --      ⟦ `prim  p ⟧′ = ⟦ p ⟧
  --      ⟦  g `∘ f  ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
  --      ⟦  f `⊗ g  ⟧′ = ⟦ f ⟧′ ⊗ ⟦ g ⟧′

    category : Category _⇨_
    category = record { id = `route id ; _∘_ = _`∘_ }

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

    braided : Braided _⇨_
    braided = record { swap = `route swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = `route exl ; exr = `route exr ; dup = `route dup }

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
