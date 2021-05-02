{-# OPTIONS --safe --without-K #-}

-- Symbolic category

module Symbolic.Raw where

open import Level using (Level; 0ℓ)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Instances.Function.Raw
import Categorical.Instances.Function.Laws

private
  _↠_ : Set → Set → Set
  _↠_ = Function {0ℓ}

  q : Level
  q = 0ℓ

open import Typed.Raw _↠_ renaming (_⇨_ to _⇨ₜ_)

import Routing.Raw as r
import Routing.Homomorphism as rh
import Primitive _↠_ q as p

private variable a b c d : Ty

infix  0 _⇨_
infixr 7 _`⊗_
infixr 9 _`∘_

data _⇨_ : Ty → Ty → Set where
  `route : (a r.⇨ b) → (a ⇨ b)
  `prim  : (a p.⇨ b) → (a ⇨ b)
  _`∘_   : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  _`⊗_   : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)

module symbolic-raw-instances where

  instance

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
