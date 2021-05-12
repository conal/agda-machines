{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Level
open import Data.Product using (_,_)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw 0ℓ
-- open import Categorical.Instances.Setoid.Raw 0ℓ

open import Ty
open import Typed.Raw (Function {0ℓ}) hiding (_⇨_)
-- open import Typed.Raw _⟶_ hiding (_⇨_)

open import Routing.Type public

private variable a b c d : Ty

swapIx : TyIx (b × a) → TyIx (a × b)
swapIx (left x) = right x
swapIx (right x) = left x

assocIxʳ : TyIx (a × (b × c)) → TyIx ((a × b) × c)
assocIxʳ (left x) = left (left x)
assocIxʳ (right (left x)) = left (right x)
assocIxʳ (right (right x)) = right x

assocIxˡ : TyIx ((a × b) × c) → TyIx (a × (b × c))
assocIxˡ (left (left x)) = left x
assocIxˡ (left (right x)) = right (left x)
assocIxˡ (right x) = right (right x)

infixr 7 _⊗Ix_
_⊗Ix_ : (f : TyIx c → TyIx a) (g : TyIx d → TyIx b) → TyIx (c × d) → TyIx (a × b)
(f ⊗Ix g) (left  x) = left  (f x)
(f ⊗Ix g) (right y) = right (g y)


instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk f) (mk g) → mk (g ∘ f) }

  monoidal : Monoidal _⇨_
  monoidal = record
    { !        = mk λ ()
    ; _⊗_      = λ (mk f) (mk g) → mk (f ⊗Ix g)
    ; unitorᵉˡ = mk right
    ; unitorᵉʳ = mk left
    ; unitorⁱˡ = mk λ { (right x) → x }
    ; unitorⁱʳ = mk λ { (left  x) → x }
    ; assocˡ   = mk assocIxˡ
    ; assocʳ   = mk assocIxʳ
    }

  -- TODO: Use definitions and properties now in Routing.Homomorphisms

  braided : Braided _⇨_
  braided = record { swap = mk λ { (left x) → right x ; (right x) → left x } }

  cartesian : Cartesian _⇨_
  cartesian = record { exl = mk left
                     ; exr = mk right
                     ; dup = mk λ { (left x) → x ; (right x) → x }
                     }
