{-# OPTIONS --safe --without-K #-}

module Routing.Raw where

open import Data.Product using (_,_)

open import Categorical.Raw

open import Categorical.Instances.Function.Raw
open import Ty.Raw renaming (_⇨_ to _⇨ₜ_)

private variable A B C D : Ty

-- Index of a bit in a type
data TyIx : Ty → Set where
  here : TyIx Bool
  left  : TyIx A → TyIx (A × B)
  right : TyIx B → TyIx (A × B)

swapIx : TyIx (B × A) → TyIx (A × B)
swapIx (left x) = right x
swapIx (right x) = left x

assocIxʳ : TyIx (A × (B × C)) → TyIx ((A × B) × C)
assocIxʳ (left x) = left (left x)
assocIxʳ (right (left x)) = left (right x)
assocIxʳ (right (right x)) = right x

assocIxˡ : TyIx ((A × B) × C) → TyIx (A × (B × C))
assocIxˡ (left (left x)) = left x
assocIxˡ (left (right x)) = right (left x)
assocIxˡ (right x) = right (right x)

infixr 7 _⊗Ix_
_⊗Ix_ : (f : TyIx C → TyIx A) (g : TyIx D → TyIx B) → TyIx (C × D) → TyIx (A × B)
(f ⊗Ix g) (left  x) = left  (f x)
(f ⊗Ix g) (right y) = right (g y)


infix 0 _⇨_
record _⇨_ (A B : Ty) : Set where
  constructor mk
  field
    f : TyIx B → TyIx A

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
