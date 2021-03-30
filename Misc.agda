{-# OPTIONS --safe --without-K #-}

-- Miscellaneous simply-typed categorical operations on functions

open import Level
open import Data.Unit
import Data.Product as ×
open × using (_,_; _×_)

private
  variable
    ℓ : Level
    A B C D : Set ℓ

const : B → A → B
const b a = b

id : A → A
id a = a

infixr 9 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

dup : A → A × A
dup a = a , a

exl : A × B → A
exl (a , b) = a

exr : A × B → B
exr (a , b) = b

first : (A → C) → (A × B) → (C × B)
first f (a , b) = f a , b

second : (B → D) → (A × B) → (A × D)
second g (a , b) = a , g b

infixr 7 _△_
_△_ : (A → C) → (A → D) → (A → C × D)
_△_ = ×.<_,_>

infixr 7 _⊗_
_⊗_ : (A → C) → (B → D) → (A × B → C × D)
f ⊗ g = ×.map f g

-- (f ⊗ g) (a , b) = f a , g b
-- f ⊗ g = f ∘ exl △ g ∘ exr

-- f △ g = (f ⊗ g) ∘ dup

assocʳ : (A × B) × C → A × (B × C)
assocʳ = ×.assocʳ

assocˡ : A × (B × C) → (A × B) × C
assocˡ = ×.assocˡ

swap× : A × B → B × A
swap× = ×.swap

transpose : (A × B) × (C × D) → (A × C) × (B × D)
transpose ((a , b) , (c , d)) = (a , c) , (b , d)

-- Elimination half of unitor isomorphisms
unitorᵉˡ : ⊤ × A → A
unitorᵉˡ = exr

unitorᵉʳ : A × ⊤ → A
unitorᵉʳ = exl

-- Introduction half of unitor isomorphisms
unitorⁱˡ : A → ⊤ × A
unitorⁱˡ = tt ,_

unitorⁱʳ : A → A × ⊤
unitorⁱʳ = _, tt

! : A → ⊤
! _ = tt

open import Data.Sum renaming (map to map⊎)
infixr 6 _⊕_
_⊕_ : (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
_⊕_ = map⊎

jam : ∀ {a}{A : Set a} → A ⊎ A → A
jam (inj₁ x) = x
jam (inj₂ y) = y
