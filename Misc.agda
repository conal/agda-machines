-- Miscellaneous simply-typed categorical operations on functions

open import Function
open import Data.Product using () renaming (swap to swap×) public
open import Data.Product

private
  variable
    A B C D : Set

id→ : A → A
id→ a = a

infixr 9 _∘→_
_∘→_ : (B → C) → (A → B) → (A → C)
g ∘→ f = g ∘′ f

dup→ : A → A × A
dup→ a = a , a

exl→ : A × B → A
exl→ = proj₁

exr→ : A × B → B
exr→ = proj₂

first→ : (A → C) → (A × B) → (C × B)
first→ f (a , b) = f a , b

second→ : (B → D) → (A × B) → (A × D)
second→ g (a , b) = a , g b

infixr 7 _▵→_
_▵→_ : (A → C) → (A → D) → (A → C × D)
_▵→_ = <_,_>

infixr 7 _⊗→_
_⊗→_ : (A → C) → (B → D) → (A × B → C × D)
f ⊗→ g = map f g

-- (f ⊗→ g) (a , b) = f a , g b
-- f ⊗→ g = f ∘ exl ▵→ g ∘ exr

-- f ▵→ g = (f ⊗ g) ∘ dup

assocʳ→ : (A × B) × C → A × (B × C)
assocʳ→ = assocʳ

assocˡ→ : A × (B × C) → (A × B) × C
assocˡ→ = assocˡ
