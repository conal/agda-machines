module Tinkering.Reflection.Lam where

open import Function
open import Data.Product
open import Data.Unit

private variable A B C D : Set

-- Body of a lambda
data Lam (A : Set) : Set → Set₁ where
  Var : Lam A A
  Con : B → Lam A B
  App : Lam A (B → C) → Lam A B → Lam A C

⟦_⟧ : Lam A B → (A → B)
⟦   Var   ⟧ = id
⟦  Con x  ⟧ = const x
⟦ App u v ⟧ = ⟦ u ⟧ ˢ ⟦ v ⟧

data Arr : Set → Set → Set₁ where
  Id : Arr A A
  Comp : Arr B C → Arr A B → Arr A C
  Const : B → Arr A B
  Fork : Arr A C → Arr A D → Arr A (C × D)

⟦_⟧′ : Arr A B → (A → B)
⟦    Id    ⟧′ = id
⟦ Comp g f ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
⟦ Const b  ⟧′ = λ _ → b
⟦ Fork f g ⟧′ = < ⟦ f ⟧′ , ⟦ g ⟧′ >

-- toArr : Lam A B → Arr A B
-- toArr Var = Id
-- toArr (Con b) = Const b
-- toArr (App u v) = {!!}
