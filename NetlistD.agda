module NetlistD where

open import Data.Nat

data Vec′ (F : ℕ → ℕ → Set) : ℕ → Set where
  [] : Vec′ F zero
  _∷_ : ∀ {k n} → F k n → Vec′ F (n + k)

infixr 5 _∷_

-- For circuits, F k n = ∃ λ m → Prim m n x (Fin m → Fin k)
