module Machine where

open import Level

open import Data.Product

open import Data.Unit
open import Data.List

private
  variable
    a b c d : Set

-- State machine synchronously mapping from List a to List b.
-- For composability, hide the state type.
M : Set → Set → Set (suc 0ℓ)
M a b = ∃ λ (σ : Set) → σ × (a × σ → b × σ)

run : M a b → List a → List b
run (σ , s , f) [] = []
run (σ , s , f) (a ∷ as) = let (b , s′) = f (a , s) in b ∷ run (σ , s′ , f) as

-- Equivalently
run′ : M a b → List a → List b
run′ {a}{b} (σ , s₀ , f) = go s₀
 where
   go : σ → List a → List b
   go s [] = []
   go s (a ∷ as) = let (b , s′) = f (a , s) in b ∷ go s′ as

-- The state types are given explicitly in the combinators below, but Agda can
-- infer them in each case.

-- Mapping a function (empty state)
mapᴹ : (a → b) → M a b
mapᴹ f = ⊤ , tt , map₁ f
                  -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : ∀ {a b c} → M b c → M a b → M a c
(τ , t₀ , g) ∘ (σ , s₀ , f) =
 (σ × τ) , (s₀ , t₀) , λ (a , (s , t)) →
   let (b , s′) = f (a , s)
       (c , t′) = g (b , t)
   in
      c , (s′ , t′)

-- Parallel composition
infixr 10 _⊗_
_⊗_ : M a c → M b d → M (a × b) (c × d)
(σ , s , f) ⊗ (τ , t , g) =
  (σ × τ) , (s , t) , λ ((a , b) , (s , t)) →
    let (c , s′) = f (a , s)
        (d , t′) = g (b , t)
    in
      (c , d) , (s′ , t′)

-- Cons (memory/register)
delay : a → M a a
delay {a} x = a , x , swap
                       -- (λ (next , prev) → prev , next)
