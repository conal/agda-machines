-- Synchronous stream functions as composable state machines

{-# OPTIONS --safe --without-K #-}

module Machine where

open import Data.Product
open import Data.Unit
open import Data.List

private
  variable
    a b c d : Set

-- State machine synchronously mapping from List a to List b.
-- For composability, the state type is not visible in the type.
record M (a b : Set) : Set₁ where
  constructor mach
  field
    { σ } : Set
    s₀ : σ
    f : a × σ → b × σ

-- We can easily make machines universe-level-polymorphic

⟦_⟧ : M a b → List a → List b
⟦ mach s f ⟧ [] = []
⟦ mach s f ⟧ (a ∷ as) = let (b , s′) = f (a , s) in b ∷ ⟦ mach s′ f ⟧ as

-- Mapping a function (empty state)
mapᴹ : (a → b) → M a b
mapᴹ f = mach tt (map₁ f)
                 -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : M b c → M a b → M a c
mach t₀ g ∘ mach s₀ f = mach (s₀ , t₀) λ (a , (s , t)) →
 let (b , s′) = f (a , s)
     (c , t′) = g (b , t)
 in
    c , (s′ , t′)

-- Parallel composition
infixr 10 _⊗_
_⊗_ : M a c → M b d → M (a × b) (c × d)
mach s f ⊗ mach t g = mach (s , t) λ ((a , b) , (s , t)) →
  let (c , s′) = f (a , s)
      (d , t′) = g (b , t)
  in
    (c , d) , (s′ , t′)

-- Cons (memory/register)
delay : a → M a a
delay a = mach a swap
                 -- (λ (next , prev) → prev , next)

