-- Synchronous stream functions as composable state machines

{-# OPTIONS --safe --without-K #-}

module Machine where

open import Level

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

run : M a b → List a → List b
run (mach s f) [] = []
run (mach s f) (a ∷ as) = let (b , s′) = f (a , s) in b ∷ run (mach s′ f) as

-- Equivalently, highlight the constancy of the state transition function
run′ : M a b → List a → List b
run′ {a}{b} (mach {σ} s₀ f) = go s₀
 where
   go : σ → List a → List b
   go s [] = []
   go s (a ∷ as) = let (b , s′) = f (a , s) in b ∷ go s′ as

-- Mapping a function (empty state)
mapᴹ : (a → b) → M a b
mapᴹ f = mach tt (map₁ f)
                 -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : ∀ {a b c} → M b c → M a b → M a c
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

