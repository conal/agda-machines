module Machine where

open import Level

open import Data.Product

open import Data.Unit
open import Data.List


-- infixr 5 _∷_
-- record Stream (A : Set) : Set where
--   coinductive
--   constructor _∷_
--   field
--     head : A
--     tail : Stream A

private
  variable
    a b c d : Set

M : Set → Set → Set (suc 0ℓ)
M a b = ∃ λ (σ : Set) → σ × (a × σ → b × σ)

run : M a b → List a → List b
run (_ , s , f) [] = []
run (_ , s , f) (a ∷ as) = let (b , s′) = f (a , s) in b ∷ run (_ , s′ , f) as

-- Equivalently
run′ : ∀ {σ : Set} → (a × σ → b × σ) → σ → List a → List b
run′ {a}{b}{σ} f = go
 where
   go : σ → List a → List b
   go s [] = []
   go s (a ∷ as) = let (b , s′) = f (a , s) in b ∷ go s′ as

arr : (a → b) → M a b
arr f = ⊤ , tt , map₁ f
                 -- λ (a , tt) → f a , tt

infixr 9 _∘_
_∘_ : ∀ {a b c} → M b c → M a b → M a c
(τ , t₀ , g) ∘ (σ , s₀ , f) =
 (σ × τ) , (s₀ , t₀) , λ (a , (s , t)) →
   let (b , s′) = f (a , s)
       (c , t′) = g (b , t)
   in
      c , (s′ , t′)

infixr 10 _⊗_
_⊗_ : M a c → M b d → M (a × b) (c × d)
(σ , s , f) ⊗ (τ , t , g) =
  (σ × τ) , (s , t) , λ ((a , b) , (s , t)) →
    let (c , s′) = f (a , s)
        (d , t′) = g (b , t)
    in
      (c , d) , (s′ , t′)

delay : a → M a a
delay {a} x = a , x , swap -- (λ (next , prev) → prev , next)
