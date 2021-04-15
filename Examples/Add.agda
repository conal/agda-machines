open import Category

open import Data.Nat

open import Ty  -- Specialize for speculate

module Examples.Add
         {_⇨′_ : Ty → Ty → Set} (let private infix 0 _⇨_; _⇨_ = _⇨′_)
         ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄ ⦃ _ : Conditional _⇨_ ⦄
 where

-- TODO: package up module parameters into one record to pass in and open.

private variable A B C : Ty

-- Morphism with carry-in and carry-out
infix 0 _⇨ᶜ_
_⇨ᶜ_ : Ty → Ty → Set
A ⇨ᶜ B = A × Bool ⇨ B × Bool

-- Summands ⇨ sum , carry
-- λ (a , b) → (a ⊕ b , a ∧ b)
half : Bool ⇨ᶜ Bool
half = xor △ ∧     -- This _△_ is the only use of Cartesian

-- λ ((a , b) , c) → let (d , p) = half (a , b)
--                       (e , q) = half (d , c) in (e , p ∨ q)

full : Bool × Bool ⇨ᶜ Bool
full = second ∨ ∘ inAssocˡ (first swap) ∘ second half
     ∘ assocʳ ∘ first (swap ∘ half)

-- (a , b) , c
-- (d , p) , c
-- (p , d) , c
-- p , (d , c)
-- p , (e , q)
-- e , (p , q)
-- e , p ∨ q

-- TODO: semantic specifications and correctness proofs.

ripple : (A ⇨ᶜ B) → (n : ℕ) → (V A n ⇨ᶜ V B n)
ripple f   zero  = id
ripple f (suc n) = inAssocʳ′ (ripple f n ∘ swap) ∘ first f ∘ inAssocʳ′ swap

rippleAdd : ∀ n → V (Bool × Bool) n ⇨ᶜ V Bool n
rippleAdd = ripple full

-- ((a , b) , ps) , cᵢ
-- ((a , b) , cᵢ) , ps
-- (o , cₘ) , ps
-- o , (ps , cₘ)
-- o , (os , cₒ)
-- (o , os) , cₒ

constʳ : (⊤ ⇨ B) → (A × B ⇨ C) → (A ⇨ C)
constʳ b f = f ∘ second b ∘ unitorⁱʳ

speculate : (A × Bool ⇨ B) → (A × Bool ⇨ B)
speculate f = cond ∘ second ((constʳ false f ⊗ constʳ true f) ∘ dup) ∘ swap

V² : Ty → ℕ → ℕ → Ty
V² A m n = V (V A n) m

carrySelect : ∀ m n → V² (Bool × Bool) m n ⇨ᶜ V² Bool m n
carrySelect m n = ripple (speculate (ripple full n)) m
