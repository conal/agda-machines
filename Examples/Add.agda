open import Category

open import Data.Nat

open import Ty  -- Specialize for speculate

module Examples.Add
         {_⇨_ : Ty → Ty → Set} (let private infix 0 _⇨_; _⇨_ = _⇨_)
         ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
 where

-- TODO: package up module parameters into one record to pass in and open.

private variable A B C : Ty

-- Morphism with carry-in and carry-out
infix 0 _⇨ᶜ_
_⇨ᶜ_ : Ty → Ty → Set
A ⇨ᶜ B = Bool × A ⇨ B × Bool

-- Summands ⇨ sum , carry
-- λ (c , a) → (c ⊕ z , c ∧ a)
halfAdd : Bool ⇨ᶜ Bool
halfAdd = xor △ ∧

fullAdd : Bool × Bool ⇨ᶜ Bool
fullAdd = second ∨ ∘ inAssocˡ′ halfAdd ∘ second halfAdd

-- λ (c , (a , b)) → let (p , d) = halfAdd (a , b)
--                       (q , e) = halfAdd (c , p) in (q , e ∨ d)

-- c , (a , b)
-- c , (p , d)
-- q , (e , d)
-- q , e ∨ d

-- TODO: semantic specifications and correctness proofs.

ripple : (A ⇨ᶜ B) → (n : ℕ) → (V A n ⇨ᶜ V B n)
ripple f  zero   = swap
ripple f (suc n) = assocˡ ∘ second (ripple f n) ∘ inAssocˡ′ f

-- cᵢ , (a , as)
-- b , (c′ , as)
-- b , (bs , cₒ)
-- (b , bs) , cₒ

rippleAdd : ∀ n → V (Bool × Bool) n ⇨ᶜ V Bool n
rippleAdd = ripple fullAdd

constˡ : (A × B ⇨ C) → (⊤ ⇨ A) → (B ⇨ C)
constˡ f a = f ∘ first a ∘ unitorⁱˡ

-- b
-- tt , b
-- a , b
-- f (a , b)

speculate : (Bool × A ⇨ B) → (Bool × A ⇨ B)
speculate f = cond ∘ second (constˡ f false △ constˡ f true)

-- (cᵢ , a)
-- (cᵢ , (f (false , a) , f (true , a)))
-- cond (cᵢ , (f (false , a) , f (true , a)))

V² : Ty → ℕ → ℕ → Ty
V² A m n = V (V A n) m

carrySelect : ∀ m n → V² (Bool × Bool) m n ⇨ᶜ V² Bool m n
carrySelect m n = ripple (speculate (ripple fullAdd n)) m
