open import Category

open import Data.Nat

open import Ty  -- Specialize for speculate

module Examples.Add
         {_⇨′_ : Ty → Ty → Set} (let private infix 0 _⇨_; _⇨_ = _⇨′_)
         ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄ ⦃ _ : Conditional _⇨_ ⦄
 where

-- module Examples.Add
--          {o}{obj : Set o}
--          {_⇨′_ : obj → obj → Set} (let private infix 0 _⇨_; _⇨_ = _⇨′_)
--          ⦃ prodsᵒ : Products obj ⦄ ⦃ booleanᵒ : Boolean obj ⦄
--          ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Logic _⇨_ ⦄
--  where

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

rippleⱽ : (A ⇨ᶜ B) → (n : ℕ) → (V A n ⇨ᶜ V B n)
rippleⱽ f   zero  = id
rippleⱽ f (suc n) = inAssocʳ′ (rippleⱽ f n ∘ swap) ∘ first f ∘ inAssocʳ′ swap

rippleAddⱽ : ∀ n → V (Bool × Bool) n ⇨ᶜ V Bool n
rippleAddⱽ = rippleⱽ full

-- rippleAddⱽ  zero   = id
-- rippleAddⱽ (suc n) = inAssocʳ′ (rippleAddⱽ n ∘ swap) ∘ first full ∘ inAssocʳ′ swap

-- rippleAddⱽ  zero   (tt       , cᵢ) = tt , cᵢ
-- rippleAddⱽ (suc n) ((p , ps) , cᵢ) =
--   let (o , cₘ) = full (p , cᵢ) ; (os , cₒ) = rippleAddⱽ ps cₘ in ((o , os) , cₒ)

-- ((a , b) , ps) , cᵢ
-- ((a , b) , cᵢ) , ps
-- (o , cₘ) , ps
-- o , (ps , cₘ)
-- o , (os , cₒ)
-- (o , os) , cₒ

rippleᵀ : (A ⇨ᶜ B) → (n : ℕ) → (T A n ⇨ᶜ T B n)
rippleᵀ f  zero   = f
rippleᵀ f (suc n) =
  inAssocʳ′ (rippleᵀ f n ∘ swap) ∘ first (rippleᵀ f n) ∘ inAssocʳ′ swap

rippleAddᵀ : ∀ n → T (Bool × Bool) n ⇨ᶜ T Bool n
rippleAddᵀ = rippleᵀ full

-- rippleAddᵀ  zero   = full
-- rippleAddᵀ (suc n) =
--   inAssocʳ′ (rippleAddᵀ n ∘ swap) ∘ first (rippleAddᵀ n) ∘ inAssocʳ′ swap

-- open import Data.Bool using (if_then_else_) renaming (true to true′; false to false′)
-- open import Data.Product using (_,_)
-- speculate : ∀ {A B : Set} → (A × Bool → B) → (A × Bool → B)
-- speculate f (a , b) = if b then f (a , true′) else f (a , false′)
-- speculate f (a , b) = cond (b , f (a , true′) , f (a , false′))

constʳ : (⊤ ⇨ B) → (A × B ⇨ C) → (A ⇨ C)
constʳ b f = f ∘ second b ∘ unitorⁱʳ

speculate : (A × Bool ⇨ B) → (A × Bool ⇨ B)
speculate f = cond ∘ second ((constʳ false f ⊗ constʳ true f) ∘ dup) ∘ swap

-- rippleAddⱽspec : ∀ n → V (Bool × Bool) n × Bool ⇨ V Bool n × Bool
-- rippleAddⱽspec  zero   = id
-- rippleAddⱽspec (suc n) =
--   inAssocʳ′ (rippleAddⱽspec n ∘ swap) ∘ first (speculate full) ∘ inAssocʳ′ swap

-- rippleAddᵀspec : ∀ n → T (Bool × Bool) n × Bool ⇨ T Bool n × Bool
-- rippleAddᵀspec  zero   = speculate full
-- rippleAddᵀspec (suc n) =
--   inAssocʳ′ (rippleAddᵀspec n ∘ swap) ∘ first (rippleAddᵀspec n) ∘ inAssocʳ′ swap

V² T² : Ty → ℕ → Ty
V² A n = V (V A n) n
T² A n = T (T A n) n

carrySelectⱽ : ∀ n → V² (Bool × Bool) n ⇨ᶜ V² Bool n
carrySelectⱽ n = rippleⱽ (speculate (rippleⱽ full n)) n

carrySelectᵀ : ∀ n → T² (Bool × Bool) n ⇨ᶜ T² Bool n
carrySelectᵀ n = rippleᵀ (speculate (rippleᵀ full n)) n

-- carrySelectⱽ  zero   = id
-- carrySelectⱽ (suc n) = {!!}

-- rippleⱽ : (A ⇨ᶜ B) → (n : ℕ) → (V A n ⇨ᶜ V B n)
-- rippleⱽ f   zero  = id
-- rippleⱽ f (suc n) = inAssocʳ′ (rippleⱽ f n ∘ swap) ∘ first f ∘ inAssocʳ′ swap
