open import Category

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

-- Summands ⇨ sum , carry
-- λ (a , b) → (a ⊕ b , a ∧ b)
half : Bool × Bool ⇨ Bool × Bool
half = xor △ ∧     -- This _△_ is the only use of Cartesian

-- λ ((a , b) , c) → let (d , p) = half (a , b)
--                       (e , q) = half (d , c) in (e , p ∨ q)

full : (Bool × Bool) × Bool ⇨ Bool × Bool
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

open import Data.Nat

rippleV : ∀ n → V (Bool × Bool) n × Bool ⇨ V Bool n × Bool
rippleV  zero   = id
rippleV (suc n) = inAssocʳ′ (rippleV n ∘ swap) ∘ first full ∘ inAssocʳ′ swap

-- rippleV  zero   (tt       , cᵢ) = tt , cᵢ
-- rippleV (suc n) ((p , ps) , cᵢ) =
--   let (o , cₘ) = full (p , cᵢ) ; (os , cₒ) = rippleV ps cₘ in ((o , os) , cₒ)

-- ((a , b) , ps) , cᵢ
-- ((a , b) , cᵢ) , ps
-- (o , cₘ) , ps
-- o , (ps , cₘ)
-- o , (os , cₒ)
-- (o , os) , cₒ

rippleT : ∀ n → T (Bool × Bool) n × Bool ⇨ T Bool n × Bool
rippleT  zero   = full
rippleT (suc n) =
  inAssocʳ′ (rippleT n ∘ swap) ∘ first (rippleT n) ∘ inAssocʳ′ swap

-- open import Data.Bool using (if_then_else_) renaming (true to true′; false to false′)
-- open import Data.Product using (_,_)
-- speculate : ∀ {A B : Set} → (A × Bool → B) → (A × Bool → B)
-- speculate f (a , b) = if b then f (a , true′) else f (a , false′)
-- speculate f (a , b) = cond (b , f (a , true′) , f (a , false′))

constʳ : ∀ {A B C} → (⊤ ⇨ B) → (A × B ⇨ C) → (A ⇨ C)
constʳ b f = f ∘ second b ∘ unitorⁱʳ

speculate : ∀ {A B} → (A × Bool ⇨ B) → (A × Bool ⇨ B)
speculate f = cond ∘ second ((constʳ false f ⊗ constʳ true f) ∘ dup) ∘ swap

rippleVspec : ∀ n → V (Bool × Bool) n × Bool ⇨ V Bool n × Bool
rippleVspec  zero   = id
rippleVspec (suc n) =
  inAssocʳ′ (rippleVspec n ∘ swap) ∘ first (speculate full) ∘ inAssocʳ′ swap

rippleTspec : ∀ n → T (Bool × Bool) n × Bool ⇨ T Bool n × Bool
rippleTspec  zero   = speculate full
rippleTspec (suc n) =
  inAssocʳ′ (rippleTspec n ∘ swap) ∘ first (rippleTspec n) ∘ inAssocʳ′ swap
