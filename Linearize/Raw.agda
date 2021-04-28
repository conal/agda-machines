{-# OPTIONS --safe --without-K #-}

-- A linearizing category, parametrized by primitives. This category embodies a
-- normal form for monoidal formulas as a strictly linear composition of form:
--
--     rₙ ∘ first pₙ₋₁ ∘ rₙ₋₁ ⋯ ∘ first p₀ ∘ r₀
--  
-- where the `pᵢ` are primitive operations and the `rᵢ` are pure routings. This
-- category was designed to capture the simple essence of stack machines and
-- compiling to them homomorphically. It appears also to capture SSA and
-- hardware netlists nicely. Primitives always operate on the first part of a
-- pair ("the accumulator") while preserving the second ("the stack").
-- See http://conal.net/papers/calculating-compilers-categorically .

-- open import Level using (0ℓ; _⊔_)

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws


module Linearize.Raw {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             q ⦃ equivₘ : Equivalent q _⇨ₘ_ ⦄
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ _ : Monoidal _⇨ₘ_ ⦄
             ⦃ _ : Braided  _⇨ᵣ_ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ productsH : ProductsH _⇨ᵣ_ _⇨ₘ_ q ⦄
  where

private variable a b c d z : obj

infix 0 _⇨_
infixr 9 _∘·first_∘_
data _⇨_ : obj → obj → Set ℓ where
  ⌞_⌟ : (r : a ⇨ᵣ b) → (a ⇨ b)
  _∘·first_∘_ : (f : c × z ⇨ d) (p : b ⇨ₚ c) (r : a ⇨ᵣ b × z) → (a ⇨ d)

route : (a ⇨ᵣ b) → (a ⇨ b)
route = ⌞_⌟

prim : (a ⇨ₚ b) → (a ⇨ b)
prim p = ⌞ unitorᵉʳ ⌟ ∘·first p ∘ unitorⁱʳ

infixr 9 _∘ₖ_
_∘ₖ_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
g ∘ₖ (f ∘·first p ∘ r) = (g ∘ₖ f) ∘·first p ∘ r
(g ∘·first p ∘ r₂) ∘ₖ ⌞ r₁ ⌟ = g ∘·first p ∘ (r₂ ∘ r₁)
⌞ r₂ ⌟ ∘ₖ ⌞ r₁ ⌟ = ⌞ r₂ ∘ r₁ ⌟

firstₖ : (a ⇨ c) → (a × b ⇨ c × b)
firstₖ ⌞ r ⌟ = ⌞ first r ⌟
firstₖ (f ∘·first p ∘ r) =
  (firstₖ f ∘ₖ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r)

swapₖ : a × b ⇨ b × a
swapₖ = route swap

secondₖ : (b ⇨ d) → (a × b ⇨ a × d)
secondₖ f = swapₖ ∘ₖ firstₖ f ∘ₖ swapₖ

-- first (first f) ≈ assocˡ ∘ first f ∘ assocʳ

-- first (f ∘ first p ∘ r)
-- first f ∘ first (first p) ∘ first r
-- first f ∘ assocˡ ∘ first f ∘ assocʳ ∘ first r

-- first′ : (Fₒ a ⇨ₘ Fₒ c) → (Fₒ (a × b) ⇨ₘ Fₒ (c × b))
-- first′ f = subst₂′ _⇨ₘ_ F-× F-× (first f)

⟦_⟧ₖ : (a ⇨ b) → (Fₒ a ⇨ₘ Fₒ b)
⟦ ⌞ r ⌟ ⟧ₖ = Fₘ r
⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ μ ∘ first (Fₘ p) ∘ μ⁻¹ ∘ Fₘ r

-- TODO: when proofs are done, consider localizing _∘ₖ_, firstₖ, and secondₖ

instance

  category : Category _⇨_
  category = record { id = route id ; _∘_ = _∘ₖ_ }

  monoidal : Monoidal _⇨_
  monoidal = record
               { _⊗_      = λ f g → secondₖ g ∘ firstₖ f
               ; !        = route !
               ; unitorᵉˡ = route unitorᵉˡ
               ; unitorᵉʳ = route unitorᵉʳ
               ; unitorⁱˡ = route unitorⁱˡ
               ; unitorⁱʳ = route unitorⁱʳ
               ; assocʳ   = route assocʳ
               ; assocˡ   = route assocˡ
               }

  braided : Braided _⇨_
  braided = record { swap = swapₖ }

  cartesian : ⦃ _ : Cartesian _⇨ᵣ_ ⦄ → Cartesian _⇨_
  cartesian = record { exl = route exl ; exr = route exr ; dup = route dup }

  logic : ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _⇨ₚ_ ⦄ → Logic _⇨_
  logic = record
            { false = prim false
            ; true  = prim true
            ; not   = prim not
            ; ∧     = prim ∧
            ; ∨     = prim ∨
            ; xor   = prim xor
            ; cond  = prim cond
            }
