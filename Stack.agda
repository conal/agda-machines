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

open import Level using (0ℓ; _⊔_)

open import Category

module Stack {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             q ⦃ equivₘ : Equivalent q _⇨ₘ_ ⦄
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄ -- ⦃ prodH : ProductsH ⦃ Hₒ = Hₒ ⦄ ⦄
             ⦃ _ : Monoidal _⇨ₘ_ ⦄
             ⦃ _ : LawfulCategory _⇨ₘ_ q ⦄  -- probably replace by LawfulMonoidal
             ⦃ _ : Braided  _⇨ᵣ_ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ monoidalHᵣ : MonoidalH _⇨ᵣ_ _⇨ₘ_ q ⦄
  where

private variable a b c d z : obj

open Homomorphismₒ Hₒ using () renaming (Fₒ to ⟦_⟧ₒ)
open Homomorphism  Hₚ using () renaming (Fₘ to ⟦_⟧ₚ)
open Homomorphism  Hᵣ using () renaming (Fₘ to ⟦_⟧ᵣ)
-- open ProductsH prodH
-- open CategoryH categoryHᵣ
open MonoidalH monoidalHᵣ

-- TODO: reconsider having these homomorphism classes open in Category

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

swapₖ : (a × b ⇨ b × a)
swapₖ = route swap

secondₖ : (b ⇨ d) → (a × b ⇨ a × d)
secondₖ f = swapₖ ∘ₖ firstₖ f ∘ₖ swapₖ

-- first (first f) ≈ assocˡ ∘ first f ∘ assocʳ

-- first (f ∘ first p ∘ r)
-- first f ∘ first (first p) ∘ first r
-- first f ∘ assocˡ ∘ first f ∘ assocʳ ∘ first r

-- first′ : (Fₒ a ⇨ₘ Fₒ c) → (Fₒ (a × b) ⇨ₘ Fₒ (c × b))
-- first′ f = subst₂′ _⇨ₘ_ F-× F-× (first f)

open ᴴ obj _⇨ₘ_

⟦_⟧ₖ : (a ⇨ b) → (Fₒ a ⇨ₘ Fₒ b)
⟦ ⌞ r ⌟ ⟧ₖ = ⟦ r ⟧ᵣ
-- ⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ first′ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ
⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ

-- TODO: Maybe move first′ to Category, and likewise for _⊗_, second,
-- associators, and unitors.

-- TODO: when proofs are done, consider localizing _∘ₖ_, firstₖ, and secondₖ

instance

  homomorphism : Homomorphism _⇨_ _⇨ₘ_
  homomorphism = record { Fₘ = ⟦_⟧ₖ }

  equivalent : Equivalent q _⇨_
  equivalent = H-equiv homomorphism

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

open ≈-Reasoning

infixr 9 _⟦∘⟧_
_⟦∘⟧_ : ∀ (g : b ⇨ c) (f : a ⇨ b) → ⟦ g ∘ f ⟧ₖ ≈ ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ

g ⟦∘⟧ (f ∘·first p ∘ r) =
  begin
    ⟦ g ∘ (f ∘·first p ∘ r) ⟧ₖ
  ≡⟨⟩
    ⟦ (g ∘ f) ∘·first p ∘ r ⟧ₖ
  ≡⟨⟩
    ⟦ g ∘ f ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ
  ≈⟨ ∘-resp-≈ˡ (g ⟦∘⟧ f) ⟩
    (⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ) ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ
  ≈⟨ assoc ⟩
    ⟦ g ⟧ₖ ∘ (⟦ f ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ)
  ≡⟨⟩
    ⟦ g ⟧ₖ ∘ ⟦ f ∘·first p ∘ r ⟧ₖ
  ∎

(g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ =
  begin
    ⟦ (g ∘·first p ∘ r₂) ∘ ⌞ r₁ ⌟ ⟧ₖ
  ≡⟨⟩
    ⟦ g ∘·first p ∘ (r₂ ∘ r₁) ⟧ₖ
  ≡⟨⟩
    ⟦ g ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r₂ ∘ r₁ ⟧ᵣ
  ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (F-∘ r₂ r₁)) ⟩
    ⟦ g ⟧ₖ ∘ (firstᴴ ⟦ p ⟧ₚ ∘ (⟦ r₂ ⟧ᵣ ∘ ⟦ r₁ ⟧ᵣ))
  ≈˘⟨ ∘-resp-≈ʳ assoc ⟩
    ⟦ g ⟧ₖ ∘ ((firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r₂ ⟧ᵣ) ∘ ⟦ r₁ ⟧ᵣ)
  ≈˘⟨ assoc ⟩
    (⟦ g ⟧ₖ ∘ (firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r₂ ⟧ᵣ)) ∘ ⟦ r₁ ⟧ᵣ
  ≡⟨⟩
    ⟦ g ∘·first p ∘ r₂ ⟧ₖ ∘ ⟦ ⌞ r₁ ⌟ ⟧ₖ
  ∎

⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘ r₂ r₁

⟦first⟧ : (f : a ⇨ c) → ⟦ firstₖ {b = b} f ⟧ₖ ≈ firstᴴ ⟦ f ⟧ₖ

⟦first⟧ ⌞ r ⌟ = F-first r

-- ⟦first⟧ ⌞ r ⌟ =
--   begin
--     ⟦ firstₖ ⌞ r ⌟ ⟧ₖ
--   ≡⟨⟩
--     ⟦ ⌞ first r ⌟ ⟧ₖ
--   ≡⟨⟩
--     ⟦ first r ⟧ᵣ
--     ≈⟨ F-first ⟩
--     firstᴴ ⟦ r ⟧ᵣ
--   ≡⟨⟩
--     firstᴴ ⟦ ⌞ r ⌟ ⟧ₖ
--   ∎

⟦first⟧ (f ∘·first p ∘ r) =
  begin
    ⟦ firstₖ (f ∘·first p ∘ r) ⟧ₖ
  ≡⟨⟩
    ⟦ (firstₖ f ∘ₖ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r) ⟧ₖ
  ≡⟨⟩
    ⟦ firstₖ f ∘ₖ ⌞ assocˡ ⌟ ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ∘ first r ⟧ᵣ
  ≈⟨ ∘-resp-≈ (firstₖ f ⟦∘⟧ ⌞ assocˡ ⌟) (∘-resp-≈ʳ (F-∘ assocʳ (first r))) ⟩
    (⟦ firstₖ f ⟧ₖ ∘ ⟦ ⌞ assocˡ ⌟ ⟧ₖ) ∘ firstᴴ ⟦ p ⟧ₚ ∘ (⟦ assocʳ ⟧ᵣ ∘ ⟦ first r ⟧ᵣ)
  ≈⟨ {!!} ⟩
    ⟦ firstₖ f ⟧ₖ ∘ (⟦ ⌞ assocˡ ⌟ ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  ≈⟨ {!!} ⟩
    ⟦ firstₖ f ⟧ₖ ∘ (assocᴴˡ ∘ firstᴴ ⟦ p ⟧ₚ ∘ assocᴴʳ) ∘ firstᴴ ⟦ r ⟧ᵣ
  ≈⟨ ∘-resp-≈ˡ (⟦first⟧ f) ⟩
    firstᴴ ⟦ f ⟧ₖ ∘ (assocᴴˡ ∘ firstᴴ ⟦ p ⟧ₚ ∘ assocᴴʳ) ∘ firstᴴ ⟦ r ⟧ᵣ
  ≈⟨ {!!} ⟩
    firstᴴ ⟦ f ∘·first p ∘ r ⟧ₖ
  ∎

-- firstₖ (f ∘·first p ∘ r) = (firstₖ f ∘ₖ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r)

-- ⟦ f ∘·first p ∘ r ⟧ₖ = ⟦ f ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ

instance

  categoryH : CategoryH _⇨_ _⇨ₘ_ q
  categoryH = record { F-id = F-id ; F-∘ = _⟦∘⟧_ }

  lawful-category : LawfulCategory _⇨_ q ⦃ equiv = equivalent ⦄
  lawful-category = LawfulCategoryᶠ categoryH

-- infixr 7 _⟦⊗⟧_
-- _⟦⊗⟧_ : ∀ (f : a ⇨ c) (g : c ⇨ d) → ⟦ f ⊗ g ⟧ ≈ ⟦ f ⟧ ⊗ ⟦ g ⟧
-- f ⟦⊗⟧ g = {!!}

-- open import Relation.Binary.PropositionalEquality
-- ⟦⟧-monoidalH : MonoidalH _⇨_ _⇨ₘ_ 0ℓ ⦃ H = ⟦⟧-H ⦄
-- ⟦⟧-monoidalH = record
--   { categoryH  = ⟦⟧-categoryH
--   ; F-⊗        = {!!}
--   ; F-!        = λ x → swizzle-id
--   ; F-unitorᵉˡ = λ x → swizzle-id
--   ; F-unitorⁱˡ = λ x → swizzle-id
--   ; F-unitorᵉʳ = λ x → swizzle-id
--   ; F-unitorⁱʳ = λ x → swizzle-id
--   ; F-assocʳ   = λ x → swizzle-id
--   ; F-assocˡ   = λ x → swizzle-id
--   }

