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

open import Level using (0ℓ)

module Stack where

open import Data.Product using (∃; _,_)

open import Ty
open import Category
import Primitive as p

private variable a b c d z : Ty

-- Stack operations

infix 0 _⇨_
infixr 9 _∘·first_∘_
data _⇨_ : Ty → Ty → Set where
  ⌞_⌟ : (r : a r.⇨ b) → (a ⇨ b)
  _∘·first_∘_ : (f : c × z ⇨ d) (p : b p.⇨ c) (r : a r.⇨ b × z) → (a ⇨ d)

route : (a r.⇨ b) → (a ⇨ b)
route = ⌞_⌟

prim : (a p.⇨ b) → (a ⇨ b)
prim p = ⌞ unitorᵉʳ ⌟ ∘·first p ∘ unitorⁱʳ

infixr 9 _∘′_
_∘′_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
g ∘′ (f ∘·first p ∘ r) = (g ∘′ f) ∘·first p ∘ r
(g ∘·first p ∘ r₂) ∘′ ⌞ r₁ ⌟ = g ∘·first p ∘ (r₂ ∘ r₁)
⌞ r₂ ⌟ ∘′ ⌞ r₁ ⌟ = ⌞ r₂ ∘ r₁ ⌟

first′ : (a ⇨ c) → (a × b ⇨ c × b)
first′ ⌞ r ⌟ = ⌞ first r ⌟
first′ (f ∘·first p ∘ r) =
  (first′ f ∘′ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r)

second′ : (b ⇨ d) → (a × b ⇨ a × d)
second′ f = route swap ∘′ first′ f ∘′ route swap

-- first (first f) ≈ assocˡ ∘ first f ∘ assocʳ

-- first (f ∘ first p ∘ r)
-- first f ∘ first (first p) ∘ first r
-- first f ∘ assocˡ ∘ first f ∘ assocʳ ∘ first r

-- TODO: when proofs are done, consider localizing _∘′_, first′, and second′

instance

  meaningful : Meaningful (a ⇨ b)
  meaningful = record { ⟦_⟧ = ⟦_⟧′ }
   where
     ⟦_⟧′ : (a ⇨ b) → (a ty.⇨ b)
     ⟦ ⌞ r ⌟ ⟧′ = ⟦ r ⟧
     ⟦ f ∘·first p ∘ r ⟧′ = ⟦ f ⟧′ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧

  category : Category _⇨_
  category = record { id = route id ; _∘_ = _∘′_ }

  monoidal : Monoidal _⇨_
  monoidal = record
               { _⊗_      = λ f g → second′ g ∘ first′ f
               ; !        = route !
               ; unitorᵉˡ = route unitorᵉˡ
               ; unitorᵉʳ = route unitorᵉʳ
               ; unitorⁱˡ = route unitorⁱˡ
               ; unitorⁱʳ = route unitorⁱʳ
               ; assocʳ   = route assocʳ
               ; assocˡ   = route assocˡ
               }

  braided : Braided _⇨_
  braided = record { swap = route swap }

  cartesian : Cartesian _⇨_
  cartesian = record { exl = route exl ; exr = route exr ; dup = route dup }

  logic : Logic _⇨_
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
_⟦∘⟧_ : ∀ (g : b ⇨ c) (f : a ⇨ b) → ⟦ g ∘ f ⟧ ≈ ⟦ g ⟧ ∘ ⟦ f ⟧

g ⟦∘⟧ (f ∘·first p ∘ r) = let open CategoryH r.⟦⟧-categoryH in
  begin
    ⟦ g ∘ (f ∘·first p ∘ r) ⟧
  ≡⟨⟩
    ⟦ (g ∘ f) ∘·first p ∘ r ⟧
  ≡⟨⟩
    ⟦ g ∘ f ⟧ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧
  ≈⟨ ∘-resp-≈ˡ {h = ⟦ g ∘ f ⟧} (g ⟦∘⟧ f) ⟩
    (⟦ g ⟧ ∘ ⟦ f ⟧) ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧
  ≈⟨ assoc {g = ⟦ f ⟧}{h = ⟦ g ⟧} ⟩
    ⟦ g ⟧ ∘ (⟦ f ⟧ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧)
  ≡⟨⟩
    ⟦ g ⟧ ∘ ⟦ f ∘·first p ∘ r ⟧
  ∎

(g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ = let open CategoryH r.⟦⟧-categoryH in
  begin
    ⟦ (g ∘·first p ∘ r₂) ∘ ⌞ r₁ ⌟ ⟧
  ≡⟨⟩
    ⟦ g ∘·first p ∘ (r₂ ∘ r₁) ⟧
  ≡⟨⟩
    ⟦ g ⟧ ∘ first ⟦ p ⟧  ∘ ⟦ r₂ ∘ r₁ ⟧
  ≈⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (∘-resp-≈ʳ {h = first ⟦ p ⟧} (F-∘ r₂ r₁)) ⟩
    ⟦ g ⟧ ∘ (first ⟦ p ⟧ ∘ (⟦ r₂ ⟧ ∘ ⟦ r₁ ⟧))
  ≈˘⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (assoc {f = ⟦ r₁ ⟧}{g = ⟦ r₂ ⟧}{h = first ⟦ p ⟧}) ⟩
    ⟦ g ⟧ ∘ ((first ⟦ p ⟧ ∘ ⟦ r₂ ⟧) ∘ ⟦ r₁ ⟧)
  ≈˘⟨ assoc {g = first ⟦ p ⟧ ∘ ⟦ r₂ ⟧}{h = ⟦ g ⟧}⟩
    (⟦ g ⟧ ∘ (first ⟦ p ⟧ ∘ ⟦ r₂ ⟧)) ∘ ⟦ r₁ ⟧
  ≡⟨⟩
    ⟦ g ∘·first p ∘ r₂ ⟧ ∘ ⟦ ⌞ r₁ ⌟ ⟧
  ∎

⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘ r₂ r₁   where open CategoryH r.⟦⟧-categoryH

⟦⟧-Hₒ : Homomorphismₒ Ty Ty
⟦⟧-Hₒ = record { Fₒ = id }

⟦⟧-H : Homomorphism _⇨_ ty._⇨_
⟦⟧-H = record { Fₘ = ⟦_⟧ }

⟦⟧-categoryH : CategoryH _⇨_ ty._⇨_ 0ℓ ⦃ H = ⟦⟧-H ⦄
⟦⟧-categoryH = record { F-id = λ _ → swizzle-id ; F-∘ = _⟦∘⟧_ }

equivalent : Equivalent 0ℓ _⇨_
equivalent = H-equiv ⟦⟧-H

lawful-category : LawfulCategory _⇨_ 0ℓ ⦃ equiv = equivalent ⦄
lawful-category = LawfulCategoryᶠ ⦃ H = ⟦⟧-H ⦄ ⟦⟧-categoryH

-- ⟦first⟧ : (f : a ⇨ c) → ⟦ first′ {b = b} f ⟧ ≈ first ⟦ f ⟧
-- ⟦first⟧ {b = b} ⌞ r ⌟ =
--   begin
--     ⟦ first′ ⌞ r ⌟ ⟧
--   ≡⟨⟩
--     ⟦ ⌞ first r ⌟ ⟧
--   ≡⟨⟩
--     ⟦ first r ⟧
--   ≡⟨⟩
--     ⟦ r ⊗ id ⟧
--   ≈⟨ F-⊗ {f = r}{g = id} ⟩
--     ⟦ r ⟧ ⊗ ⟦ id {_⇨_ = r._⇨_} ⟧
--   -- ≈⟨ ∘-resp-≈ʳ {_⇨′_ = ty._⇨_} {!F-id!} ⟩
--   ≈⟨ (λ x → {!!}) ⟩
--     ⟦ r ⟧ ⊗ id
--   ≡⟨⟩
--     first ⟦ r ⟧
--   ≡⟨⟩
--     first ⟦ ⌞ r ⌟ ⟧
--   ∎
--  where
--    open ≈-Reasoning
--    instance _ = r.equivalent
--    open MonoidalH r.⟦⟧-monoidalH

-- ⟦first⟧ (f ∘·first p ∘ r) = {!!}

-- ⟦ first′ ⌞ r ⌟ ⟧
-- ⟦ ⌞ first r ⌟ ⟧
-- ⟦ first r ⟧
-- first ⟦ r ⟧
-- first ⟦ ⌞ r ⌟ ⟧

-- first′ : (a ⇨ c) → (a × b ⇨ c × b)
-- first′ ⌞ r ⌟ = ⌞ first r ⌟
-- first′ (f ∘·first p ∘ r) =
--   (first′ f ∘′ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r)


-- infixr 7 _⟦⊗⟧_
-- _⟦⊗⟧_ : ∀ (f : a ⇨ c) (g : c ⇨ d) → ⟦ f ⊗ g ⟧ ≈ ⟦ f ⟧ ⊗ ⟦ g ⟧
-- f ⟦⊗⟧ g = {!!}

-- open import Relation.Binary.PropositionalEquality
-- ⟦⟧-monoidalH : MonoidalH _⇨_ ty._⇨_ 0ℓ ⦃ H = ⟦⟧-H ⦄
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


import Symbolic as s
-- Homomorphic compilation. Pretty and unnecessary. TODO: move this function
-- to Symbolic, and generalize the target category.
compile : a s.⇨ b → a ⇨ b
compile (s.`route r) = route r
compile (s.`prim  p) = prim p
compile ( g s.`∘ f ) = compile g ∘ compile f
compile ( f s.`⊗ g ) = compile f ⊗ compile g
