-- Composable Mealy machines, parametrized by an underlying category considered
-- to be "combinational".
{-# OPTIONS --safe --without-K #-}

open import Level using (_⊔_)
open import Categorical.Raw

module Mealy {o} {obj : Set o} ⦃ _ : Products obj ⦄
        {ℓ}(_↠′_ : obj → obj → Set ℓ) (let private infix 0 _↠_; _↠_ = _↠′_) where

private variable A B C D σ τ : obj

infix 0 _⇨_

-- Pseudo values
⌞_⌟ : obj → Set ℓ
⌞ A ⌟ = ⊤ ↠ A

-- Note: using ⊤ ↠ A obviates needing Meaningful, but it might also prevent any
-- efficient implementation for functions.

-- Synchronous state machine.
-- For composability, the state type is not visible in the type.
record _⇨_ (A B : obj) : Set (ℓ ⊔ o) where
  constructor mealy
  field
    { State } : obj
    start : ⌞ State ⌟
    transition : A × State ↠ B × State

-- Mapping a function (empty state, i.e., combinational logic)
comb : ⦃ _ : Monoidal _↠_ ⦄ → A ↠ B → A ⇨ B
comb f = mealy ! (first f)

delay : ⦃ _ : Braided _↠_ ⦄ → ⌞ A ⌟ → A ⇨ A
delay a₀ = mealy a₀ swap

instance

  -- meaningful : ∀ {A B} → Meaningful {μ = ⟦ A ⟧ m.⇨ ⟦ B ⟧} (A ⇨ B)
  -- meaningful {A}{B} =
  --   record { ⟦_⟧ = λ { (mealy s₀ f) → m.mealy s₀ (ty.mk⁻¹ ⟦ f ⟧) } }

  -- TODO: Give a semantics without values?

  category : ⦃ _ : Braided _↠_ ⦄ → Category _⇨_
  category = record { id = comb id ; _∘_ = _⊙_ }
   where
     _⊙_ : B ⇨ C → A ⇨ B → A ⇨ C
     mealy t₀ g ⊙ mealy s₀ f = mealy (s₀ ⦂ t₀)
       (swiz₂ ∘ second g ∘ swiz₁ ∘ first f ∘ assocˡ)
      where
        swiz₁ : (B × σ) × τ ↠ σ × (B × τ)
        swiz₁ = assocʳ ∘ first swap
        swiz₂ : σ × (C × τ) ↠ C × (σ × τ)
        swiz₂ = inAssocˡ′ swap

  monoidal : ⦃ _ : Braided _↠_ ⦄ → Monoidal _⇨_
  monoidal = record
    { _⊗_ = λ { (mealy s₀ f) (mealy t₀ g) →
              mealy (s₀ ⦂ t₀) (transpose ∘ (f ⊗ g) ∘ transpose) }
    ; ! = comb !
    ; unitorᵉˡ = comb unitorᵉˡ
    ; unitorᵉʳ = comb unitorᵉʳ
    ; unitorⁱˡ = comb unitorⁱˡ
    ; unitorⁱʳ = comb unitorⁱʳ
    ; assocʳ   = comb assocʳ
    ; assocˡ   = comb assocˡ
    }

  braided : ⦃ _ : Braided _↠_ ⦄ → Braided _⇨_
  braided = record { swap = comb swap }

  cartesian : ⦃ _ : Cartesian _↠_ ⦄ → Cartesian _⇨_
  cartesian = record { exl = comb exl ; exr = comb exr ; dup = comb dup }

  logic : ⦃ _ : Monoidal _↠_ ⦄ → ⦃ _ : Boolean obj ⦄ → ⦃ _ : Logic _↠_ ⦄
        → Logic _⇨_
  logic = record { ∧ = comb ∧ ; ∨ = comb ∨ ; xor = comb xor ; not = comb not
                 ; false = comb false ; true = comb true ; cond = comb cond }

