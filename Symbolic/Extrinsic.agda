-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic.Extrinsic where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Bool using (false;true)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≗_; refl)
open import Function using (_on_) renaming (const to const′)

open import Ty

open import Category

private
  variable
    A B C D σ τ : Ty

showBit : Bool → String
showBit false = "0"
showBit true  = "1"

-- Combinational primitives
module p where

  infix 1 _⇨_
  data _⇨_ : Ty → Ty → Set where
    `∧ `∨ `xor : Bool × Bool ⇨ Bool
    `not : Bool ⇨ Bool
    `const : ⟦ A ⟧ → ⊤ ⇨ A

  instance

    meaningful : ∀ {a b} → Meaningful {μ = a ty.⇨ b} (a ⇨ b)
    meaningful {a}{b} = record
      { ⟦_⟧ = λ { `∧         → ty.mk ∧
                ; `∨         → ty.mk ∨
                ; `xor       → ty.mk xor
                ; `not       → ty.mk not
                ; (`const a) → ty.mk (const a) } }

    p-show : ∀ {a b} → Show (a ⇨ b)
    p-show = record { show = λ { `∧ → "∧"
                               ; `∨ → "∨"
                               ; `xor → "⊕"
                               ; `not → "not"
                               ; (`const x) → showTy x
                               }
                    }

    constants : Constant _⇨_
    constants = record { const = `const }

    logic : Logic _⇨_
    logic = record { ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; not = `not }


-- Combinational circuits
module c where

  infix  0 _⇨_
  infixr 7 _`⊗_
  infixr 9 _`∘_

  data _⇨_ : Ty → Ty → Set where
    `route : A r.⇨ B → A ⇨ B
    `prim : A p.⇨ B → A ⇨ B
    _`∘_ : B ⇨ C → A ⇨ B → A ⇨ C
    _`⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D

  instance

    meaningful : ∀ {a b} → Meaningful (a ⇨ b)
    meaningful {a}{b} = record { ⟦_⟧ = ⟦_⟧′ }
     where
       ⟦_⟧′ : A ⇨ B → A ty.⇨ B
       ⟦ `route f ⟧′ = ⟦ f ⟧
       ⟦ `prim  p ⟧′ = ⟦ p ⟧
       ⟦  g `∘ f  ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
       ⟦  f `⊗ g  ⟧′ = ⟦ f ⟧′ ⊗ ⟦ g ⟧′

    category : Category _⇨_
    category = record { id = `route id ; _∘_ = _`∘_ }

    monoidal : Monoidal _⇨_
    monoidal = record
                 { _⊗_ = _`⊗_
                 ; ! = `route !
                 ; unitorᵉˡ = `route unitorᵉˡ
                 ; unitorᵉʳ = `route unitorᵉʳ
                 ; unitorⁱˡ = `route unitorⁱˡ
                 ; unitorⁱʳ = `route unitorⁱʳ
                 ; assocʳ   = `route assocʳ
                 ; assocˡ   = `route assocˡ
                 }

    braided : Braided _⇨_
    braided = record { swap = `route swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = `route exl ; exr = `route exr ; dup = `route dup }

    constants : Constant _⇨_
    constants = record { const = `prim ∘ const }

    logic : Logic _⇨_
    logic =
      record { ∧ = `prim ∧ ; ∨ = `prim ∨ ; xor = `prim xor ; not = `prim not}

-- Synchronous state machine.
module s where

  -- For composability, the state type is invisible in the type.
  infix  0 _⇨_
  record _⇨_ (A B : Ty) : Set where
    constructor mealy
    field
      { State } : Ty
      start : ⟦ State ⟧
      transition : A × State c.⇨ B × State

  comb : A c.⇨ B → A ⇨ B
  comb f = mealy tt (first f)

  delay : ⟦ A ⟧ → A ⇨ A
  delay a₀ = mealy a₀ swap

  -- import Mealy as m

  instance

    -- meaningful : ∀ {A B} → Meaningful {μ = ⟦ A ⟧ m.⇨ ⟦ B ⟧} (A ⇨ B)
    -- meaningful {A}{B} =
    --   record { ⟦_⟧ = λ { (mealy s₀ f) → m.mealy s₀ (ty.mk⁻¹ ⟦ f ⟧) } }

    category : Category _⇨_
    category = record { id = comb id ; _∘_ = _⊙_ }
     where
       _⊙_ : B ⇨ C → A ⇨ B → A ⇨ C
       mealy t₀ g ⊙ mealy s₀ f = mealy (s₀ , t₀)
         (swiz₂ ∘ second g ∘ swiz₁ ∘ first f ∘ assocˡ)
        where
          swiz₁ : (B × σ) × τ c.⇨ σ × (B × τ)
          swiz₁ = exr ∘ exl △ first exl
          swiz₂ : σ × (C × τ) c.⇨ C × (σ × τ)
          swiz₂ = exl ∘ exr △ second exr

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_ = λ { (mealy s₀ f) (mealy t₀ g) →
                mealy (s₀ , t₀) (transpose ∘ (f ⊗ g) ∘ transpose) }
      ; ! = comb !
      ; unitorᵉˡ = comb unitorᵉˡ
      ; unitorᵉʳ = comb unitorᵉʳ
      ; unitorⁱˡ = comb unitorⁱˡ
      ; unitorⁱʳ = comb unitorⁱʳ
      ; assocʳ = comb assocʳ
      ; assocˡ = comb assocˡ
      }

    braided : Braided _⇨_
    braided = record { swap = comb swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = comb exl ; exr = comb exr ; dup = comb dup }

    constants : Constant _⇨_
    constants = record { const = comb ∘ const }

    logic : Logic _⇨_
    logic = record { ∧ = comb ∧ ; ∨ = comb ∨ ; xor = comb xor ; not = comb not }
