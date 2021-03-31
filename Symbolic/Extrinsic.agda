-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic.Extrinsic where

import Data.Bool as Bool
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≗_; refl)
open import Function using (_on_)

open import Ty

import Misc as F
import Category as C

private
  variable
    A B C D σ τ : Ty

showBit : Boolᵗ → String
showBit Bool.false = "0"
showBit Bool.true  = "1"

-- Generalized routing.
module r where

  infix 1 _⇨_
  _⇨_ : Ty → Ty → Set
  A ⇨ B = TyIx B → TyIx A

  ⟦_⟧′ : A ⇨ B → ∀ {X} → TyF X A → TyF X B
  ⟦_⟧′ = swizzle′

  open C

  instance

    meaningful : ∀ {a b} → Meaningful (a ⇨ b)
    meaningful {a}{b} = record { Meaning = a →ᵗ b ; ⟦_⟧ = λ r → tyfun (swizzle r) }

    category : Category _⇨_
    category = record
      { id = F.id
      ; _∘_ = λ f g → g F.∘ f
      -- ; _≈_ = _≗_
      -- ; id-l = λ _ → refl
      -- ; id-r = λ _ → refl
      -- ; assoc = λ _ → refl
      }

    monoidal : Monoidal _⇨_
    monoidal = record
      { ⊤ = Ty.⊤
      ; _×_ = Ty._×_
      ; _⊗_ = λ f g → λ { (left x) → left (f x) ; (right x) → right (g x) }
      ; unitorᵉˡ = right
      ; unitorᵉʳ = left
      ; unitorⁱˡ = λ { (right y) → y }
      ; unitorⁱʳ = λ { (left  x) → x }
      ; assocʳ = λ { (left x) → left (left x)
                   ; (right (left x)) → left (right x)
                   ; (right (right x)) → right x
                   }
      ; assocˡ = λ { (left (left x)) → left x
                   ; (left (right x)) → right (left x)
                   ; (right x) → right (right x)
                   }
      ; ! = λ ()
      }

    braided : Braided _⇨_
    braided = record { swap = λ { (left x) → right x ; (right x) → left x } }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = left ; exr = right ; dup = λ { (left x) → x ; (right x) → x } }

-- open r hiding (_⇨_)


-- Combinational primitives
module p where

  infix 1 _⇨_
  data _⇨_ : Ty → Ty → Set where
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    not : Bool ⇨ Bool
    const : ⟦ A ⟧ᵗ → ⊤ ⇨ A

  open C

  instance

    meaningful : ∀ {a b} → Meaningful (a ⇨ b)
    meaningful {a}{b} = record
      { Meaning = a →ᵗ b
      ; ⟦_⟧ = λ { ∧ → tyfun (uncurry Bool._∧_)
                ; ∨ → tyfun (uncurry Bool._∨_)
                ; xor → tyfun (uncurry Bool._xor_)
                ; not → tyfun (Bool.not)
                ; (const a) → tyfun (F.const a) }
      }

    p-show : ∀ {a b} → Show (a ⇨ b)
    p-show = record { show = λ { ∧ → "∧"
                               ; ∨ → "∨"
                               ; xor → "xor"
                               ; not → "not"
                               ; (const x) → showTy x
                               }
                    }

  dom : A ⇨ B → Ty
  dom {A}{B} _ = A

  cod : A ⇨ B → Ty
  cod {A}{B} _ = B

-- open p hiding (_⇨_; dom; cod; ∧; ∨; xor; not; const)

-- Combinational circuits
module c where

  infix  0 _⇨_
  infixr 7 _⊗_
  infixr 9 _∘_

  data _⇨_ : Ty → Ty → Set where
    route : A r.⇨ B → A ⇨ B
    prim : A p.⇨ B → A ⇨ B
    _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
    _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D

  open C hiding (_∘_; _⊗_; ⊤; _×_)

  ⟦_⟧ᶜ : A ⇨ B → A →ᵗ B
  ⟦ route f ⟧ᶜ = ⟦ f ⟧
  ⟦ prim  p ⟧ᶜ = ⟦ p ⟧
  ⟦  g ∘ f  ⟧ᶜ = ⟦ g ⟧ᶜ C.∘ ⟦ f ⟧ᶜ
  ⟦  f ⊗ g  ⟧ᶜ = ⟦ f ⟧ᶜ C.⊗ ⟦ g ⟧ᶜ

  instance

    meaningful : ∀ {a b} → Meaningful (a ⇨ b)
    meaningful {a}{b} = record { ⟦_⟧ = ⟦_⟧ᶜ }

    category : Category _⇨_
    category = record
                 { id = route F.id
                 ; _∘_ = _∘_
                 -- ; _≈_ = λ f g → ⟦ f ⟧ ≈ ⟦ g ⟧
                         -- _≈_ on ⟦_⟧
                 -- ; id-l = {!!}
                 -- ; id-r = {!!}
                 -- ; assoc = {!!}
                 }

    monoidal : C.Monoidal _⇨_
    monoidal = record
                 { ⊤ = ⊤
                 ; _×_ = _×_
                 ; _⊗_ = _⊗_
                 ; ! = route !
                 ; unitorᵉˡ = route unitorᵉˡ
                 ; unitorᵉʳ = route unitorᵉʳ
                 ; unitorⁱˡ = route unitorⁱˡ
                 ; unitorⁱʳ = route unitorⁱʳ
                 ; assocʳ   = route assocʳ
                 ; assocˡ   = route assocˡ
                 }

    braided : C.Braided _⇨_
    braided = record { swap = route swap }

    cartesian : C.Cartesian _⇨_
    cartesian = record { exl = route exl ; exr = route exr ; dup = route dup }

-- open c hiding (_⇨_; _∘_; _⊗_; prim; ⟦_⟧ᶜ)

-- Synchronous state machine.
module s where

  open C hiding (⊤; _×_)

  -- For composability, the state type is not visible in the type.
  infix  0 _⇨_
  record _⇨_ (A B : Ty) : Set where
    constructor mealy
    field
      { State } : Ty
      start : ⟦ State ⟧
      transition : A × State c.⇨ B × State

  comb : A c.⇨ B → A ⇨ B
  comb f = mealy tt (first f)

  prim : A p.⇨ B → A ⇨ B
  prim p = comb (c.prim p)

  ∧ ∨ xor : Bool × Bool ⇨ Bool
  not : Bool ⇨ Bool
  ∧   = prim p.∧
  ∨   = prim p.∨
  xor = prim p.xor
  not = prim p.not

  delay : ⟦ A ⟧ᵗ → A ⇨ A
  delay a₀ = mealy a₀ swap

  import Mealy as m

  instance
    meaningful : ∀ {A B} → Meaningful (A ⇨ B)
    meaningful {A}{B} = record
      { Meaning = ⟦ A ⟧ m.⇨ ⟦ B ⟧
      ; ⟦_⟧ = λ { (mealy s₀ f) → m.mealy s₀ (tyfun⁻¹ ⟦ f ⟧) }
      }

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
                   { ⊤ = ⊤
                   ; _×_ = _×_
                   ; _⊗_ = λ { (mealy s₀ f) (mealy t₀ g) →
                       mealy (s₀ , t₀) (transpose ∘ (f ⊗ g) ∘ transpose) }
                   ; ! = comb !
                   ; unitorᵉˡ = comb unitorᵉˡ
                   ; unitorᵉʳ = comb unitorᵉʳ
                   ; unitorⁱˡ = comb unitorⁱˡ
                   ; unitorⁱʳ = comb unitorⁱʳ
                   ; assocʳ   = comb assocʳ
                   ; assocˡ   = comb assocˡ
                   }

    braided : Braided _⇨_
    braided = record { swap = comb swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = comb exl ; exr = comb exr ; dup = comb dup }
