-- Another attempt as netlists, this time with better static typing.

module NetlistB where

import Misc as F
open import Ty
open import Symbolic.ExtrinsicTy

private variable A B C D : Ty

mutual

  data Netlist : Set where
    input : Ty → Netlist
    snoc : (f : Netlist) → Source f A → A p.⇨ B → Netlist

  -- Type as output of a netlist component
  infix 4 _∈_
  data _∈_ (B : Ty) : Netlist → Set where
    input∈ : B ∈ input B
    here   : ∀ {f}{s : Source f A}{p : A p.⇨ B}         → B ∈ snoc f s p
    there  : ∀ {f}{s : Source f A}{p : A p.⇨ B} → B ∈ f → B ∈ snoc f s p

  -- Data source
  infixr 8 _∙_
  data Source : Netlist → Ty → Set where
    tt  : ∀ {f} → Source f ⊤
    bit : ∀ {f} → B ∈ f → BitIx B → Source f Bool
    _∙_ : ∀ {f} → Source f A → Source f B → Source f (A × B)

-- Netlist domain: input type
dom : Netlist → Ty
dom (input A) = A
dom (snoc f _ _) = dom f

-- Netlist codomain: most recently added component or input if empty.
cod : Netlist → Ty
cod (input A) = A
cod (snoc _ _ p) = codᵖ p
  where
    codᵖ : A p.⇨ B → Ty
    codᵖ {B = B} _ = B

-- This cod can't work, because it gives no way to translate combinational
-- circuits ending route or _⊗_.

-- infix 0 _⇨_
-- data _⇨_ (A B : Ty) : Set where
--   netlist : (f : Netlist) → 
    

⟦_⟧ⁿ : (f : Netlist) → dom f →ᵗ cod f
⟦ input A ⟧ⁿ = F.id
⟦ snoc f s p ⟧ⁿ = p.⟦ p ⟧ F.∘ {!!}
