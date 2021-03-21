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

  record NetSource A : Set where
    constructor netSource
    field
      netlist : Netlist
      source : Source netlist A

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

infix 0 _⇨_
data _⇨_ : Ty → Ty → Set where
  netlist : (f : Netlist) → Source f B → dom f ⇨ B
    
-- ⟦_⟧ⁱˢ : Source (input A) B → A →ᵗ B
-- ⟦_⟧ⁱˢ tt = F.!
-- ⟦_⟧ⁱˢ (bit input∈ i) = ⟦ i ⟧ᵇ
-- ⟦_⟧ⁱˢ (s₁ ∙ s₂) = ⟦ s₁ ⟧ⁱˢ F.△ ⟦ s₂ ⟧ⁱˢ

⟦_⟧ⁿ : A ⇨ B → A →ᵗ B
⟦ netlist _ tt ⟧ⁿ = F.!
⟦ netlist f (bit B∈f i) ⟧ⁿ = {!!}
⟦ netlist f (s₁ ∙ s₂) ⟧ⁿ = ⟦ netlist f s₁ ⟧ⁿ F.△ ⟦ netlist f s₂ ⟧ⁿ

-- ⟦ netlist (input _) s ⟧ⁿ = {!s!} -- ⟦ s ⟧ⁱˢ
-- ⟦ netlist (snoc f s′ p) s ⟧ⁿ = {!!}

