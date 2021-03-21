-- Another attempt as netlists, this time with better static typing.

module NetlistB where

import Misc as F
open import Ty
open import Symbolic.ExtrinsicTy

private variable A B C D : Ty

mutual

  record NetSrc A : Set where
    inductive
    constructor netSource
    field
      netlist : Netlist
      source : Source netlist A

  data Netlist : Set where
    input : Ty → Netlist
    snoc  : NetSrc A → A p.⇨ B → Netlist

  -- Type as output of a netlist component
  infix 4 _∈_
  data _∈_ (B : Ty) : Netlist → Set where
    input∈ : B ∈ input B
    here   : ∀ {s}{p : A p.⇨ B} → B ∈ snoc s p
    there  : ∀ {s}{p : A p.⇨ B} → B ∈ NetSrc.netlist s → B ∈ snoc s p

  -- Data source
  infixr 8 _∙_
  data Source : Netlist → Ty → Set where
    tt  : ∀ {f} → Source f ⊤
    _∙_ : ∀ {f} → Source f A → Source f B → Source f (A × B)
    bit : ∀ {f} → B ∈ f → BitIx B → Source f Bool

-- Netlist domain: input type
dom : Netlist → Ty
dom (input A) = A
dom (snoc (netSource nl s) _) = dom nl

domˢ : NetSrc A → Ty
domˢ (netSource f _) = dom f

mutual

  ⟦_∈⟧ : ∀ {f} → B ∈ f → dom f →ᵗ B
  ⟦ input∈ ∈⟧ = F.id
  ⟦ here {s = s}{p} ∈⟧ = p.⟦ p ⟧ F.∘ ⟦ s ⟧ˢ         -- TODO: make s & p explicit?
  ⟦ there i ∈⟧ = ⟦ i ∈⟧

  ⟦_⟧ˢ : (s : NetSrc B) → domˢ s →ᵗ B
  ⟦ netSource _ tt ⟧ˢ = F.!
  ⟦ netSource f (s₁ ∙ s₂) ⟧ˢ = ⟦ netSource f s₁ ⟧ˢ F.△ ⟦ netSource f s₂ ⟧ˢ
  ⟦ netSource f (bit B∈f i) ⟧ˢ = ⟦ i ⟧ᵇ F.∘ ⟦ B∈f ∈⟧

  -- Use of F.△ here loses all sharing and so will be inefficient.
  -- Do we care? I think we can improve.

  -- TODO: Try *implicit* netlist in NetSrc.

infix 0 _⇨_
data _⇨_ : Ty → Ty → Set where
  netfun : (s : NetSrc B) → domˢ s ⇨ B
    

⟦_⟧ⁿ : A ⇨ B → A →ᵗ B
⟦ netfun ns ⟧ⁿ = ⟦ ns ⟧ˢ

-- TODO: maybe split s into two netfun arguments

-- TODO: move dom into Netlist type, and rename NetSrc to _⇨_.

-- TODO: Maybe add some optimizations like constant folding and hash consing
-- (common subexpression elimination).
