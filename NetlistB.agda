-- Another attempt as netlists, this time with better static typing.

module NetlistB where

open import Misc
open import Ty
open import Symbolic.ExtrinsicTy

private variable A B C D : Ty

mutual

  data Netlist : Set where
    nil : Netlist
    snoc : (f : Netlist) → Source f A → A p.⇨ B → Netlist

  -- Type as output of a netlist component
  infix 4 _∈_
  data _∈_ (B : Ty) : Netlist → Set where
    here  : ∀ {f}{s : Source f A}{p : A p.⇨ B}          → B ∈ snoc f s p
    there : ∀ {f}{s : Source f A}{p : A p.⇨ B} → B ∈ f → B ∈ snoc f s p

  -- Data source
  infixr 8 _∙_
  data Source : Netlist → Ty → Set where
    tt  : ∀ {f} → Source f ⊤
    bit : ∀ {f} → B ∈ f → BitIx B → Source f Bool
    _∙_ : ∀ {f} → Source f A → Source f B → Source f (A × B)

-- ⟦_⟧ⁿ : Netlist 
