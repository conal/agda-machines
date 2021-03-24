-- Another attempt as netlists, this time with better static typing.

-- module NetlistB where

import Misc as F
open import Ty
open import Symbolic.ExtrinsicTy

private variable A B C D X : Ty

mutual

  -- Netlist with typed input and compatible identified output source
  infix 0 _⇨_
  record _⇨_ (A B : Ty) : Set where
    inductive
    constructor netFun
    field
      { netlist } : Netlist A
      source : Source netlist B

  -- Netlist with input type
  infixr 5 _∷_
  data Netlist (A : Ty) : Set where
    [] : Netlist A
    _∷_  : B p.⇨ C → A ⇨ B → Netlist A

  private variable nets : Netlist A

  -- Type as output of a netlist component
  infix 4 _∈_
  data _∈_ (C : Ty) : Netlist A → Set where
    input∈ : C ∈ [] {C}
    here   : ∀ (f : A ⇨ B) (p : B p.⇨ C)          → C ∈ p ∷ f
    there  : ∀ {f : A ⇨ B} {p : B p.⇨ D} → C ∈⇨ f → C ∈ p ∷ f

  infix 4 _∈⇨_
  _∈⇨_ : Ty → A ⇨ B → Set
  C ∈⇨ netFun { nets } _ = C ∈ nets

  -- Data source
  infixr 8 _∙_
  data Source : Netlist A → Ty → Set where
    tt  : Source nets ⊤
    _∙_ : Source nets B → Source nets C → Source nets (B × C)
    val : C ∈ nets → B ∈ᵗ C → Source nets B

mutual

  ⟦_∈⟧ : {nets : Netlist A} → B ∈ nets → A →ᵗ B
  ⟦ input∈   ∈⟧ = F.id
  ⟦ here f p ∈⟧ = p.⟦ p ⟧ F.∘ ⟦ f ⟧
  ⟦ there i  ∈⟧ = ⟦ i ∈⟧

  ⟦_⟧ : A ⇨ B → A →ᵗ B
  ⟦ netFun tt ⟧ = F.!
  ⟦ netFun (s₁ ∙ s₂) ⟧ = ⟦ netFun s₁ ⟧ F.△ ⟦ netFun s₂ ⟧
  ⟦ netFun (val B∈f i) ⟧ = ⟦ i ∈ᵗ⟧ F.∘ ⟦ B∈f ∈⟧

  -- Use of F.△ here loses all sharing and so will be inefficient.
  -- Do we care? I think we can improve.


-- TODO: Maybe add some optimizations like constant folding and hash consing
-- (common subexpression elimination).

netIn : Source ([] {A}) B → A ⇨ B
netIn = netFun                  -- type specialization

idˢ : Source ([] {A}) A
idˢ = val input∈ here

id : A ⇨ A
id = netIn idˢ

exl : A × B ⇨ A
exl = netIn (val input∈ (left here))

exr : A × B ⇨ B
exr = netIn (val input∈ (right here))

dup : A ⇨ A × A
dup = netIn (idˢ ∙ idˢ)

! : A ⇨ ⊤
! = netIn tt

-- mutual

--   infixr 5 _++ⁿ_
--   _++ⁿ_ : Netlist B → Netlist A → Netlist A
--   [] ++ⁿ a = a
--   (p ∷ netFun {b} s) ++ⁿ a = p ∷ netFun {netlist = b ++ⁿ a} {!!} -- (bumpˢ b a s)

--   bumpˢ : ∀ (b : Netlist D) (a : Netlist A) (s : Source b B) → Source (b ++ⁿ a) B
--   bumpˢ = {!!}

--   bumpˢ : ∀ (b : Netlist B) (a : Netlist A) (s : Source a D) → Source (b ++ⁿ a) D
--   bumpˢ [] a s = s
--   bumpˢ (p ∷ netFun source) a s = {!!}

bar : {f : Netlist A} → X ∈ᵗ B → Source f B → Source f X
bar here fs = fs
bar (left  X∈ᵗB×C) (fs₁ ∙ fs₂) = bar X∈ᵗB×C fs₁
bar (right X∈ᵗB×C) (fs₁ ∙ fs₂) = bar X∈ᵗB×C fs₂
bar X∈ᵗB (val C∈f B∈ᵗC) = val C∈f (B∈ᵗC ∘∈ᵗ X∈ᵗB)

foo : {f : Netlist A} → Source ([] {B}) X → Source f B → Source f X
foo tt fs = tt
foo (gs₁ ∙ gs₂) fs = foo gs₁ fs ∙ foo gs₂ fs
foo (val input∈ C∈ᵗB) fs = bar C∈ᵗB fs

mutual

  infixr 9 _∘_
  _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
  netFun {[]} gs ∘ netFun {f} fs = netFun {netlist = f} (foo gs fs)
  netFun {p ∷ g} tt ∘ f = netFun {netlist = []} tt
  netFun {p ∷ g} (gs₁ ∙ gs₂) ∘ f = netFun gs₁ ∘ f △ netFun gs₂ ∘ f  -- hm
  netFun {p ∷ g} (val (here .g .p) C∈ᵗD) ∘ f = netFun (val (here (g ∘ f) p) C∈ᵗD)
  netFun {p ∷ g} (val (there x) C∈ᵗD) ∘ f = netFun (val x C∈ᵗD) ∘ f

--   infixr 7 _△_
--   _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
--   f △ g = {!!}

-- first : A ⇨ C → A × B ⇨ C × B
-- first f = {!!}

-- f : A ⇨ B
-- g : B ⇨ B₁

-- g ∘ f : A ⇨ B₁

-- p : B₁ p.⇨ C₁

-- infixr 7 _⊗_
-- _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D
-- f ⊗ g = {!!}

-- infixr 7 _△_
-- _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
-- f △ g = (f ⊗ g) ∘ dup



route : A r.⇨ B → A ⇨ B
route r.id  = id
route r.dup = netIn (idˢ ∙ idˢ)
route r.exl = netIn (val input∈ (left here))
route r.exr = netIn (val input∈ (right here))
route r.!   = netIn tt

-- prim : A p.⇨ B → A ⇨ B
-- prim p = netIn {!!}

-- compile : A c.⇨ B → A ⇨ B
-- compile (c.route r) = route r
-- compile (c.prim p)  = {!!}
-- compile (g c.∘ f)   = {!!}
-- compile (f c.⊗ g)   = {!!}
