-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

-- Relative to Symbolic.ExtrinsicTy, replace the inductive routing type with a
-- reverse TyIx mapping.

module Symbolic.ExtrinsicTyB where

import Data.Bool as Bool
open import Data.String using (String)

open import Ty

import Misc as F

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

  ⟦_⟧ : A ⇨ B → A →ᵗ B
  ⟦_⟧ = swizzle

  ⟦_⟧′ : A ⇨ B → ∀ {X} → TyF X A → TyF X B
  ⟦_⟧′ = swizzle′

  id : A ⇨ A
  id = F.id

  infixr 9 _∘_
  _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
  g ∘ f = f F.∘ g

  infixr 7 _⊗_
  _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D
  (f ⊗ g) (left  c) = left  (f c)
  (f ⊗ g) (right d) = right (g d)

  first : A ⇨ C → A × B ⇨ C × B
  first f = f ⊗ id

  second : B ⇨ D → A × B ⇨ A × D
  second g = id ⊗ g

  exl : A × B ⇨ A
  exl = left

  exr : A × B ⇨ B
  exr = right

  dup : A ⇨ A × A
  dup (left  a) = a
  dup (right a) = a

  infixr 7 _△_
  _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
  f △ g = (f ⊗ g) ∘ dup

  swap : A × B ⇨ B × A
  swap = exr △ exl

  assocˡ : A × (B × C) ⇨ (A × B) × C
  assocʳ : (A × B) × C ⇨ A × (B × C)

  assocˡ = second exl △ exr ∘ exr
  assocʳ = exl ∘ exl △ first exr

  transpose : (A × B) × (C × D) ⇨ (A × C) × (B × D)
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)

  ! : A ⇨ ⊤
  ! ()

  -- Elimination half of unitor isomorphisms
  unitorᵉˡ : ⊤ × A ⇨ A
  unitorᵉˡ = right

  unitorᵉʳ : A × ⊤ ⇨ A
  unitorᵉʳ = left

  -- Introduction half of unitor isomorphisms
  unitorⁱˡ : A ⇨ ⊤ × A
  unitorⁱˡ (left ())
  unitorⁱˡ (right y) = y

  unitorⁱʳ : A ⇨ A × ⊤
  unitorⁱʳ (left y) = y
  unitorⁱʳ (right ())


-- Combinational primitives
module p where

  infix 1 _⇨_
  data _⇨_ : Ty → Ty → Set where
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    not : Bool ⇨ Bool
    const : ⟦ A ⟧ᵗ → ⊤ ⇨ A

  ⟦_⟧ : A ⇨ B → A →ᵗ B
  ⟦ ∧ ⟧       = uncurry Bool._∧_
  ⟦ ∨ ⟧       = uncurry Bool._∨_
  ⟦ xor ⟧     = uncurry Bool._xor_
  ⟦ not ⟧     = Bool.not
  ⟦ const a ⟧ = F.const a

  show : A ⇨ B → String
  show ∧         = "∧"
  show ∨         = "∨"
  show xor       = "xor"
  show not       = "not"
  show (const a) = showTy a


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

  ⟦_⟧ : A ⇨ B → A →ᵗ B
  ⟦ route f ⟧ = r.⟦ f ⟧
  ⟦ prim  f ⟧ = p.⟦ f ⟧
  ⟦  g ∘ f  ⟧ = ⟦ g ⟧ F.∘ ⟦ f ⟧
  ⟦  f ⊗ g  ⟧ = ⟦ f ⟧ F.⊗ ⟦ g ⟧

  -- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
  -- parametrized by denotation.

  id : A ⇨ A
  dup : A ⇨ A × A
  exl : A × B ⇨ A
  exr : A × B ⇨ B
  !   : A ⇨ ⊤

  id  = route r.id
  dup = route r.dup
  exl = route r.exl
  exr = route r.exr
  !   = route r.!

  -- Cartesian-categorical operations with standard definitions:

  infixr 7 _△_
  _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
  f △ g = (f ⊗ g) ∘ dup

  first : A ⇨ C → A × B ⇨ C × B
  first f = f ⊗ id

  second : B ⇨ D → A × B ⇨ A × D
  second f = id ⊗ f

  -- Some useful composite combinational circuits

  assocˡ : A × (B × C) ⇨ (A × B) × C
  assocʳ : (A × B) × C ⇨ A × (B × C)

  assocˡ = second exl △ exr ∘ exr
  assocʳ = exl ∘ exl △ first exr

  swap : A × B ⇨ B × A
  swap = exr △ exl

  transpose : (A × B) × (C × D) ⇨ (A × C) × (B × D)
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)

  -- Agsy can synthesize most of these definitions, thought not most succinctly.
  -- Where _△_ is used, I gave it explicitly ("? △ ?").
  -- On the other hand, we can give these definitions elsewhere for *all*
  -- cartesian categories and then remove them here.

-- Synchronous state machine.
module s where

  -- For composability, the state type is not visible in the type.
  infix  0 _⇨_
  record _⇨_ (A B : Ty) : Set where
    constructor mealy
    field
      { State } : Ty
      start : ⟦ State ⟧ᵗ
      transition : A × State c.⇨ B × State

  import Mealy as m

  ⟦_⟧ : A ⇨ B → ⟦ A ⟧ᵗ m.⇨ ⟦ B ⟧ᵗ
  ⟦ mealy s₀ f ⟧ = m.mealy s₀ c.⟦ f ⟧

  comb : A c.⇨ B → A ⇨ B
  comb f = mealy tt (c.first f)

  id  : A ⇨ A
  dup : A ⇨ A × A
  exl : A × B ⇨ A
  exr : A × B ⇨ B
  !   : A ⇨ ⊤

  id  = comb c.id
  dup = comb c.dup
  exl = comb c.exl
  exr = comb c.exr
  !   = comb c.!

  prim : A p.⇨ B → A ⇨ B
  prim p = comb (c.prim p)

  ∧ ∨ xor : Bool × Bool ⇨ Bool
  not : Bool ⇨ Bool
  ∧   = prim p.∧
  ∨   = prim p.∨
  xor = prim p.xor
  not = prim p.not

  delay : ⟦ A ⟧ᵗ → A ⇨ A
  delay a₀ = mealy a₀ c.swap

  infixr 9 _∘_
  _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
  mealy t₀ g ∘ mealy s₀ f = mealy (s₀ , t₀)
    (swiz₂ c.∘ c.second g c.∘ swiz₁ c.∘ c.first f c.∘ c.assocˡ)
   where
     swiz₁ : (B × σ) × τ c.⇨ σ × (B × τ)
     swiz₁ = c.exr c.∘ c.exl c.△ c.first c.exl
     swiz₂ : σ × (C × τ) c.⇨ C × (σ × τ)
     swiz₂ = c.exl c.∘ c.exr c.△ c.second c.exr

  infixr 7 _⊗_
  _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D
  mealy s₀ f ⊗ mealy t₀ g = mealy (s₀ , t₀) (c.transpose c.∘ (f c.⊗ g) c.∘ c.transpose)

  infixr 7 _△_
  _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
  f △ g = (f ⊗ g) ∘ comb c.dup

  first : A ⇨ C → A × B ⇨ C × B
  first f = f ⊗ id

  second : B ⇨ D → A × B ⇨ A × D
  second f = id ⊗ f

  assocˡ : A × (B × C) ⇨ (A × B) × C
  assocʳ : (A × B) × C ⇨ A × (B × C)

  assocˡ = comb c.assocˡ
  assocʳ = comb c.assocʳ

  swap : A × B ⇨ B × A
  swap = exr △ exl

  transpose : (A × B) × (C × D) ⇨ (A × C) × (B × D)
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)


-- TODO: consider making categorical operations (most of the functionality in
-- this module) be methods of a common typeclass, so that (a) we can state and
-- prove laws conveniently, and (b) we needn't use clumsy names.

-- TODO: Rebuild this module in terms of semantic Mealy machines.

-- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
-- parametrized by denotation.

-- TODO: Cocartesian.

-- TODO: replicate compiling-to-categories using Agda reflection, and use to
-- make definitions like `_∘_` and `_⊗_` above read like their counterparts in
-- the Mealy module.
