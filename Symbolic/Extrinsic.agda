-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic.Extrinsic where

open import Data.Unit
import Data.Bool as Bool
open Bool using (Bool)
open import Data.Product using (_×_; _,_; uncurry)
open import Relation.Binary.PropositionalEquality

import Misc as F

private
  variable
    A B C D σ τ : Set

-- Routing
module r where

  infix 1 _⇨_
  data _⇨_ : Set → Set → Set₁ where
    id  : A ⇨ A
    dup : A ⇨ A × A
    exl : A × B ⇨ A
    exr : A × B ⇨ B
    !   : A ⇨ ⊤

  ⟦_⟧ : A ⇨ B → A → B
  ⟦ id  ⟧ = F.id
  ⟦ dup ⟧ = F.dup
  ⟦ exl ⟧ = F.exl
  ⟦ exr ⟧ = F.exr
  ⟦ ! ⟧   = F.!

-- Combinational primitives
module p where

  infix 1 _⇨_
  data _⇨_ : Set → Set → Set₁ where
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    not : Bool ⇨ Bool

  ⟦_⟧ : A ⇨ B → A → B
  ⟦ ∧   ⟧ = uncurry Bool._∧_
  ⟦ ∨   ⟧ = uncurry Bool._∨_
  ⟦ xor ⟧ = uncurry Bool._xor_
  ⟦ not ⟧ = Bool.not

-- Combinational circuits
module c where

  infix  0 _⇨_
  infixr 7 _⊗_
  infixr 9 _∘_

  data _⇨_ : Set → Set → Set₁ where
    route : A r.⇨ B → A ⇨ B
    prim : A p.⇨ B → A ⇨ B
    _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
    _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D

  ⟦_⟧ : A ⇨ B → A → B
  ⟦ route f ⟧ = r.⟦ f ⟧
  ⟦ prim f ⟧ = p.⟦ f ⟧
  ⟦ g ∘ f ⟧ = ⟦ g ⟧ F.∘ ⟦ f ⟧
  ⟦ f ⊗ g ⟧ = ⟦ f ⟧ F.⊗ ⟦ g ⟧

  -- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
  -- parametrized by denotation.
  -- Lift routes primitives to combinational circuits
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

  -- Cartesian-categorical operations with standard definitions. Agsy can
  -- synthesize most of these definitions, thought not most succinctly. Where
  -- _△_ is used, I gave it explicitly ("? △ ?"). On the other hand, we can give
  -- these definitions elsewhere for *all* cartesian categories and then remove
  -- them here.

  infixr 7 _△_
  _△_ : A ⇨ C → A ⇨ D → A ⇨ C × D
  f △ g = (f ⊗ g) ∘ dup

  first : A ⇨ C → A × B ⇨ C × B
  first f = f ⊗ id

  second : B ⇨ D → A × B ⇨ A × D
  second f = id ⊗ f

  assocˡ : A × (B × C) ⇨ (A × B) × C
  assocʳ : (A × B) × C ⇨ A × (B × C)

  assocˡ = second exl △ exr ∘ exr
  assocʳ = exl ∘ exl △ first exr

  swap : A × B ⇨ B × A
  swap = exr △ exl

  transpose : (A × B) × (C × D) ⇨ (A × C) × (B × D)
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)


-- Synchronous state machine.
module s where

  -- For composability, the state type is not visible in the type.
  infix  0 _⇨_
  record _⇨_ (A B : Set) : Set₁ where
    constructor mealy
    field
      { State } : Set
      start : State
      transition : A × State c.⇨ B × State

  import Mealy as m

  ⟦_⟧ : A ⇨ B → A m.⇨ B
  ⟦ mealy s₀ f ⟧ = m.mealy s₀ c.⟦ f ⟧

  comb : A c.⇨ B → A ⇨ B
  comb f = mealy tt (c.first f)

  id : A ⇨ A
  id = comb c.id

  delay : A → A ⇨ A
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
