-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic where

open import Data.Unit
open import Data.Bool
open import Data.Product hiding (zip; assocˡ; assocʳ)
  renaming (map to map×)
open import Function using () renaming (id to id→; _∘_ to _∘→_)
open import Relation.Binary.PropositionalEquality

private
  variable
    A B C D σ τ : Set

-- Combinational primitives
infix 1 _⇀_
data _⇀_ : Set → Set → Set₁ where
  ∧⇀ ∨⇀ xor⇀ : Bool × Bool ⇀ Bool
  ¬⇀ : Bool ⇀ Bool
  dup⇀ : A ⇀ A × A
  exl⇀ : A × B ⇀ A
  exr⇀ : A × B ⇀ B
  id⇀ : A ⇀ A

⟦_⟧⇀ : A ⇀ B → A → B
⟦ ∧⇀   ⟧⇀ = uncurry _∧_
⟦ ∨⇀   ⟧⇀ = uncurry _∨_
⟦ xor⇀ ⟧⇀ = uncurry _xor_
⟦ ¬⇀   ⟧⇀ = not
⟦ dup⇀ ⟧⇀ = < id→ , id→ >
⟦ exl⇀ ⟧⇀ = proj₁
⟦ exr⇀ ⟧⇀ = proj₂
⟦ id⇀  ⟧⇀ = id→

infix  1 _↠_
infixr 7 _⊗↠_
infixr 9 _∘↠_

-- Combinational circuits
data _↠_ : Set → Set → Set₁ where
  prim : A ⇀ B → A ↠ B
  _∘↠_ : B ↠ C → A ↠ B → A ↠ C
  _⊗↠_ : A ↠ C → B ↠ D → A × B ↠ C × D

⟦_⟧↠ : A ↠ B → A → B
⟦ prim f ⟧↠ = ⟦ f ⟧⇀
⟦ g ∘↠ f ⟧↠ = ⟦ g ⟧↠ ∘→ ⟦ f ⟧↠
⟦ f ⊗↠ g ⟧↠ = map× ⟦ f ⟧↠ ⟦ g ⟧↠

-- TODO: Try parametrizing _⇀_ and _↠_ by their denotation.

-- TODO: Prove the cartesian category laws for _↠_. Probably easier if
-- parametrized by denotation.

-- Lift primitives to combinational circuits
∧↠ ∨↠ xor↠ : Bool × Bool ↠ Bool
¬↠ : Bool ↠ Bool
dup↠ : A ↠ A × A
exl↠ : A × B ↠ A
exr↠ : A × B ↠ B
id↠ : A ↠ A

∧↠   = prim ∧⇀
∨↠   = prim ∨⇀
xor↠ = prim xor⇀
¬↠   = prim ¬⇀
dup↠ = prim dup⇀
exl↠ = prim exl⇀
exr↠ = prim exr⇀
id↠  = prim id⇀

-- Cartesian-categorical operations.

infixr 7 _▵↠_
_▵↠_ : A ↠ C → A ↠ D → A ↠ C × D
f ▵↠ g = (f ⊗↠ g) ∘↠ dup↠

first↠ : A ↠ C → A × B ↠ C × B
first↠ f = f ⊗↠ id↠

second↠ : B ↠ D → A × B ↠ A × D
second↠ f = id↠ ⊗↠ f

-- Some useful composite combinational circuits

assocˡ↠ : A × (B × C) ↠ (A × B) × C
assocʳ↠ : (A × B) × C ↠ A × (B × C)

assocˡ↠ = second↠ exl↠ ▵↠ exr↠ ∘↠ exr↠
assocʳ↠ = exl↠ ∘↠ exl↠ ▵↠ first↠ exr↠

swap↠ : A × B ↠ B × A
swap↠ = exr↠ ▵↠ exl↠

transpose↠ : (A × B) × (C × D) ↠ (A × C) × (B × D)
transpose↠ = (exl↠ ⊗↠ exl↠) ▵↠ (exr↠ ⊗↠ exr↠)

-- Agsy can synthesize most of these definitions, thought not most succinctly.
-- Where _▵↠_ is used, I gave it explicitly ("? ▵↠ ?").

-- Synchronous state machine.
-- For composability, the state type is not visible in the type.
infix  1 _⇨_
record _⇨_ (A B : Set) : Set₁ where
  constructor mealy
  field
    { State } : Set
    start : State
    transition : A × State ↠ B × State

import Mealy as ◇

⟦_⟧ : A ⇨ B → A ◇.⇨ B
⟦ mealy s₀ f ⟧ = ◇.mealy s₀ ⟦ f ⟧↠

comb : A ↠ B → A ⇨ B
comb f = mealy tt (f ⊗↠ id↠)

-- comb f = mealy tt {!!}

-- comb f = {!!}   -- weird, correct result

id : A ⇨ A
id = comb id↠

-- id = mealy tt id↠

-- TODO: more comb shorthands

delay : A → A ⇨ A
delay a₀ = mealy a₀ swap↠

infixr 9 _∘_
_∘_ : B ⇨ C → A ⇨ B → A ⇨ C
mealy t₀ g ∘ mealy s₀ f = mealy (s₀ , t₀)
  (swiz₂ ∘↠ second↠ g ∘↠ swiz₁ ∘↠ first↠ f ∘↠ assocˡ↠)
 where
   swiz₁ : (B × σ) × τ ↠ σ × (B × τ)
   swiz₁ = exr↠ ∘↠ exl↠ ▵↠ first↠ exl↠
   swiz₂ : σ × (C × τ) ↠ C × (σ × τ)
   swiz₂ = exl↠ ∘↠ exr↠ ▵↠ second↠ exr↠

infixr 7 _⊗_
_⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D
mealy s₀ f ⊗ mealy t₀ g = mealy (s₀ , t₀) (transpose↠ ∘↠ (f ⊗↠ g) ∘↠ transpose↠)

infixr 7 _▵_
_▵_ : A ⇨ C → A ⇨ D → A ⇨ C × D
f ▵ g = (f ⊗ g) ∘ comb dup↠

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
