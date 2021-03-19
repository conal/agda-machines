-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic.Extrinsic where

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
infix 1 _→ᵖ_
data _→ᵖ_ : Set → Set → Set₁ where
  ∧ᵖ ∨ᵖ xorᵖ : Bool × Bool →ᵖ Bool
  notᵖ : Bool →ᵖ Bool
  dupᵖ : A →ᵖ A × A
  exlᵖ : A × B →ᵖ A
  exrᵖ : A × B →ᵖ B
  idᵖ : A →ᵖ A

⟦_⟧ᵖ : A →ᵖ B → A → B
⟦ ∧ᵖ   ⟧ᵖ = uncurry _∧_
⟦ ∨ᵖ   ⟧ᵖ = uncurry _∨_
⟦ xorᵖ ⟧ᵖ = uncurry _xor_
⟦ notᵖ ⟧ᵖ = not
⟦ dupᵖ ⟧ᵖ = < id→ , id→ >
⟦ exlᵖ ⟧ᵖ = proj₁
⟦ exrᵖ ⟧ᵖ = proj₂
⟦ idᵖ  ⟧ᵖ = id→

infix  0 _→ᶜ_
infixr 7 _⊗ᶜ_
infixr 9 _∘ᶜ_

-- Combinational circuits
data _→ᶜ_ : Set → Set → Set₁ where
  prim : A →ᵖ B → A →ᶜ B
  _∘ᶜ_ : B →ᶜ C → A →ᶜ B → A →ᶜ C
  _⊗ᶜ_ : A →ᶜ C → B →ᶜ D → A × B →ᶜ C × D

⟦_⟧ᶜ : A →ᶜ B → A → B
⟦ prim f ⟧ᶜ = ⟦ f ⟧ᵖ
⟦ g ∘ᶜ f ⟧ᶜ = ⟦ g ⟧ᶜ ∘→ ⟦ f ⟧ᶜ
⟦ f ⊗ᶜ g ⟧ᶜ = map× ⟦ f ⟧ᶜ ⟦ g ⟧ᶜ

-- TODO: Try parametrizing _ᵖ_ and _ᶜ_ by their denotation.

-- TODO: Prove the cartesian category laws for _ᶜ_. Probably easier if
-- parametrized by denotation.

-- Lift primitives to combinational circuits
∧ᶜ ∨ᶜ xorᶜ : Bool × Bool →ᶜ Bool
¬ᶜ : Bool →ᶜ Bool
dupᶜ : A →ᶜ A × A
exlᶜ : A × B →ᶜ A
exrᶜ : A × B →ᶜ B
idᶜ : A →ᶜ A

∧ᶜ   = prim ∧ᵖ
∨ᶜ   = prim ∨ᵖ
xorᶜ = prim xorᵖ
¬ᶜ   = prim notᵖ
dupᶜ = prim dupᵖ
exlᶜ = prim exlᵖ
exrᶜ = prim exrᵖ
idᶜ  = prim idᵖ

-- Cartesian-categorical operations.

infixr 7 _▵ᶜ_
_▵ᶜ_ : A →ᶜ C → A →ᶜ D → A →ᶜ C × D
f ▵ᶜ g = (f ⊗ᶜ g) ∘ᶜ dupᶜ

firstᶜ : A →ᶜ C → A × B →ᶜ C × B
firstᶜ f = f ⊗ᶜ prim idᵖ
--- firstᶜ f = f ⊗ᶜ idᶜ

secondᶜ : B →ᶜ D → A × B →ᶜ A × D
secondᶜ f = idᶜ ⊗ᶜ f

-- Some useful composite combinational circuits

assocˡᶜ : A × (B × C) →ᶜ (A × B) × C
assocʳᶜ : (A × B) × C →ᶜ A × (B × C)

assocˡᶜ = secondᶜ exlᶜ ▵ᶜ exrᶜ ∘ᶜ exrᶜ
assocʳᶜ = exlᶜ ∘ᶜ exlᶜ ▵ᶜ firstᶜ exrᶜ

swapᶜ : A × B →ᶜ B × A
swapᶜ = exrᶜ ▵ᶜ exlᶜ

transposeᶜ : (A × B) × (C × D) →ᶜ (A × C) × (B × D)
transposeᶜ = (exlᶜ ⊗ᶜ exlᶜ) ▵ᶜ (exrᶜ ⊗ᶜ exrᶜ)

-- Agsy can synthesize most of these definitions, thought not most succinctly.
-- Where _▵ᶜ_ is used, I gave it explicitly ("? ▵ᶜ ?").

-- Synchronous state machine.
-- For composability, the state type is not visible in the type.
infix  0 _→ˢ_
record _→ˢ_ (A B : Set) : Set₁ where
  constructor mealy
  field
    { State } : Set
    start : State
    transition : A × State →ᶜ B × State

import Mealy as ◇

⟦_⟧ˢ : A →ˢ B → A ◇.→ˢ B
⟦ mealy s₀ f ⟧ˢ = ◇.mealy s₀ ⟦ f ⟧ᶜ

comb : A →ᶜ B → A →ˢ B
comb f = mealy tt (firstᶜ f)

-- comb f = mealy tt {!!}

-- comb f = {!!}   -- weird, correct result

idˢ : A →ˢ A
idˢ = comb idᶜ

-- id = mealy tt idᶜ

-- TODO: more comb shorthands

delayˢ : A → A →ˢ A
delayˢ a₀ = mealy a₀ swapᶜ

infixr 9 _∘ˢ_
_∘ˢ_ : B →ˢ C → A →ˢ B → A →ˢ C
mealy t₀ g ∘ˢ mealy s₀ f = mealy (s₀ , t₀)
  (swiz₂ ∘ᶜ secondᶜ g ∘ᶜ swiz₁ ∘ᶜ firstᶜ f ∘ᶜ assocˡᶜ)
 where
   swiz₁ : (B × σ) × τ →ᶜ σ × (B × τ)
   swiz₁ = exrᶜ ∘ᶜ exlᶜ ▵ᶜ firstᶜ exlᶜ
   swiz₂ : σ × (C × τ) →ᶜ C × (σ × τ)
   swiz₂ = exlᶜ ∘ᶜ exrᶜ ▵ᶜ secondᶜ exrᶜ

infixr 7 _⊗ˢ_
_⊗ˢ_ : A →ˢ C → B →ˢ D → A × B →ˢ C × D
mealy s₀ f ⊗ˢ mealy t₀ g = mealy (s₀ , t₀) (transposeᶜ ∘ᶜ (f ⊗ᶜ g) ∘ᶜ transposeᶜ)

infixr 7 _▵ˢ_
_▵ˢ_ : A →ˢ C → A →ˢ D → A →ˢ C × D
f ▵ˢ g = (f ⊗ˢ g) ∘ˢ comb dupᶜ

-- TODO: consider making categorical operations (most of the functionality in
-- this module) be methods of a common typeclass, so that (a) we can state and
-- prove laws conveniently, and (b) we needn't use clumsy names.

-- TODO: Rebuild this module in terms of semantic Mealy machines.

-- TODO: Prove the cartesian category laws for _→ˢ_. Probably easier if
-- parametrized by denotation.

-- TODO: Cocartesian.

-- TODO: replicate compiling-to-categories using Agda reflection, and use to
-- make definitions like `_∘_` and `_⊗_` above read like their counterparts in
-- the Mealy module.
