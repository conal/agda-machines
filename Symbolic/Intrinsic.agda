-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog). This version parametrizes the symbolic
-- representations by their denotations.

module Symbolic.Intrinsic where

open import Data.Unit
import Data.Bool as Bool
open import Data.Product using (_×_; _,_; uncurry)
open import Relation.Binary.PropositionalEquality

import Misc as F  -- categorical operations on functions

private
  variable
    A B C D σ τ : Set

-- Combinational primitives
module p where

  data Prim : {A B : Set} → (A → B) → Set₁ where
    ∧   : Prim (uncurry Bool._∧_)
    ∨   : Prim (uncurry Bool._∨_)
    xor : Prim (uncurry Bool._xor_)
    not : Prim Bool.not
    dup : Prim (F.dup {A})
    exl : Prim (F.exl {A} {B})
    exr : Prim (F.exr {A} {B})
    id  : Prim (F.id {A})

open p using (Prim)

-- Combinational circuits
module c where

  data Comb : ∀ {A B : Set} → (A → B) → Set₁ where
    prim : ∀ {f : A → B} (p : Prim f) → Comb f
    _∘_ : ∀ {f : A → B} {g : B → C} → Comb g → Comb f → Comb (g F.∘ f)
    _⊗_ : ∀ {f : A → C} {g : B → D} → Comb f → Comb g → Comb (f F.⊗ g)

  infixr 7 _⊗_
  infixr 9 _∘_

  ⟦_⟧ : ∀ {f : A → B} → Comb f → A → B
  ⟦_⟧ {f = f} _ = f

  ∧   : Comb (uncurry Bool._∧_)
  ∨   : Comb (uncurry Bool._∨_)
  xor : Comb (uncurry Bool._xor_)
  not : Comb Bool.not
  dup : Comb (F.dup {A})
  exl : Comb (F.exl {A} {B})
  exr : Comb (F.exr {A} {B})
  id  : Comb (F.id {A})

  -- Definitions by Agsy:
  ∧   = prim p.∧
  ∨   = prim p.∨
  xor = prim p.xor
  not = prim p.not
  dup = prim p.dup
  exl = prim p.exl
  exr = prim p.exr
  id  = prim p.id

  -- Cartesian-categorical operations:

  infixr 7 _△_
  _△_ : ∀ {f : A → C} {g : A → D} → Comb f → Comb g → Comb (f F.△ g)
  f △ g = (f ⊗ g) ∘ dup

  first : ∀ {f : A → C} → Comb f → Comb {A × B} {C × B} (F.first f)
  first f = f ⊗ id

  second : ∀ {g : B → D} → Comb g → Comb {A × B} {A × D} (F.second g)
  second f = id ⊗ f

  assocˡ : Comb {A × (B × C)} {(A × B) × C} F.assocˡ
  assocʳ : Comb {(A × B) × C} {A × (B × C)} F.assocʳ

  assocˡ = second exl △ exr ∘ exr
  assocʳ = exl ∘ exl △ first exr

  swap : Comb {A × B} {B × A} F.swap×
  swap = exr △ exl

  transpose : Comb {(A × B) × (C × D)} {(A × C) × (B × D)} F.transpose
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)

open c using (Comb)

-- Sequential computations 
module s where

  import Mealy as m

  record Mealy (m : A m.⇨ B) : Set₁ where
    constructor mealy
    field
      transition : Comb (m._⇨_.transition m)

  ⟦_⟧ : {f : A m.⇨ B} (m : Mealy f) → A m.⇨ B
  ⟦_⟧ {f = f} _ = f

  comb : ∀ {f : A → B} (c : Comb f) → Mealy (m.arr f)
  comb c = mealy (c.first c)

  id : Mealy (m.id {A})
  id = comb c.id

  delay : (a₀ : A) → Mealy (m.delay a₀)
  delay _ = mealy c.swap

  infixr 9 _∘_
  _∘_ : {g : B m.⇨ C} {f : A m.⇨ B} → Mealy g → Mealy f → Mealy (g m.∘ f)
  mealy g ∘ mealy f =
    mealy (swiz₂ c.∘ c.second g c.∘ swiz₁ c.∘ c.first f c.∘ c.assocˡ)
   where
     swiz₁ : Comb λ ((b , s′) , t) → s′ , (b , t)
     swiz₁ = c.exr c.∘ c.exl c.△ c.first c.exl
     swiz₂ : Comb λ (s′ , (c , t′)) → c , (s′ , t′)
     swiz₂ = c.exl c.∘ c.exr c.△ c.second c.exr

  infixr 7 _⊗_
  _⊗_ : {f : A m.⇨ C} {g : B m.⇨ D} → Mealy f → Mealy g → Mealy (f m.⊗ g)
  mealy f ⊗ mealy g = mealy (c.transpose c.∘ (f c.⊗ g) c.∘ c.transpose)

  infixr 7 _△_
  _△_ : {f : A m.⇨ C} {g : A m.⇨ D} → Mealy f → Mealy g → Mealy (f m.△ g)
  f △ g = (f ⊗ g) ∘ comb c.dup
 
-- TODO: consider making categorical operations (most of the functionality in
-- this module) be methods of a common typeclass, so that (a) we can state and
-- prove laws conveniently, and (b) we needn't use clumsy names.

-- Agsy did not fare well with filling in the combinational or sequential
-- circuit definitions, but compiling-to-categories would be.

-- TODO: replicate compiling-to-categories using Agda reflection, and use to
-- make definitions like `_∘_` and `_⊗_` above read like their counterparts in
-- the Mealy module.

-- TODO: Cocartesian.

-- TODO: are the semantic functions worth keeping explicitly?
