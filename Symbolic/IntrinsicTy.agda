-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog). This version parametrizes the symbolic
-- representations by their denotations.

module Symbolic.IntrinsicTy where

import Data.Bool as Bool

open import Ty
import Misc as F  -- categorical operations on functions

private
  variable
    A B C D σ τ : Ty

-- Routing
module r where

  data Route : {A B : Ty} → (A →ᵗ B) → Set₁ where
    id  : Route {A} F.id
    dup : Route {A} F.dup
    exl : Route {A × B} F.exl
    exr : Route {A × B} F.exr
    !   : Route {A} F.!

open r using (Route)

-- Combinational primitives
module p where

  data Prim : {A B : Ty} → (A →ᵗ B) → Set₁ where
    ∧   : Prim (uncurry Bool._∧_)
    ∨   : Prim (uncurry Bool._∨_)
    xor : Prim (uncurry Bool._xor_)
    not : Prim Bool.not

open p using (Prim)

-- Combinational circuits
module c where

  data Comb : ∀ {A B : Ty} → (A →ᵗ B) → Set₁ where
    route : ∀ {f} (r : Route {A}{B} f) → Comb f
    prim : ∀ {f} (p : Prim {A}{B} f) → Comb f
    _∘_ : ∀ {f}{g} → Comb {B}{C} g → Comb {A}{B} f → Comb (g F.∘ f)
    _⊗_ : ∀ {f}{g} → Comb {A}{C} f → Comb {B}{D} g → Comb (f F.⊗ g)

  -- Alternatively,
    -- prim : ∀ {f : A →ᵗ B} (p : Prim f) → Comb f
    -- _∘_ : ∀ {f : A →ᵗ B} {g : B →ᵗ C} → Comb g → Comb f → Comb (g F.∘ f)
    -- _⊗_ : ∀ {f : A →ᵗ C} {g : B →ᵗ D} → Comb f → Comb g → Comb (f F.⊗ g)

  infixr 7 _⊗_
  infixr 9 _∘_

  ⟦_⟧ : ∀ {f : A →ᵗ B} → Comb f → A →ᵗ B
  ⟦_⟧ {f = f} _ = f

  id  : Comb {A} F.id
  dup : Comb {A} F.dup
  exl : Comb {A × B} F.exl
  exr : Comb {A × B} F.exr
  !   : Comb {A} F.!

  ∧   : Comb (uncurry Bool._∧_)
  ∨   : Comb (uncurry Bool._∨_)
  xor : Comb (uncurry Bool._xor_)
  not : Comb Bool.not

  -- Definitions by Agsy:
  id  = route r.id
  dup = route r.dup
  exl = route r.exl
  exr = route r.exr
  !   = route r.!
  ∧   = prim  p.∧
  ∨   = prim  p.∨
  xor = prim  p.xor
  not = prim  p.not

  -- Cartesian-categorical operations:

  infixr 7 _△_
  _△_ : ∀ {f : A →ᵗ C} {g : A →ᵗ D} → Comb f → Comb g → Comb (f F.△ g)
  f △ g = (f ⊗ g) ∘ dup

  first : ∀ {f : A →ᵗ C} → Comb f → Comb {A × B} {C × B} (F.first f)
  first f = f ⊗ id

  second : ∀ {g : B →ᵗ D} → Comb g → Comb {A × B} {A × D} (F.second g)
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

  import MealyTy as m

  record Mealy (m : A m.⇨ B) : Set₁ where
    constructor mealy
    field
      transition : Comb (m._⇨_.transition m)

  ⟦_⟧ : {f : A m.⇨ B} (m : Mealy f) → A m.⇨ B
  ⟦_⟧ {f = f} _ = f

  comb : ∀ {f : A →ᵗ B} (c : Comb f) → Mealy (m.arr f)
  comb c = mealy (c.first c)

  id : Mealy (m.id {A})
  id = comb c.id

  delay : { a₀ : ⟦ A ⟧ᵗ} → Mealy (m.delay a₀)
  delay = mealy c.swap
  -- TODO: should a₀ be an implicit or explicit parameter?

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

-- TODO: are the explicit semantic functions worth keeping?
