-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module SymbolicB where

open import Data.Unit
open import Data.Bool
open import Data.Product hiding (zip)
  renaming (map to map×; assocˡ to assocˡ→; assocʳ to assocʳ→; swap to swap×)
open import Function using () renaming (id to id→; _∘_ to _∘→_)
open import Relation.Binary.PropositionalEquality

private
  variable
    A B C D σ τ : Set

-- Combinational primitives
data Prim : {A B : Set} → (A → B) → Set₁ where
  ∧⇀   : Prim (uncurry _∧_)
  ∨⇀   : Prim (uncurry _∨_)
  xor⇀ : Prim (uncurry _xor_)
  not⇀ : Prim not
  dup⇀ : Prim {A} {A × A} (λ a → a , a)
  exl⇀ : Prim {A × B} {A} proj₁
  exr⇀ : Prim {A × B} {B} proj₂
  id⇀  : Prim {A} {A} id→

-- TODO: replace suffix "⇀" with "ᶜ"

⟦_⟧⇀ : ∀ {f : A → B} → Prim f → A → B
⟦_⟧⇀ {f = f} _ = f

infixr 7 _⊗→_
_⊗→_ : (A → C) → (B → D) → (A × B → C × D)
(f ⊗→ g) (a , b) = f a , g b

infixr 7 _▵→_
_▵→_ : (A → C) → (A → D) → (A → C × D)
(f ▵→ g) = λ a → f a , g a

-- TODO: make a module with simply typed, level-monomorphic versions of these
-- operations. Import as "→".

-- Combinational circuits
data Comb : ∀ {A B : Set} → (A → B) → Set₁ where
  prim : ∀ {f : A → B} (p : Prim f) → Comb f
  _∘↠_ : ∀ {f : A → B} {g : B → C} → Comb g → Comb f → Comb (g ∘→ f)
  _⊗↠_ : ∀ {f : A → C} {g : B → D} → Comb f → Comb g → Comb (f ⊗→ g)

infixr 7 _⊗↠_
infixr 9 _∘↠_

-- TODO: replace suffix "↠" with "ᶜ"

⟦_⟧↠ : ∀ {f : A → B} → Comb f → A → B
⟦_⟧↠ {f = f} _ = f

-- TODO: Prove the cartesian category laws for _↠_.

∧↠ : Comb (uncurry _∧_)
∧↠ = prim ∧⇀

∨↠ : Comb (uncurry _∨_)
∨↠ = prim ∨⇀

xor↠ : Comb (uncurry _xor_)
xor↠ = prim xor⇀

not↠ : Comb not
not↠ = prim not⇀

dup↠ : Comb {A} {A × A} (λ a → a , a)
dup↠ = prim dup⇀

exl↠ : Comb {A × B} {A} proj₁
exl↠ = prim exl⇀

exr↠ : Comb {A × B} {B} proj₂
exr↠ = prim exr⇀

id↠  : Comb {A} {A} id→
id↠ = prim id⇀

-- Agsy filled in all of the definitions above.

-- Cartesian-categorical operations.

infixr 7 _▵↠_
_▵↠_ : ∀ {f : A → C} {g : A → D} → Comb f → Comb g → Comb (f ▵→ g)
f ▵↠ g = (f ⊗↠ g) ∘↠ dup↠

first↠ : ∀ {f : A → C} → Comb f → Comb {A × B} {C × B} (map₁ f)
first↠ f = f ⊗↠ id↠

second↠ : ∀ {g : B → D} → Comb g → Comb {A × B} {A × D} (map₂ g)
second↠ f = id↠ ⊗↠ f

-- Some useful composite combinational circuits

assocˡ↠ : Comb {A × (B × C)} {(A × B) × C} assocˡ→
assocʳ↠ : Comb {(A × B) × C} {A × (B × C)} assocʳ→

assocˡ↠ = second↠ exl↠ ▵↠ exr↠ ∘↠ exr↠
assocʳ↠ = exl↠ ∘↠ exl↠ ▵↠ first↠ exr↠

swap↠ : Comb {A × B} {B × A} swap×
swap↠ = exr↠ ▵↠ exl↠

transpose→ : (A × B) × (C × D) → (A × C) × (B × D)
transpose→ ((a , b) , (c , d)) = (a , c) , (b , d)

transpose↠ : Comb {(A × B) × (C × D)} {(A × C) × (B × D)} transpose→
transpose↠ = (exl↠ ⊗↠ exl↠) ▵↠ (exr↠ ⊗↠ exr↠)


import Mealy as ◇

-- Synchronous state machine.
-- For composability, the state type is not visible in the type.
record Mealy {A B : Set} (m : A ◇.⇨ B) : Set₁ where
  constructor mealy
  State : Set
  State = ◇._⇨_.State m
  start : State
  start = ◇._⇨_.start m
  field
    transition : Comb (◇._⇨_.transition m)

-- TODO: maybe replace the record type with the transition Comb.

⟦_⟧ : {f : A ◇.⇨ B} (m : Mealy f) → A ◇.⇨ B
⟦_⟧ {f = f} _ = f

comb : ∀ {f : A → B} (c : Comb f) → Mealy (◇.arr f)
comb c = mealy (first↠ c)

id : Mealy {A} ◇.id
id = comb id↠

-- TODO: more comb shorthands

delay : (a₀ : A) → Mealy (◇.delay a₀)
delay _ = mealy swap↠

infixr 9 _∘_
_∘_ : {g : B ◇.⇨ C} {f : A ◇.⇨ B} → Mealy g → Mealy f → Mealy (g ◇.∘ f)
mealy g ∘ mealy f = mealy
  (swiz₂ ∘↠ second↠ g ∘↠ swiz₁ ∘↠ first↠ f ∘↠ assocˡ↠)
 where
   swiz₁ : Comb {(B × σ) × τ} {σ × (B × τ)} λ { ((b , s) , t) → s , (b , t) }
   swiz₁ = exr↠ ∘↠ exl↠ ▵↠ first↠ exl↠
   swiz₂ : Comb {σ × (C × τ)} {C × (σ × τ)} λ { (s , (c , t)) → c , (s , t) }
   swiz₂ = exl↠ ∘↠ exr↠ ▵↠ second↠ exr↠

infixr 7 _⊗_
_⊗_ : {f : A ◇.⇨ C} {g : B ◇.⇨ D} → Mealy f → Mealy g → Mealy (f ◇.⊗ g)
mealy f ⊗ mealy g = mealy (transpose↠ ∘↠ (f ⊗↠ g) ∘↠ transpose↠)

infixr 7 _▵_
_▵_ : {f : A ◇.⇨ C} {g : A ◇.⇨ D} → Mealy f → Mealy g → Mealy (f ◇.▵ g)
f ▵ g = (f ⊗ g) ∘ comb dup↠

-- TODO: consider making categorical operations (most of the functionality in
-- this module) be methods of a common typeclass, so that (a) we can state and
-- prove laws conveniently, and (b) we needn't use clumsy names.

-- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
-- parametrized by denotation.

-- TODO: Cocartesian.

-- TODO: replicate compiling-to-categories using Agda reflection, and use to
-- make definitions like `_∘_` and `_⊗_` above read like their counterparts in
-- the Mealy module.
