-- This variation is based on a vector-like type with sized elements.
-- Replace products with vectors.

-- module Netlist where

open import Function renaming (id to id′) using (_∘′_)
open import Data.Product using (∃; _,_) renaming (_×_ to _×ᵗ_)

-- open import Data.Nat
-- open import Data.Fin using (Fin; raise; inject+) renaming (splitAt to splitAtᶠ)
-- -- TODO: trim Data.Fin imports
-- -- open import Data.Fin using (Fin)
-- import Data.Sum as ⊎
-- open ⊎ using (_⊎_)

import Misc as F
open import Ty
open import Symbolic.ExtrinsicTyB

private variable A B C D X Y Z : Ty

infixr 5 _∷_
data Vec′ (F : Ty → Ty → Set) : Ty → Set where
  [] : Vec′ F ⊤
  _∷_ : F X Y → Vec′ F X → Vec′ F (Y × X)

F : Ty → Ty → Set
F X B = ∃ λ A → (A p.⇨ B) ×ᵗ (X r.⇨ A)

Netlist : Ty → Set
Netlist = Vec′ F

-- A netlist with i outputs and result size A
Src : Ty → Ty → Set
Src X A = Netlist X ×ᵗ (X r.⇨ A)

-- The netlist category. The shape of total netlist output is static.
infix 0 _⇨_
_⇨_ : Ty → Ty → Set
A ⇨ B = ∃ λ Y → ∀ {X} → Src X A → Src (Y × X) B

route : A r.⇨ B → A ⇨ B
route r = ⊤ , λ {x} (netsᵢ , x⇨ᵣa) → netsᵢ , r r.∘ x⇨ᵣa

-- -- Now id and _∘_ are easy. What about _⊗_?

-- id : A ⇨ A
-- id = zero , id′

-- open import Relation.Binary.PropositionalEquality
-- open import Data.Nat.Properties

-- infixr 9 _∘_
-- _∘_ : B ⇨ C → A ⇨ B → A ⇨ C
-- _∘_ {C = C} (gj , g) (fj , f) =
--   gj × fj , λ {i} sₐ → subst (λ n → Src n C) (sym (×-assoc gj fj i)) (g (f sₐ))

-- first : A ⇨ C → A × B ⇨ C × B
-- first (fj , f) = fj , λ {i} (netsᵢ , ir⇒a×b) →
--  let nets_fj×i , fj×i⇨ᵣc = f {i} (netsᵢ , r.exl r.∘ ir⇒a×b) in
--    nets_fj×i , fj×i⇨ᵣc r.△ r.exr r.∘ ir⇒a×b r.∘ r.exr

-- second : B ⇨ D → A × B ⇨ A × D
-- second {B}{D}{A} g = route (r.swap {D}{A}) ∘ first g ∘ route (r.swap {A}{B})

-- -- route r.swap : A × B ⇨ B × A
-- -- first g : B × A ⇨ D × A
-- -- route r.swap : D × A ⇨ A × D

-- infixr 7 _⊗_
-- _⊗_ : A ⇨ C → B ⇨ D → A × B ⇨ C × D
-- f ⊗ g = second g ∘ first f

-- -- r.exr : fj × i r.⇨ i
-- -- ir⇒a×b : i r.⇨ A × B
-- -- r.exr : A × B r.⇨ B
-- -- 
-- -- r.exr r.∘ ir⇒a×b r.∘ r.exr : fj × i r.⇨ B
