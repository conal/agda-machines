-- Synchronous list functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecNFun where

open import Function using (_∘′_; case_of_; const) renaming (id to id→)
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (zip)
  renaming (map to map×; map₁ to map×₁; map₂ to map×₂)
open import Data.Unit
open import Data.Nat
open import Data.Vec renaming (map to mapv)

private
  variable
    A B C D : Set
    m n p : ℕ

VF : ℕ → Set → Set → Set
VF n A B = Vec A n → Vec B n

-- Mapping a function (combinational logic)
map : (A → B) → VF n A B
map f = mapv f

id : VF n A A
id = id→

infixr 9 _∘_
_∘_ : VF n B C → VF n A B → VF n A C
g ∘ f = g ∘′ f

-- Parallel composition
infixr 10 _⊗_
_⊗_ : VF n A C → VF n B D → VF n (A × B) (C × D)
f ⊗ g = uncurry zip ∘′ map× f g ∘′ unzip
-- (f ⊗ g) ps = let as , bs = unzip ps in zip (f as) (g bs)

-- -- -- Conditional/choice composition
-- -- infixr 6 _⊕_
-- -- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- -- Puzzle: how to define _⊕_?

-- Cons (memory/register)
delay : A → VF n A A
delay a as = init (a ∷ as)

open import Relation.Binary.PropositionalEquality

init∷ : ∀ {a : A} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
init∷ as with initLast as
... | as′ , l , refl = refl

-- TODO: Put init∷ into an agda-stdlib PR.

∷delay : ∀ {a₀ a : A} {as : Vec A n} → a₀ ∷ delay a as ≡ delay a₀ (a ∷ as)
∷delay {a₀ = a₀}{a}{as} = sym (init∷ (a ∷ as))
