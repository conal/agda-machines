-- Length-preserving vector functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecFun where

open import Function using (_∘′_; case_of_; const) renaming (id to id→)
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (zip)
  renaming (map to map×; map₁ to map×₁; map₂ to map×₂)
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≗_)

private
  variable
    A B C D : Set

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = ∀ {n} → Vec A n → Vec B n

infix 4 _≗_
_≗_ : (f g : A ↠ B) → Set _
f ≗ g = ∀ {n} (as : Vec _ n) → f as ≡ g as

-- Mapping a function (combinational logic)
arr : (A → B) → (A ↠ B)
arr f = map f

id : A ↠ A
id = id→

infixr 9 _∘_
_∘_ : (B ↠ C) → (A ↠ B) → (A ↠ C)
g ∘ f = g ∘′ f

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (A ↠ C) → (B ↠ D) → (A × B ↠ C × D)
f ⊗ g = uncurry zip ∘′ map× f g ∘′ unzip
-- (f ⊗ g) ps = let as , bs = unzip ps in zip (f as) (g bs)

-- -- Conditional/choice composition
-- infixr 6 _⊕_
-- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- Puzzle: how to define _⊕_?

-- Cons (memory/register)
delay : A → (A ↠ A)
delay a as = init (a ∷ as)

open import Relation.Binary.PropositionalEquality

init∷ : ∀ {a : A}{n} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
init∷ as with initLast as
... | as′ , l , refl = refl

-- TODO: Package init∷ into an agda-stdlib PR.

∷delay : ∀ {a₀ a : A} {n} {as : Vec A n} → a₀ ∷ delay a as ≡ delay a₀ (a ∷ as)
∷delay {a = a}{as = as} = sym (init∷ (a ∷ as))
