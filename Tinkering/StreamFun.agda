-- Synchronous stream functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K --copatterns #-}

{-# OPTIONS --guardedness #-}

module StreamFun where

open import Function using (_∘′_; case_of_) renaming (id to id→)
open import Data.Product hiding (zip) renaming (map to map×)
open import Data.Unit

private
  variable
    A B C D : Set

infixr 5 _∷_
record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

open Stream

zip : Stream A → Stream B → Stream (A × B)
head (zip as bs) = head as , head bs
tail (zip as bs) = zip (tail as) (tail bs)

infix 1 _↠_
_↠_ : Set → Set → Set
A ↠ B = Stream A → Stream B

const : A → Stream A
head (const a) = a
tail (const a) = const a

-- Mapping a function (combinational logic)
map : (A → B) → (A ↠ B)
head (map f as) = f (head as)
tail (map f as) = map f (tail as)

-- Seems a shame to make two passes, but I couldn't figure out how to satisfy
-- the termination checker in a single-pass definition.
unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

id : A ↠ A
id = id→

infixr 9 _∘_
_∘_ : (B ↠ C) → (A ↠ B) → (A ↠ C)
_∘_ = _∘′_

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (A ↠ C) → (B ↠ D) → (A × B ↠ C × D)
f ⊗ g = uncurry zip ∘′ map× f g ∘′ unzip
-- (f ⊗ g) ps = let as , bs = unzip ps in zip (f as) (g bs)

-- -- -- Conditional/choice composition
-- -- infixr 6 _⊕_
-- -- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- -- How to define _⊕_?

-- open import Data.Sum
-- open import Data.Bool

-- unzip+ : Stream (A ⊎ B) → Stream Bool × Stream A × Stream B
-- unzip+ zs = {!!} , {!!} , {!!}

-- Cons (memory/register)
delay : A → (A ↠ A)
delay = _∷_
