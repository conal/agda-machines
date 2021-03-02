-- Synchronous list functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module ListFun where

open import Function using (_∘′_) renaming (id to id→)
open import Data.Product hiding (zip) renaming (map to map×)
open import Data.Unit
open import Data.List renaming (map to mapᴸ)

private
  variable
    A B C D : Set

infix 1 _↠_
_↠_ : Set → Set → Set
A ↠ B = List A → List B

-- Mapping a function
map : (A → B) → (A ↠ B)
map = mapᴸ

id : A ↠ A
id = id→

infixr 9 _∘_
_∘_ : (B ↠ C) → (A ↠ B) → (A ↠ C)
_∘_ = _∘′_

-- id and _∘_ come from Function (re-exported)

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (A ↠ C) → (B ↠ D) → (A × B ↠ C × D)
f ⊗ g = uncurry zip ∘′ map× f g ∘′ unzip
-- (f ⊗ g) ps = let as , bs = unzip ps in zip (f as) (g bs)

-- -- Conditional/choice composition
-- infixr 6 _⊕_
-- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- How to define _⊕_?

-- Cons (memory/register)
delay : A → (A ↠ A)
delay = _∷_
