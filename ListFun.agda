-- Synchronous list functions, used as semantics for machines

{-# OPTIONS --safe --without-K #-}

module ListFun where

open import Function using (id ; _∘_) public
open import Data.Product hiding (map; zip)
open import Data.Unit
open import Data.List renaming (map to mapᴸ)

private
  variable
    A B C D : Set

infix 1 _⇢_
_⇢_ : Set → Set → Set
A ⇢ B = List A → List B

-- Mapping a function (empty state)
map : (A → B) → (A ⇢ B)
map = mapᴸ

-- id and _∘_ come from Function

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (A ⇢ C) → (B ⇢ D) → (A × B ⇢ C × D)
(f ⊗ g) abs = let (as , bs) = unzip abs in zip (f as) (g bs)

-- Cons (memory/register)
delay : A → (A ⇢ A)
delay = _∷_
