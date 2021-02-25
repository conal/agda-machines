-- Synchronous list functions, used as semantics for machines

{-# OPTIONS --safe --without-K #-}

module ListFun where

open import Function using (id ; _∘_) public
open import Data.Product hiding (map; zip)
open import Data.Unit
open import Data.List renaming (map to mapᴸ)

private
  variable
    a b c d : Set

infix 1 _⇢_
_⇢_ : Set → Set → Set
a ⇢ b = List a → List b

-- Mapping a function (empty state)
map : (a → b) → (a ⇢ b)
map = mapᴸ

-- id and _∘_ come from Function

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (a ⇢ c) → (b ⇢ d) → (a × b ⇢ c × d)
(f ⊗ g) abs = let (as , bs) = unzip abs in zip (f as) (g bs)

-- Cons (memory/register)
delay : a → (a ⇢ a)
delay = _∷_
