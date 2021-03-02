-- Synchronous list functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module ListFun where

open import Function using (_∘′_; case_of_) renaming (id to id→)
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (zip)
  renaming (map to map×; map₁ to map×₁; map₂ to map×₂)
open import Data.Unit
open import Data.List renaming (map to mapᴸ)

private
  variable
    A B C D : Set

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = List A → List B

-- Mapping a function (combinational logic)
map : (A → B) → (A ↠ B)
map = mapᴸ

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

-- -- Conditional/choice composition
-- infixr 6 _⊕_
-- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- Puzzle: how to define _⊕_?

-- Cons (memory/register)
delay : A → (A ↠ A)
delay = _∷_


-- -- Easier?
-- [_,_] : (A ↠ C) → (B ↠ C) → (A ⊎ B ↠ C)
-- [ f , g ] [] = []
-- [ f , g ] (z ∷ zs) = {![ f , g ]′ z!} ∷ {!!}

-- foo : List (A ⊎ B) → List A × List B
-- foo [] = [] , []
-- foo (inj₁ x ∷ zs) = map×₁ (x ∷_) (foo zs)
-- foo (inj₂ y ∷ zs) = map×₂ (y ∷_) (foo zs)

open import Data.Bool

foo : List (A ⊎ B) → List Bool × List A × List B
foo [] = [] , [] , []
foo (z ∷ zs) = let fs , as , bs = foo zs in
  case z of λ
    { (inj₁ a) → false ∷ fs , a ∷ as , bs
    ; (inj₂ b) → true  ∷ fs , as , b ∷ bs }

-- foo (inj₁ a ∷ zs) = let fs , as , bs = foo zs in false ∷ fs , a ∷ as , bs
-- foo (inj₂ b ∷ zs) = let fs , as , bs = foo zs in true  ∷ fs , as , b ∷ bs
