-- Synchronous list functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecFun where

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

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = ∀ {n} → Vec A n → Vec B n

-- Mapping a function (combinational logic)
map : (A → B) → (A ↠ B)
map f = mapv f

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


-- -- -- Easier?
-- -- [_,_] : (A ↠ C) → (B ↠ C) → (A ⊎ B ↠ C)
-- -- [ f , g ] [] = []
-- -- [ f , g ] (z ∷ zs) = {![ f , g ]′ z!} ∷ {!!}

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

foo : Vec (A ⊎ B) p → ∃₂ λ m n → (p ≡ m + n) × Vec A m × Vec B n
foo [] = zero , zero , refl , [] , []
foo (inj₁ a ∷ zs) with foo zs
... | m , n , refl , as , bs = suc m , n , refl , a ∷ as , bs
foo (inj₂ b ∷ zs) with foo zs
... | m , n , refl , as , bs = m , suc n , sym (+-suc m n) , as , b ∷ bs

open import Data.Bool

bar : Vec (A ⊎ B) p → Vec Bool p
bar = mapv [ const false , const true ]′

baz : Vec (A ⊎ B) p → Vec Bool p × ∃₂ λ m n → (p ≡ m + n) × Vec A m × Vec B n
baz [] = [] , zero , zero , refl , [] , []
baz (inj₁ a ∷ zs) with baz zs
... | cs , m , n , refl , as , bs = false ∷ cs , suc m , n , refl , a ∷ as , bs
baz (inj₂ b ∷ zs) with baz zs
... | cs , m , n , refl , as , bs = true ∷ cs , m , suc n , sym (+-suc m n) , as , b ∷ bs

baz′ : Vec (A ⊎ B) p → Vec Bool p × ∃₂ λ m n → (p ≡ m + n) × Vec A m × Vec B n
baz′ = < bar , foo >

-- restore : Vec Bool p → (∃₂ λ m n → (p ≡ m + n) × Vec A m × Vec B n) → Vec (A ⊎ B) p
-- restore [] (zero , zero , refl , [] , []) = []
-- restore (false ∷ cs) (m , n , eq , as , bs) = {!!}
-- restore (true  ∷ cs) (m , n , eq , as , bs) = {!!}

-- We'll need more e.g., that the number of falses and trues are m and n
-- respectively. 

-- restore {zero} [] (zero , zero , refl , [] , []) = []
-- restore {suc p} (x ∷ cs) (m , n , eq , as , bs) = {!!}

-- open import Data.Bool

-- foo : List (A ⊎ B) → List Bool × List A × List B
-- foo [] = [] , [] , []
-- foo (z ∷ zs) = let fs , as , bs = foo zs in
--   case z of λ
--     { (inj₁ a) → false ∷ fs , a ∷ as , bs
--     ; (inj₂ b) → true  ∷ fs , as , b ∷ bs }

-- -- foo (inj₁ a ∷ zs) = let fs , as , bs = foo zs in false ∷ fs , a ∷ as , bs
-- -- foo (inj₂ b ∷ zs) = let fs , as , bs = foo zs in true  ∷ fs , as , b ∷ bs
