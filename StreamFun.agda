-- Synchronous stream functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K --copatterns --guardedness #-}

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

open import Data.Nat

infix 8 _!_
_!_ : Stream A → ℕ → A
us ! zero = head us
us ! suc i = tail us ! i

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

Ext : ∀ {ℓ} → Rel B ℓ → Rel (A → B) ℓ
Ext _≈_ f g = ∀ a → f a ≈ g a

infix 4 _≛_
_≛_ : (u v : Stream A) → Set _
u ≛ v = Ext _≡_ (u !_) (v !_)
-- u ≛ v = ∀ n → u ! n ≡ v ! n

open import Data.Vec using (Vec; []; _∷_)

take : ∀ n → Stream A → Vec A n
take zero as = []
take (suc n) as = head as ∷ take n (tail as)

infix 4 _≛_upto_
_≛_upto_ : Stream A → Stream A → ℕ → Set _
u ≛ v upto n = take n u ≡ take n v

-- u ≛ v upto n = ∀ i → i < n → u ! i ≡ v ! i

zip : Stream A → Stream B → Stream (A × B)
head (zip as bs) = head as , head bs
tail (zip as bs) = zip (tail as) (tail bs)


infix 1 _↠_
_↠_ : Set → Set → Set
A ↠ B = Stream A → Stream B

infix 4 _≗_
_≗_ : (f g : A ↠ B) → Set _
_≗_ = Ext _≛_

causal : (A ↠ B) → Set _
causal f = ∀ n u v → u ≛ v upto n → f u ! n ≡ f v ! n

-- TODO: Define a category of causal stream functions. Then map Mealy to them.

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
unzip = < map proj₁ , map proj₂ >
-- unzip zs = map proj₁ zs , map proj₂ zs

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

-- Cons (memory/register)
delay : A → (A ↠ A)
delay = _∷_

scanlV : (B → A → B) → B → A ↠ B
head (scanlV f e as) = e
tail (scanlV f e as) = scanlV f (f e (head as)) (tail as)