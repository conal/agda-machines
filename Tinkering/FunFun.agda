-- Synchronous stream functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K --copatterns --guardedness #-}

module Tinkering.FunFun where

open import Function using (_∘′_; case_of_) renaming
  (id to id′; const to const′)
open import Data.Product hiding (zip) renaming (map to map×)
open import Data.Unit
open import Data.Nat
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality hiding (_≗_)


Stream : (A : Set) → Set
Stream A = ℕ → A

private
  variable
    A B C D : Set
    u v as : Stream A
    a : A

head : Stream A → A
head u = u zero

tail : Stream A → Stream A
tail u = u ∘′ suc

infixr 5 _∷_
_∷_ : A → Stream A → Stream A
(a ∷ as) zero    = a
(a ∷ as) (suc i) = as i

head∷ : head (a ∷ as) ≡ a
head∷ = refl

tail∷ : tail (a ∷ as) ≡ as
tail∷ = refl

-- Mapping a function (combinational logic)
map : (A → B) → Stream A → Stream B
map = _∘′_

zip : Stream A → Stream B → Stream (A × B)
zip = <_,_>

-- Seems a shame to make two passes, but I couldn't figure out how to satisfy
-- the termination checker in a single-pass definition.
unzip : Stream (A × B) → Stream A × Stream B
unzip = < map proj₁ , map proj₂ >
-- unzip zs = map proj₁ zs , map proj₂ zs

-- zip∘unzip : ∀ (u : Stream A) (v : Stream B) → unzip (zip u v) ≡ (u , v)
-- zip∘unzip (u , v) = refl

zip∘unzip : ∀ (uv : Stream A × Stream B) → unzip (uncurry zip uv) ≡ uv
zip∘unzip uv = refl

unzip∘zip : ∀ (w : Stream (A × B)) → uncurry zip (unzip w) ≡ w
unzip∘zip w = refl

-- Extensionality parametrized over an equivalence relation
Ext : ∀ {ℓ} → Rel B ℓ → Rel (A → B) ℓ
Ext _≈_ f g = ∀ a → f a ≈ g a

infix 4 _≛_
_≛_ : (u v : Stream A) → Set _
_≛_ = Ext _≡_

open import Data.Vec using (Vec; []) renaming (_∷_ to _∷ⱽ_)

-- Truncate to a vector
take : ∀ n → Stream A → Vec A n
take zero    as = []
take (suc n) as = head as ∷ⱽ take n (tail as)

infix 4 _≛_upto_
_≛_upto_ : Stream A → Stream A → ℕ → Set _
u ≛ v upto n = take n u ≡ take n v

infix 4 _≡_at_
_≡_at_ : Stream A → Stream A → ℕ → Set _
u ≡ v at i = u i ≡ v i

infix 1 _↠_
_↠_ : Set → Set → Set
A ↠ B = Stream A → Stream B

infix 4 _≗_
_≗_ : (f g : A ↠ B) → Set _
_≗_ = Ext _≛_

causal : (A ↠ B) → Set _
causal f = ∀ n u v → u ≛ v upto n → f u n ≡ f v n

-- TODO: Define a category of causal stream transformers. Then map Mealy to them.

-- Mapping a function (combinational logic)
arr : (A → B) → (A ↠ B)
arr = map

const : A → Stream A
const = const′

id : A ↠ A
id = id′

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
scanlV _∙_ ε u zero    = ε
scanlV _∙_ ε u (suc i) = scanlV _∙_ (ε ∙ head u) (tail u) i
