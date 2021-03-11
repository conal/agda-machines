-- Length-preserving vector functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecFun where

open import Function using (_∘′_; case_of_; const) renaming (id to id′)
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
id = id′

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
... | _ , _ , refl = refl

-- TODO: Package init∷ into an agda-stdlib PR.

delay∷ : ∀ {a₀ a : A} {n} {as : Vec A n} → delay a₀ (a ∷ as) ≡ a₀ ∷ delay a as
delay∷ {a = a}{as = as} = init∷ (a ∷ as)


-- scanlV : (B → A → B) → B → ∀ {n} → Vec A n → Vec B n
scanlV : (B → A → B) → B → A ↠ B
scanlV f e []       = []
scanlV f e (a ∷ as) = e ∷ scanlV f (f e a) as

scanlV′ : (B → A → B) → B → ∀ {n} → Vec A n → Vec B (suc n)
scanlV′ f e []       = e ∷ []
scanlV′ f e (a ∷ as) = e ∷ scanlV′ f (f e a) as

open ≡-Reasoning

init∘scanlV′ : ∀ {f : B → A → B} {e : B} {n} (as : Vec A n)
             → init (scanlV′ f e as) ≡ scanlV f e as
init∘scanlV′ [] = refl
init∘scanlV′ {f = f}{e} (a ∷ as) =
  begin
    init (e ∷ scanlV′ f (f e a) as)
  ≡⟨ init∷ _ ⟩
    e ∷ init (scanlV′ f (f e a) as)
  ≡⟨ cong (e ∷_) (init∘scanlV′ as) ⟩
    e ∷ scanlV f (f e a) as
  ∎

scanlV∷ʳ : ∀ {f : B → A → B} {e : B} {n} (as : Vec A n)
         → scanlV′ f e as ≡ scanlV f e as ∷ʳ foldl _ f e as
scanlV∷ʳ [] = refl
scanlV∷ʳ {f = f}{e} (a ∷ as) =
  begin
    scanlV′ f e (a ∷ as)
  ≡⟨⟩
    e ∷ scanlV′ f (f e a) as
  ≡⟨ cong (e ∷_) (scanlV∷ʳ as) ⟩
    e ∷ (scanlV f (f e a) as ∷ʳ foldl _ f e (a ∷ as))
  ≡⟨⟩
    (e ∷ scanlV f (f e a) as) ∷ʳ foldl _ f e (a ∷ as)
  ≡⟨⟩
    scanlV f e (a ∷ as) ∷ʳ foldl _ f e (a ∷ as)
  ∎

init∷ʳ : ∀ {n}(as : Vec A n) {a} → init (as ∷ʳ a) ≡ as
init∷ʳ [] = refl
init∷ʳ (a′ ∷ as) {a = a} =
  begin
    init ((a′ ∷ as) ∷ʳ a)
  ≡⟨⟩
    init (a′ ∷ (as ∷ʳ a))
  ≡⟨ init∷ _ ⟩
    a′ ∷ init (as ∷ʳ a)
  ≡⟨ cong (a′ ∷_) (init∷ʳ as) ⟩
    a′ ∷ as
  ∎

-- scanlV′ f e (a ∷ as) = e ∷ scanlV′ f (f e a) as

-- scanlV f e (a ∷ as) = e ∷ scanlV f (f e a) as


-- init∷ : ∀ {a : A}{n} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
