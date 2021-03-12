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
    n : ℕ

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

-- scanlV : (B → A → B) → B → ∀ {n} → Vec A n → Vec B n
scanlV : (B → A → B) → B → A ↠ B
scanlV f e []       = []
scanlV f e (a ∷ as) = e ∷ scanlV f (f e a) as

scanlV′ : (B → A → B) → B → ∀ {n} → Vec A n → Vec B (suc n)
scanlV′ f e []       = e ∷ []
scanlV′ f e (a ∷ as) = e ∷ scanlV′ f (f e a) as


-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

init∷ : ∀ {a : A} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
init∷ as with initLast as
... | _ , _ , refl = refl

-- TODO: Package init∷ into an agda-stdlib PR.

delay∷ : ∀ {a₀ a : A} {as : Vec A n} → delay a₀ (a ∷ as) ≡ a₀ ∷ delay a as
delay∷ {a = a}{as = as} = init∷ (a ∷ as)

open ≡-Reasoning

init∘scanlV′ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
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

scanlV∷ʳ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
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

init∷ʳ : ∀ (as : Vec A n) {x} → init (as ∷ʳ x) ≡ as
init∷ʳ [] = refl
init∷ʳ (a ∷ as) {x = x} =
  begin
    init ((a ∷ as) ∷ʳ x)
  ≡⟨⟩
    init (a ∷ (as ∷ʳ x))
  ≡⟨ init∷ _ ⟩
    a ∷ init (as ∷ʳ x)
  ≡⟨ cong (a ∷_) (init∷ʳ as) ⟩
    a ∷ as
  ∎


-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

open import Data.Bool

bval : Bool → ℕ
bval false = 0
bval true  = 1

⟦_⟧ : Vec Bool n → ℕ
⟦_⟧ = foldl _ (λ n b → bval b + 2 * n) 0

ex₁ : ⟦ true ∷ false ∷ true ∷ [] ⟧ ≡ 5
ex₁ = refl


Carry : Set
Carry = Bool

halfAdd : Bool → Bool → Bool × Carry
halfAdd a b = a xor b , a ∧ b

fullAdd : Carry → Bool → Bool → Bool × Carry
fullAdd cin a b =
  let a+b , cout₁ = halfAdd a b
      p , cout₂ = halfAdd cin a+b
  in
    p , cout₁ ∨ cout₂

addⱽ : Carry → Vec Bool n → Vec Bool n → Vec Bool n × Carry
addⱽ cin [] [] = [] , cin
addⱽ cin (a ∷ as) (b ∷ bs) =
  let sum₁ , cout₁ = fullAdd cin a b
      sums , cout  = addⱽ cout₁ as bs
  in
     sum₁ ∷ sums , cout

-- ⟦addⱽ⟧
