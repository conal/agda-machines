-- Composable Mealy machines

{-# OPTIONS --safe --without-K #-}

module MealyVec where

open import Data.Sum     hiding (map)
open import Data.Product hiding (map) renaming (map₁ to map×₁; swap to swap×)
open import Data.Unit
open import Data.Vec    hiding (map)

import VecFun as ◇
open ◇ using (_↠_)

private
  variable
    A B C D : Set

infix 0 _➩_

-- State machine synchronously mapping from List a to List b.
-- For composability, the state type is not visible in the type.
record _➩_ (A B : Set) : Set₁ where
  constructor mealy
  field
    { State } : Set
    start : State
    transition : A × State → B × State

-- Semantics
⟦_⟧ : (A ➩ B) → (A ↠ B)
⟦ mealy _ _ ⟧ [] = []
⟦ mealy s f ⟧ (a ∷ as) = let b , s′ = f (a , s) in b ∷ ⟦ mealy s′ f ⟧ as

-- Mapping a function (empty state, i.e., combinational logic)
map : (A → B) → (A ➩ B)
map f = mealy tt (map×₁ f)
                -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : (B ➩ C) → (A ➩ B) → (A ➩ C)
mealy t₀ g ∘ mealy s₀ f = mealy (s₀ , t₀) λ (a , (s , t)) →
 let b , s′ = f (a , s)
     c , t′ = g (b , t)
 in
    c , (s′ , t′)

-- Parallel composition / product tensor
infixr 7 _⊗_
_⊗_ : (A ➩ C) → (B ➩ D) → (A × B ➩ C × D)
mealy s₀ f ⊗ mealy t₀ g = mealy (s₀ , t₀) λ ((a , b) , (s , t)) →
  let c , s′ = f (a , s)
      d , t′ = g (b , t)
  in
    (c , d) , (s′ , t′)

-- Conditional/choice composition / coproduct tensor
infixr 6 _⊕_
_⊕_ : (A ➩ C) → (B ➩ D) → ((A ⊎ B) ➩ (C ⊎ D))
mealy s₀ f ⊕ mealy t₀ g = mealy (s₀ , t₀)
  λ { (inj₁ a , s , t) → let c , s′ = f (a , s) in inj₁ c , (s′ , t)
    ; (inj₂ b , s , t) → let d , t′ = g (b , t) in inj₂ d , (s  , t′) }

-- Cons (memory/register)
delay : A → (A ➩ A)
delay a₀ = mealy a₀ swap×
                    -- (λ (next , prev) → prev , next)

-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning

infix 4 _≗_
_≗_ : (f g : A ↠ B) → Set _
f ≗ g = ∀ {n} (as : Vec _ n) → f as ≡ g as

⟦map⟧ : ∀ (h : A → B) → ⟦ map h ⟧ ≗ ◇.map h
⟦map⟧ h [] = refl
⟦map⟧ h (a ∷ as) rewrite ⟦map⟧ h as = refl

infixr 9 _⟦∘⟧_
_⟦∘⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
(_ ⟦∘⟧ _) [] = refl
(mealy t g ⟦∘⟧ mealy s f) (a ∷ as)
  rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
            (mealy t′ g ⟦∘⟧ mealy s′ f) as) = refl

infixr 7 _⟦⊗⟧_
_⟦⊗⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ⊗ f ⟧ ≗ ⟦ g ⟧ ◇.⊗ ⟦ f ⟧
(_ ⟦⊗⟧ _) [] = refl
(mealy s f ⟦⊗⟧ mealy t g) ((a , b) ∷ abs)
  rewrite (let c , s′ = f (a , s) ; d , t′ = g (b , t) in 
            (mealy s′ f ⟦⊗⟧ mealy t′ g) abs) = refl

-- infixr 7 _⟦⊕⟧_
-- _⟦⊕⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ⊕ f ⟧ ≗ ⟦ g ⟧ ◇.⊕ ⟦ f ⟧
-- f ⟦⊕⟧ g = ?


⟦delay⟧ : (a₀ : A) → ⟦ delay a₀ ⟧ ≗ ◇.delay a₀
⟦delay⟧ a₀ [] = refl
⟦delay⟧ a₀ (a ∷ as) =
  begin
    ⟦ delay a₀ ⟧ (a ∷ as)
  ≡⟨⟩
    ⟦ mealy a₀ swap× ⟧ (a ∷ as)
  ≡⟨⟩
    (let b , s′ = swap× (a , a₀) in b ∷ ⟦ mealy s′ swap× ⟧ as)
  ≡⟨⟩
    a₀ ∷ ⟦ mealy a swap× ⟧ as
  ≡⟨⟩
    a₀ ∷ ⟦ delay a ⟧ as
  ≡⟨ cong (a₀ ∷_) (⟦delay⟧ a as) ⟩
    a₀ ∷ ◇.delay a as
  ≡⟨ ◇.∷delay ⟩
    ◇.delay a₀ (a ∷ as)
  ∎ where open ≡-Reasoning
