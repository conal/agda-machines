-- Composable Mealy machines

{-# OPTIONS --safe --without-K #-}

module Mealy where

open import Data.Sum     hiding (map)
open import Data.Product hiding (map) renaming (map₁ to map×₁; swap to swap×)
open import Data.Unit
open import Data.List    hiding (map)

import ListFun as ◇
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

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

⟦map⟧ : ∀ (h : A → B) → ⟦ map h ⟧ ≗ ◇.map h
⟦map⟧ h [] = refl
⟦map⟧ h (a ∷ as) rewrite ⟦map⟧ h as = refl

-- ⟦map⟧ h (a ∷ as) =
--   begin
--     ⟦ map h ⟧ (a ∷ as)
--   ≡⟨⟩
--     ⟦ mealy tt (map₁ h) ⟧ (a ∷ as)
--   ≡⟨⟩
--     let (b , tt) = map₁ h (a , tt) in b ∷ ⟦ mealy tt (map₁ h) ⟧ as
--   ≡⟨⟩
--     let b = h a in b ∷ ⟦ mealy tt (map₁ h) ⟧ as
--   ≡⟨⟩
--     h a ∷ ⟦ map h ⟧ as
--   ≡⟨ cong (h a ∷_) (⟦map⟧ h as) ⟩
--     h a ∷ ◇.map h as
--   ≡⟨⟩
--     ◇.map h (a ∷ as)
--   ∎

infixr 9 _⟦∘⟧_
_⟦∘⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
(_ ⟦∘⟧ _) [] = refl

(mealy t g ⟦∘⟧ mealy s f) (a ∷ as)
  rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
            (mealy t′ g ⟦∘⟧ mealy s′ f) as) = refl

-- (mealy t g ⟦∘⟧ mealy s f) (a ∷ as) =
--   begin
--     ⟦ mealy t g ∘ mealy s f ⟧ (a ∷ as)
--   ≡⟨⟩
--     ⟦ mealy (s , t) (λ (a , (s , t)) → let b , s′ = f (a , s) ; c , t′ = g (b , t) in c , (s′ , t′)) ⟧ (a ∷ as)
--   ≡⟨⟩
--     let b , s′ = f (a , s) ; c , t′ = g (b , t) in c ∷  ⟦ mealy t′ g ∘ mealy s′ f ⟧ as
--   ≡⟨ (let b , s′ = f (a , s) ; c , t′ = g (b , t) in
--        cong (c ∷_) ((mealy t′ g ⟦∘⟧ mealy s′ f) as)) ⟩
--     let b , s′ = f (a , s) ; c , t′ = g (b , t) in c ∷ (⟦ mealy t′ g ⟧ ◇.∘ ⟦ mealy s′ f ⟧) as
--   ≡⟨⟩
--     let b , s′ = f (a , s) ; c , t′ = g (b , t) in c ∷ ⟦ mealy t′ g ⟧ (⟦ mealy s′ f ⟧ as)
--   ≡⟨⟩
--     let b , s′ = f (a , s) in let c , t′ = g (b , t) in c ∷ ⟦ mealy t′ g ⟧ (⟦ mealy s′ f ⟧ as)
--   ≡⟨⟩
--     let b , s′ = f (a , s) in ⟦ mealy t g ⟧ (b ∷ ⟦ mealy s′ f ⟧ as)
--   ≡⟨⟩
--     ⟦ mealy t g ⟧ (let b , s′ = f (a , s) in b ∷ ⟦ mealy s′ f ⟧ as)
--   ≡⟨⟩
--     ⟦ mealy t g ⟧ (⟦ mealy s f ⟧ (a ∷ as))
--   ≡⟨⟩
--     (⟦ mealy t g ⟧ ◇.∘ ⟦ mealy s f ⟧) (a ∷ as)
--   ∎

infixr 7 _⟦⊗⟧_
_⟦⊗⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ⊗ f ⟧ ≗ ⟦ g ⟧ ◇.⊗ ⟦ f ⟧
(_ ⟦⊗⟧ _) [] = refl
(mealy s f ⟦⊗⟧ mealy t g) ((a , b) ∷ abs)
  rewrite (let c , s′ = f (a , s) ; d , t′ = g (b , t) in 
            (mealy s′ f ⟦⊗⟧ mealy t′ g) abs) = refl

-- infixr 7 _⟦⊕⟧_
-- _⟦⊕⟧_ : ∀ (g : B ➩ C) (f : A ➩ B) → ⟦ g ⊕ f ⟧ ≗ ⟦ g ⟧ ◇.⊕ ⟦ f ⟧
-- f ⟦⊕⟧ g = ?

-- TODO: ⟦delay⟧. I don't think this one holds without dropping the final value.
