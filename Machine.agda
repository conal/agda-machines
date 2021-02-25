-- Synchronous stream functions as composable state machines

{-# OPTIONS --safe --without-K #-}

module Machine where

open import Data.Product hiding (map)
open import Data.Unit
open import Data.List    hiding (map)

import ListFun as ◇
open ◇ using (_⇢_)

private
  variable
    a b c d : Set

infix 1 _➩_

-- State machine synchronously mapping from List a to List b.
-- For composability, the state type is not visible in the type.
record _➩_ (a b : Set) : Set₁ where
  constructor mach
  field
    { σ } : Set
    s₀ : σ
    f : a × σ → b × σ

-- We can easily make machines universe-level-polymorphic

⟦_⟧ : (a ➩ b) → (a ⇢ b)
⟦ mach s f ⟧ [] = []
⟦ mach s f ⟧ (a ∷ as) = let (b , s′) = f (a , s) in b ∷ ⟦ mach s′ f ⟧ as

-- Mapping a function (empty state)
map : (a → b) → (a ➩ b)
map f = mach tt (map₁ f)
                -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : (b ➩ c) → (a ➩ b) → (a ➩ c)
mach t₀ g ∘ mach s₀ f = mach (s₀ , t₀) λ (a , (s , t)) →
 let (b , s′) = f (a , s)
     (c , t′) = g (b , t)
 in
    c , (s′ , t′)

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (a ➩ c) → (b ➩ d) → (a × b ➩ c × d)
mach s f ⊗ mach t g = mach (s , t) λ ((a , b) , (s , t)) →
  let (c , s′) = f (a , s)
      (d , t′) = g (b , t)
  in
    (c , d) , (s′ , t′)

-- Cons (memory/register)
delay : a → (a ➩ a)
delay a = mach a swap
                 -- (λ (next , prev) → prev , next)

-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

⟦map⟧ : ∀ (h : a → b) → ⟦ map h ⟧ ≗ ◇.map h
⟦map⟧ h [] = refl
⟦map⟧ h (a ∷ as) rewrite ⟦map⟧ h as = refl

-- ⟦map⟧ h (a ∷ as) =
--   begin
--     ⟦ map h ⟧ (a ∷ as)
--   ≡⟨⟩
--     ⟦ mach tt (map₁ h) ⟧ (a ∷ as)
--   ≡⟨⟩
--     let (b , tt) = map₁ h (a , tt) in b ∷ ⟦ mach tt (map₁ h) ⟧ as
--   ≡⟨⟩
--     let b = h a in b ∷ ⟦ mach tt (map₁ h) ⟧ as
--   ≡⟨⟩
--     h a ∷ ⟦ map h ⟧ as
--   ≡⟨ cong (h a ∷_) (⟦map⟧ h as) ⟩
--     h a ∷ ◇.map h as
--   ≡⟨⟩
--     ◇.map h (a ∷ as)
--   ∎

⟦∘⟧ : ∀ (g : b ➩ c) (f : a ➩ b) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
⟦∘⟧ g f [] = refl
-- ⟦∘⟧ g f (a ∷ as) rewrite ⟦∘⟧ g f as = {!refl!}

⟦∘⟧ (mach t g) (mach s f) (a ∷ as) =
  begin
    ⟦ mach t g ∘ mach s f ⟧ (a ∷ as)
  ≡⟨⟩
    ⟦ mach (s , t) (λ (a , (s , t)) → let (b , s′) = f (a , s) ; (c , t′) = g (b , t) in c , (s′ , t′)) ⟧ (a ∷ as)
  ≡⟨⟩
    let (b , s′) = f (a , s) ; (c , t′) = g (b , t) in c ∷  ⟦ mach t′ g ∘ mach s′ f ⟧ as
  ≡⟨ cong (_ ∷_) (⟦∘⟧ (mach _ g) (mach _ f) as) ⟩
    let (b , s′) = f (a , s) ; (c , t′) = g (b , t) in c ∷ (⟦ mach t′ g ⟧ ◇.∘ ⟦ mach s′ f ⟧) as
  ≡⟨⟩
    let (b , s′) = f (a , s) ; (c , t′) = g (b , t) in c ∷ ⟦ mach t′ g ⟧ (⟦ mach s′ f ⟧ as)
  ≡⟨⟩
    let (b , s′) = f (a , s) in let (c , t′) = g (b , t) in c ∷ ⟦ mach t′ g ⟧ (⟦ mach s′ f ⟧ as)
  ≡⟨⟩
    let (b , s′) = f (a , s) in ⟦ mach t g ⟧ (b ∷ ⟦ mach s′ f ⟧ as)
  ≡⟨⟩
    ⟦ mach t g ⟧ (let (b , s′) = f (a , s) in b ∷ ⟦ mach s′ f ⟧ as)
  ≡⟨⟩
    ⟦ mach t g ⟧ (⟦ mach s f ⟧ (a ∷ as))
  ≡⟨⟩
    (⟦ mach t g ⟧ ◇.∘ ⟦ mach s f ⟧) (a ∷ as)
  ∎

-- ⟦_⟧ : (a ➩ b) → (a ⇢ b)
-- ⟦ mach s f ⟧ [] = []
-- ⟦ mach s f ⟧ (a ∷ as) = let (b , s′) = f (a , s) in b ∷ ⟦ mach s′ f ⟧ as

-- ⟦ mach t g ⟧ (b ∷ ⟦ mach s′ f ⟧ as) = let (c , t′) = g (b , t) in c ∷ ⟦ mach t′ g ⟧ (⟦ mach s′ f ⟧ as)
