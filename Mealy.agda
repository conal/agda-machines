-- Composable Mealy machines

{-# OPTIONS --safe --without-K #-}

{-# OPTIONS --guardedness #-}

module Mealy where

open import Data.Sum     hiding (map)
open import Data.Product hiding (map) renaming (map₁ to map×₁; swap to swap×)
open import Data.Unit

private
  variable
    A B C D : Set

infix 0 _⇨_

-- State machine synchronously mapping from List a to List b.
-- For composability, the state type is not visible in the type.
record _⇨_ (A B : Set) : Set₁ where
  constructor mealy
  field
    { State } : Set
    start : State
    transition : A × State → B × State

-- Mapping a function (empty state, i.e., combinational logic)
arr : (A → B) → (A ⇨ B)
arr f = mealy tt (map×₁ f)
                 -- λ (a , tt) → f a , tt

-- Sequential composition
infixr 9 _∘_
_∘_ : (B ⇨ C) → (A ⇨ B) → (A ⇨ C)
mealy t₀ g ∘ mealy s₀ f = mealy (s₀ , t₀) λ (a , (s , t)) →
 let b , s′ = f (a , s)
     c , t′ = g (b , t)
 in
    c , (s′ , t′)

-- Parallel composition / product tensor
infixr 7 _⊗_
_⊗_ : (A ⇨ C) → (B ⇨ D) → (A × B ⇨ C × D)
mealy s₀ f ⊗ mealy t₀ g = mealy (s₀ , t₀) λ ((a , b) , (s , t)) →
  let c , s′ = f (a , s)
      d , t′ = g (b , t)
  in
    (c , d) , (s′ , t′)

-- Conditional/choice composition / coproduct tensor
infixr 6 _⊕_
_⊕_ : (A ⇨ C) → (B ⇨ D) → ((A ⊎ B) ⇨ (C ⊎ D))
mealy s₀ f ⊕ mealy t₀ g = mealy (s₀ , t₀)
  λ { (inj₁ a , (s , t)) → let c , s′ = f (a , s) in inj₁ c , (s′ , t)
    ; (inj₂ b , (s , t)) → let d , t′ = g (b , t) in inj₂ d , (s  , t′) }

-- Cons (memory/register)
delay : A → (A ⇨ A)
delay a₀ = mealy a₀ swap×
                    -- (λ (next , prev) → prev , next)

scanlV : (B → A → B) → B → A ⇨ B
scanlV f s₀ = mealy s₀ (λ (a , s) → s , f s a)

-- Specification via denotational homomorphisms
module AsVecFun where

  open import Relation.Binary.PropositionalEquality hiding (_≗_)
  open ≡-Reasoning
  open import Data.Vec hiding (map)

  import VecFun as ◇
  open ◇ using (_↠_; _≗_)

  ⟦_⟧ : (A ⇨ B) → (A ↠ B)
  ⟦ mealy _ _ ⟧ [] = []
  ⟦ mealy s f ⟧ (a ∷ as) = let b , s′ = f (a , s) in b ∷ ⟦ mealy s′ f ⟧ as

  ⟦arr⟧ : ∀ (h : A → B) → ⟦ arr h ⟧ ≗ ◇.arr h
  ⟦arr⟧ h [] = refl
  ⟦arr⟧ h (a ∷ as) rewrite ⟦arr⟧ h as = refl

  infixr 9 _⟦∘⟧_
  _⟦∘⟧_ : ∀ (g : B ⇨ C) (f : A ⇨ B) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
  (_ ⟦∘⟧ _) [] = refl
  (mealy t g ⟦∘⟧ mealy s f) (a ∷ as)
    rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
              (mealy t′ g ⟦∘⟧ mealy s′ f) as) = refl

  infixr 7 _⟦⊗⟧_
  _⟦⊗⟧_ : ∀ (f : A ⇨ C) (g : B ⇨ D) → ⟦ f ⊗ g ⟧ ≗ ⟦ f ⟧ ◇.⊗ ⟦ g ⟧
  (_ ⟦⊗⟧ _) [] = refl
  (mealy s f ⟦⊗⟧ mealy t g) ((a , b) ∷ abs)
    rewrite (let c , s′ = f (a , s) ; d , t′ = g (b , t) in 
              (mealy s′ f ⟦⊗⟧ mealy t′ g) abs) = refl

  -- infixr 7 _⟦⊕⟧_
  -- _⟦⊕⟧_ : ∀ (f : A ⇨ C) (g : B ⇨ D) → ⟦ f ⊕ g ⟧ ≗ ⟦ f ⟧ ◇.⊕ ⟦ g ⟧
  -- f ⟦⊕⟧ g = ?

  ⟦delay⟧ : (a₀ : A) → ⟦ delay a₀ ⟧ ≗ ◇.delay a₀
  ⟦delay⟧ a₀ [] = refl
  ⟦delay⟧ a₀ (a ∷ as) =
    begin
      ⟦ delay a₀ ⟧ (a ∷ as)
    ≡⟨⟩
      a₀ ∷ ⟦ delay a ⟧ as
    ≡⟨ cong (a₀ ∷_) (⟦delay⟧ a as) ⟩
      a₀ ∷ ◇.delay a as
    ≡˘⟨ ◇.delay∷ ⟩
      ◇.delay a₀ (a ∷ as)
    ∎

  ⟦scanlV⟧ : ∀ (f : B → A → B) → (s₀ : B) → ⟦ scanlV f s₀ ⟧ ≗ ◇.scanlV f s₀
  ⟦scanlV⟧ f s₀ [] = refl
  ⟦scanlV⟧ f s₀ (a ∷ as) rewrite ⟦scanlV⟧ f (f s₀ a) as = refl

-- Specification via denotational homomorphisms
module AsStreamFun where

  open import Relation.Binary.PropositionalEquality hiding (_≗_)
  open ≡-Reasoning

  import StreamFun as ◇
  open ◇ using (_↠_; _∷_ ; head; tail; _≗_)

  -- ⟦_⟧ : (A ⇨ B) → (A ↠ B)
  -- ⟦ mealy s f ⟧ as = let b , s′ = f (head as , s) in b ∷ ⟦ mealy s′ f ⟧ (tail as)

  -- Termination checking failed for the following functions:
  --   AsStreamFun.⟦_⟧
  -- Problematic calls:
  --   ⟦ mealy (proj₂ (f (head as , s))) f ⟧ (tail as)
  --     (at /Users/conal/Agda/Machines/Mealy.agda:129,58-72)

  -- ⟦arr⟧ : ∀ (h : A → B) → ⟦ arr h ⟧ ≗ ◇.arr h
  -- ⟦arr⟧ h [] = refl
  -- ⟦arr⟧ h (a ∷ as) rewrite ⟦arr⟧ h as = refl

  -- infixr 9 _⟦∘⟧_
  -- _⟦∘⟧_ : ∀ (g : B ⇨ C) (f : A ⇨ B) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
  -- (_ ⟦∘⟧ _) [] = refl
  -- (mealy t g ⟦∘⟧ mealy s f) (a ∷ as)
  --   rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
  --             (mealy t′ g ⟦∘⟧ mealy s′ f) as) = refl

  -- infixr 7 _⟦⊗⟧_
  -- _⟦⊗⟧_ : ∀ (f : A ⇨ C) (g : B ⇨ D) → ⟦ f ⊗ g ⟧ ≗ ⟦ f ⟧ ◇.⊗ ⟦ g ⟧
  -- (_ ⟦⊗⟧ _) [] = refl
  -- (mealy s f ⟦⊗⟧ mealy t g) ((a , b) ∷ abs)
  --   rewrite (let c , s′ = f (a , s) ; d , t′ = g (b , t) in 
  --             (mealy s′ f ⟦⊗⟧ mealy t′ g) abs) = refl

  -- -- infixr 7 _⟦⊕⟧_
  -- -- _⟦⊕⟧_ : ∀ (f : A ⇨ C) (g : B ⇨ D) → ⟦ f ⊕ g ⟧ ≗ ⟦ f ⟧ ◇.⊕ ⟦ g ⟧
  -- -- f ⟦⊕⟧ g = ?

  -- ⟦delay⟧ : (a₀ : A) → ⟦ delay a₀ ⟧ ≗ ◇.delay a₀
  -- ⟦delay⟧ a₀ [] = refl
  -- ⟦delay⟧ a₀ (a ∷ as) =
  --   begin
  --     ⟦ delay a₀ ⟧ (a ∷ as)
  --   ≡⟨⟩
  --     a₀ ∷ ⟦ delay a ⟧ as
  --   ≡⟨ cong (a₀ ∷_) (⟦delay⟧ a as) ⟩
  --     a₀ ∷ ◇.delay a as
  --   ≡˘⟨ ◇.delay∷ ⟩
  --     ◇.delay a₀ (a ∷ as)
  --   ∎

  -- ⟦scanlV⟧ : ∀ (f : B → A → B) → (s₀ : B) → ⟦ scanlV f s₀ ⟧ ≗ ◇.scanlV f s₀
  -- ⟦scanlV⟧ f s₀ [] = refl
  -- ⟦scanlV⟧ f s₀ (a ∷ as) rewrite ⟦scanlV⟧ f (f s₀ a) as = refl
