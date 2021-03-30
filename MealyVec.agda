-- Mealy machines indexed by the vector functions they denote

{-# OPTIONS --safe --without-K #-}
{-# OPTIONS --copatterns --guardedness #-}  -- to drop

module MealyVec where

open import Data.Sum     hiding (map)
open import Data.Product hiding (zip) renaming (map to map×)
open import Data.Unit
open import Data.Vec
open import Function using (_∘′_)

import VecFun as ◇
import Mealy  as □

open ◇ using (_↠_; _≗_)
open □.AsVecFun

private
  variable
    A B C D : Set

record M {A B : Set} (f : A ↠ B) : Set₁ where
  constructor mealyV
  field
    { mealy } : A □.⇨ B
    asVec : ⟦ mealy ⟧ ≗ f
    
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning

arr : (h : A → B) → M (◇.arr h)
-- arr h = mealyV (⟦arr⟧ h)
arr h = mealyV (p h)
 where
  p : ∀ (h : A → B) → ⟦ □.arr h ⟧ ≗ ◇.arr h
  p h [] = refl
  p h (a ∷ as) rewrite p h as = refl

infixr 9 _∘_
_∘_ : ∀ {f : A ↠ B}{g : B ↠ C} → M g → M f → M (g ◇.∘ f)
_∘_ {f = f}{g = g} (mealyV {mg} gv) (mealyV {mf} fv) = mealyV {mealy = mg □.∘ mf} λ as →
  begin
    ⟦ mg □.∘ mf ⟧ as
  ≡⟨ (mg ⟦∘⟧ mf) as ⟩
    (⟦ mg ⟧ ◇.∘ ⟦ mf ⟧) as
  ≡⟨⟩
    ⟦ mg ⟧ (⟦ mf ⟧ as)
  ≡⟨ gv (⟦ mf ⟧ as) ⟩
    g (⟦ mf ⟧ as)
  ≡⟨ cong g (fv as) ⟩
    g (f as)
  ≡⟨ refl ⟩
    (g ◇.∘ f) as
  ∎

infixr 7 _⊗_
_⊗_ : ∀ {f : A ↠ C}{g : B ↠ D} → M f → M g → M (f ◇.⊗ g)
_⊗_ {f = f}{g = g} (mealyV {mf} fv) (mealyV {mg} gv) = mealyV {mealy = mf □.⊗ mg} λ as →
  begin
    ⟦ mf □.⊗ mg ⟧ as
  ≡⟨ (mf ⟦⊗⟧ mg) as ⟩
    (⟦ mf ⟧ ◇.⊗ ⟦ mg ⟧) as
  ≡⟨⟩
    (uncurry zip ∘′ map× ⟦ mf ⟧ ⟦ mg ⟧ ∘′ unzip) as
  ≡⟨⟩
    uncurry zip (map× ⟦ mf ⟧ ⟦ mg ⟧ (unzip as))
  ≡⟨ {!!} ⟩
    (f ◇.⊗ g) as
  ∎

-- Hm. These asVec proofs seem difficult without assuming extensional equality
-- and quite easy with.
