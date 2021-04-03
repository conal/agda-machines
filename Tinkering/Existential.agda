-- Algebraic bundles for existentially quantified types, with equivalence
-- defined as equivalence on proj₁.  See http://conal.net/papers/language-derivatives

{-# OPTIONS --safe --without-K #-}
open import Level

module Tinkering.Existential where

open import Algebra
open import Data.Product
open import Function using (_on_)
import Relation.Binary.Construct.On as On

private variable b c ℓ : Level

-- Lift operations to dependent products
module Dop {A : Set c} (F : A → Set ℓ) where
  D₀ : A → Set ℓ
  D₁ : Op₁ A → Set (c ⊔ ℓ)
  D₂ : Op₂ A → Set (c ⊔ ℓ)

  D₀ s  = F s
  D₁ g = ∀ {a} → F a → F (g a)
  D₂ h  = ∀ {a b} → F a → F b → F (h a b)

module Inj {A : Set c} {F : A → Set ℓ} where

  open Dop F
  
  -- Mostly work with 2nd projections, ignoring and inferring 1st projections.
  pattern inj b = (_ , b)

  inj₁ : ∀ {∙_ : Op₁ A} (∙′_ : D₁ ∙_) → Op₁ (∃ F)
  inj₁ ∙′_ (inj x) = inj (∙′ x)

  inj₂ : ∀ {_∙_ : Op₂ A} (_∙′_ : D₂ _∙_) → Op₂ (∃ F)
  inj₂ _∙′_ (inj x) (inj y) = inj (x ∙′ y)

  private
    variable
      h : Level
      P : A → Set h
      Q : A → A → Set h
      R : A → A → A → Set h

  prop₁ : (∀ a → P a) → ∀ ((a , _) : ∃ F) → P a
  prop₁ P (a , _) = P a

  prop₂ : (∀ a b → Q a b) → ∀ ((a , _) (b , _) : ∃ F) → Q a b
  prop₂ Q (a , _) (b , _) = Q a b

  prop₃ : (∀ a b c → R a b c) → ∀ ((a , _) (b , _) (c , _) : ∃ F) → R a b c
  prop₃ R (a , _) (b , _) (c , _) = R a b c

open Inj
