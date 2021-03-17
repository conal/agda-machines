-- Decompose functions-to-sums

module SumIso where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Function

private
  variable
    A B C D X : Set

infixr 6 _⊕_
_⊕_ : (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
f ⊕ g = [ inj₁ ∘ f , inj₂ ∘ g ]

-- Is _⊕_ defined somewhere already?

step : (h : X → Bool) → (x : X) → T (h x) ⊎ T (not (h x))
step h x with h x
... | true  = inj₁ tt
... | false = inj₂ tt

-- Thanks to Arjan Rouvoet for suggesting step.

merge : (h : X → Bool) → (Σ X (T ∘ h) → A) → (Σ X (T ∘ not ∘ h) → B) → (X → A ⊎ B)
merge h f g x = (f ∘ (x ,_) ⊕ (g ∘ (x ,_))) (step h x)

split : (X → A ⊎ B) → Σ (X → Bool) λ h → (Σ X (T ∘ h) → A) × (Σ X (T ∘ not ∘ h) → B)
split f = is₁ ∘ f , split₁ f , split₂ f
 where
  is₁ : A ⊎ B → Bool
  is₁ = [ const true , const false ]

  split₁ : (f : X → A ⊎ B) → Σ X (T ∘ is₁ ∘ f) → A
  split₁ f (x , q) with f x
  split₁ f (x , tt) | inj₁ a = a

  split₂ : (f : X → A ⊎ B) → Σ X (T ∘ not ∘ is₁ ∘ f) → B
  split₂ f (x , q) with f x
  split₂ f (x , tt) | inj₂ b = b
 

-- TODO: prove that merge and split form an isomorphism
