{-# OPTIONS --safe --without-K #-}

open import Level

module Categorical.Instances.Setoid.Laws (o : Level) where

open import Data.Product using (_,_)

open import Relation.Binary using (module Setoid)
open import Function.Equality as E using (Π) ; open Π

open import Miscellany
open import Categorical.Raw
open import Categorical.Laws
open import Categorical.Instances.Setoid.Raw o
open import Categorical.Instances.Function.Raw o

module setoid-lawful where

  instance

    equivalent : Equivalent o _⟶_
    equivalent = record { equiv = λ {a b} → Setoid.isEquivalence (a ⇛ b) }

    lawful-category : LawfulCategory _⟶_ o
    lawful-category = record
      { identityˡ = λ {a}{b}{f} → cong f
      ; identityʳ = λ {a}{b}{f} → cong f
      ; assoc = λ {a}{b}{c}{d}{f}{g}{h} x≈y → cong h (cong g (cong f x≈y))
      -- ; assoc = λ {a}{b}{c}{d}{f}{g}{h} x≈y → cong h ∘ cong g ∘ cong f
      ; ∘≈ = λ h≈k f≈g → h≈k ∘ f≈g
      }

    lawful-monoidal : LawfulMonoidal _⟶_ o
    lawful-monoidal = record
      { id⊗id = id
      ; ∘⊗ = λ {a₁ b₁ a₂ b₂ a₃ b₃} {f g h k} → cong (h ∘ f) ⊗ cong (k ∘ g)
      ; unitorᵉˡ∘unitorⁱˡ = id
      ; unitorⁱˡ∘unitorᵉˡ = id
      ; unitorᵉʳ∘unitorⁱʳ = id
      ; unitorⁱʳ∘unitorᵉʳ = id
      ; assocʳ∘assocˡ = id
      ; assocˡ∘assocʳ = id
      ; assocˡ∘⊗ = λ {a a′ b b′ c c′} {f : a ⟶ a′}{g : b ⟶ b′}{h : c ⟶ c′} →
          λ (x≈x′ , (y≈y′ , z≈z′)) → (cong f x≈x′ , cong g y≈y′) , cong h z≈z′
      ; assocʳ∘⊗ = λ {a a′ b b′ c c′} {f : a ⟶ a′}{g : b ⟶ b′}{h : c ⟶ c′} →
          λ ((x≈x′ , y≈y′) , z≈z′) → cong f x≈x′ , (cong g y≈y′ , cong h z≈z′)
      ; ⊗≈ = λ f≈h g≈k → f≈h ⊗ g≈k
      }
