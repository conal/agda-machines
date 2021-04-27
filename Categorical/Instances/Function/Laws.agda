{-# OPTIONS --safe --without-K #-}

module Categorical.Instances.Function.Laws where

open import Level using (Level)
open import Function using (_∘′_; const; _on_; flip) renaming (id to id′)
-- open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

open import Miscellany
open import Categorical.Raw
open import Categorical.Laws

open import Categorical.Instances.Function.Raw

private variable o : Level

module →Lawful where

  instance

    equivalent : Equivalent o Function
    equivalent = record
      { _≈_ = _≗_
      ; equiv = λ {a}{b} → record
          { refl  = λ x → refl
          ; sym   = λ f∼g x → sym (f∼g x)
          ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
          }
      }

    -- TODO: consider using an implicitly parametrized _≗_ .

    lawful-category : LawfulCategory Function o
    lawful-category = record
      { identityˡ = λ x → refl
      ; identityʳ = λ x → refl
      ; assoc     = λ x → refl
      ; ∘-resp-≈  = λ {a b c}{f g}{h k} h∼k f∼g x
                      → trans (h∼k (f x)) (cong k (f∼g x))
      }

    lawful-monoidal : LawfulMonoidal Function o
    lawful-monoidal = record
      { id⊗id             = λ x → refl
      ; ∘⊗                = λ x → refl
      ; unitorᵉˡ∘unitorⁱˡ = λ x → refl
      ; unitorⁱˡ∘unitorᵉˡ = λ x → refl
      ; unitorᵉʳ∘unitorⁱʳ = λ x → refl
      ; unitorⁱʳ∘unitorᵉʳ = λ x → refl
      ; assocʳ∘assocˡ     = λ x → refl
      ; assocˡ∘assocʳ     = λ x → refl
      ; assocˡ∘⊗          = λ x → refl
      ; ⊗-resp-≈          = λ f≗h g≗k → λ (x , y) → f≗h x ≡,≡ g≗k y
      ; assocʳ∘⊗          = λ x → refl
      }
