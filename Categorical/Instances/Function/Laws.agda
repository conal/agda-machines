{-# OPTIONS --safe --without-K #-}

open import Level using (Level)

module Categorical.Instances.Function.Laws (o : Level) where

open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; cong)
open import Data.Product using (_,_)

open import Miscellany
open import Categorical.Raw
open import Categorical.Laws
open import Categorical.Instances.Function.Raw o

module →Lawful where

  instance

    equivalent : Equivalent o Function
    equivalent = record
      { _≈_ = _≗_
      ; equiv = λ {a}{b} → record
          { refl  = λ x → ≡.refl
          ; sym   = λ f∼g x → ≡.sym (f∼g x)
          ; trans = λ f∼g g∼h x → ≡.trans (f∼g x) (g∼h x)
          }
      }

    -- TODO: consider using an implicitly parametrized _≗_ .

    lawful-category : LawfulCategory Function o
    lawful-category = record
      { identityˡ = refl
      ; identityʳ = refl
      ; assoc     = refl
      ; ∘≈  = λ {a b c}{f g}{h k} h∼k f∼g x
                      → ≡.trans (h∼k (f x)) (cong k (f∼g x))
      }

    lawful-monoidal : LawfulMonoidal Function o
    lawful-monoidal = record
      { id⊗id             = refl
      ; ∘⊗                = refl
      ; unitorᵉˡ∘unitorⁱˡ = refl
      ; unitorⁱˡ∘unitorᵉˡ = refl
      ; unitorᵉʳ∘unitorⁱʳ = refl
      ; unitorⁱʳ∘unitorᵉʳ = refl
      ; assocʳ∘assocˡ     = refl
      ; assocˡ∘assocʳ     = refl
      ; assocˡ∘⊗          = refl
      ; assocʳ∘⊗          = refl
      ; ⊗≈ = λ f≗h g≗k → λ (x , y) → f≗h x ≡,≡ g≗k y
      }
