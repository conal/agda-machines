{-# OPTIONS --safe --without-K #-}

module Categorical.Instances.Setoid.Raw where

open import Level using (0ℓ)

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
       renaming (refl to refl≡; cong to cong≡)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Function.Equality as E using (Π) ; open Π
import Relation.Binary.Bundles as B
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw

Setoid : Set₁
Setoid = B.Setoid 0ℓ 0ℓ

open B.Setoid

infixr 0 _⟶_
_⟶_ : Setoid → Setoid → Set
_⟶_ = E._⟶_

-- Lift a function between values to a setoid function, using equality.
lift→ : ∀ {a b} → (a → b) → (setoid a ⟶ setoid b)
lift→ f = record { _⟨$⟩_ = f ; cong = cong≡ f }

lift→₂ : ∀ {a b c} → (a × b → c) → (setoid a ×ₛ setoid b ⟶ setoid c)
lift→₂ f = record { _⟨$⟩_ = f ; cong = λ { (refl≡ , refl≡) → refl≡ } }

module setoid-instances where

  instance

    products : Products Setoid
    products = record { ⊤ = setoid ⊤′ ; _×_ = _×ₛ_ }

    exponentials : Exponentials Setoid
    exponentials = record { _⇛_ = E._⇨_ }

    import Data.Bool as Bool
    open Bool using () renaming (false to 𝕗; true to 𝕥)

    boolean : Boolean Setoid
    boolean = record { Bool = setoid Bool.Bool }

    -- boolean : Boolean Setoid
    -- boolean = record { Bool = setoid (Lift o B.Bool) }

    category : Category _⟶_
    category = record { id = E.id ; _∘_ = E._∘_ }

    open import Data.Product.Function.NonDependent.Setoid

    !⟶ : {a : Setoid} → (a ⟶ ⊤)
    !⟶ = record { _⟨$⟩_ = ! ; cong = λ _ → refl≡ }

    monoidal : Monoidal _⟶_
    monoidal = record
                 { _⊗_ = _×-⟶_
                 ; unitorᵉˡ = proj₂ₛ
                 ; unitorᵉʳ = proj₁ₛ
                 ; unitorⁱˡ = < !⟶ , id >ₛ
                 ; unitorⁱʳ = < id , !⟶ >ₛ
                 ; assocˡ = < id ×-⟶ proj₁ₛ , proj₂ₛ ∘ proj₂ₛ >ₛ
                 ; assocʳ = < proj₁ₛ ∘ proj₁ₛ , proj₂ₛ ×-⟶ id >ₛ
                 ; ! = E.const tt    -- move to Cartesian
                 }

    braided : Braided _⟶_
    braided = record { swap = swapₛ }

    cartesian : Cartesian _⟶_
    cartesian = record { exl = proj₁ₛ ; exr = proj₂ₛ ; dup = < id , id >ₛ }

    closed : Closed _⟶_
    closed = record { _⟴_ = λ f h →
      record { _⟨$⟩_ = λ g → h ∘ g ∘ f
             ; cong  = λ g₁≈g₂ → cong h ∘ g₁≈g₂ ∘ cong f
             }
      }

    logic : Logic _⟶_
    logic = record
      { false = lift→ false
      ; true  = lift→ true
      ; not   = lift→ not
      ; ∧     = lift→₂ ∧
      ; ∨     = lift→₂ ∨
      ; xor   = lift→₂ xor
      ; cond  = record
         { _⟨$⟩_ = cond
         ; cong  = λ { {𝕗 , _} {.𝕗 , _} (refl≡ , ≈a , ≈b) → ≈a
                     ; {𝕥 , _} {.𝕥 , _} (refl≡ , ≈a , ≈b) → ≈b }
         }
      }

