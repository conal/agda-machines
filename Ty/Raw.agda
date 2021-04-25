{-# OPTIONS --safe --without-K #-}

module Ty.Raw where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
  renaming (false to false′; true to true′)
open import Data.Bool.Show as BS
open import Data.Product using (_,_; uncurry)
open import Data.Nat
open import Data.String using (String; parens; _++_)
open import Relation.Binary.PropositionalEquality

open import Categorical.Raw
open import Categorical.Instances.Function.Raw

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : (x : Ty) (y : Ty) → Ty

private variable A B C D : Ty

⟦_⟧ᵗ : Ty → Set
⟦ `⊤ ⟧ᵗ     = ⊤
⟦ σ `× τ ⟧ᵗ = ⟦ σ ⟧ᵗ × ⟦ τ ⟧ᵗ
⟦ `Bool ⟧ᵗ  = Bool

-- Currently unused, but seems useful
showTy : ⟦ A ⟧ᵗ → String
showTy = go true′
 where
   -- flag says we're in the left part of a pair
   go : Bool → ⟦ A ⟧ᵗ → String
   go {`⊤} _ tt = "tt"
   go {`Bool} _ b = BS.show b
   go {_ `× _} p (x , y) = (if p then parens else id)
                           (go true′ x ++ "," ++ go false′ y)


infix 0 _⇨_
record _⇨_ (A B : Ty) : Set where
  constructor mk
  field
    ⟦_⟧ : ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

module ty-instances where

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    _ : Boolean Ty
    _ = record { Bool = `Bool }

    Hₒ : Homomorphismₒ Ty Set
    Hₒ = record { Fₒ = ⟦_⟧ᵗ }

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ { (mk g) (mk f) → mk (g ∘ f) } }

  --   ⟦⟧-H : Homomorphism _⇨_ Function
  --   ⟦⟧-H = record { Fₘ = ⟦_⟧ }

    -- equivalent : Equivalent 0ℓ _⇨_
    -- equivalent = H-equiv ⟦⟧-H

  --   ⟦⟧-categoryH : CategoryH _⇨_ Function 0ℓ
  --   ⟦⟧-categoryH = record { F-id = λ x → refl ; F-∘  = λ f g x → refl }

  --   lawful-category : LawfulCategory _⇨_ 0ℓ
  --   lawful-category = LawfulCategoryᶠ ⟦⟧-categoryH

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_      = λ (mk f) (mk g) → mk (f ⊗ g)
      ; !        = mk !
      ; unitorᵉˡ = mk unitorᵉˡ
      ; unitorᵉʳ = mk unitorᵉʳ
      ; unitorⁱˡ = mk unitorⁱˡ
      ; unitorⁱʳ = mk unitorⁱʳ
      ; assocʳ   = mk assocʳ
      ; assocˡ   = mk assocˡ
      }

  --   productsH : ProductsH {obj₁ = Ty}{obj₂ = Set}
  --   productsH = record { F-⊤ = refl ; F-× = refl }

  --   ⟦⟧-monoidalH : MonoidalH _⇨_ Function 0ℓ
  --   ⟦⟧-monoidalH = record
  --     { F-!        = λ _ → refl
  --     ; F-⊗        = λ _ → refl
  --     ; F-unitorᵉˡ = λ _ → refl
  --     ; F-unitorⁱˡ = λ _ → refl
  --     ; F-unitorᵉʳ = λ _ → refl
  --     ; F-unitorⁱʳ = λ _ → refl
  --     ; F-assocʳ   = λ _ → refl
  --     ; F-assocˡ   = λ _ → refl
  --     }

  --   -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
  --   -- lawful-monoidal = LawfulMonoidalᶠ ⟦⟧-monoidalH

    braided : Braided _⇨_
    braided = record { swap = mk swap }

  --   ⟦⟧-braidedH : BraidedH _⇨_ Function 0ℓ
  --   ⟦⟧-braidedH = record { F-swap = λ x → refl }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = mk exl ; exr = mk exr ; dup = mk dup }

  --   ⟦⟧-cartesianH : CartesianH _⇨_ Function 0ℓ
  --   ⟦⟧-cartesianH = record
  --     { F-exl = λ _ → refl ; F-exr = λ _ → refl ; F-dup = λ _ → refl }

    logic : Logic _⇨_
    logic = record { false = mk false ; true = mk true
                   ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                   ; cond = mk cond
                   }

  --   ⟦⟧-logicH : LogicH _⇨_ Function 0ℓ
  --   ⟦⟧-logicH = record
  --      { F-Bool  = refl
  --      ; F-false = λ _ → refl
  --      ; F-true  = λ _ → refl
  --      ; F-not   = λ _ → refl
  --      ; F-∧     = λ _ → refl
  --      ; F-∨     = λ _ → refl
  --      ; F-xor   = λ _ → refl
  --      }


