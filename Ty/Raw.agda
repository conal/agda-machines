{-# OPTIONS --safe --without-K #-}

module Ty.Raw where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
  renaming (false to 𝕗; true to 𝕥)
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
showTy = go 𝕥
 where
   -- Flag says we're in the left part of a pair
   go : Bool → ⟦ A ⟧ᵗ → String
   go {`⊤} _ tt = "tt"
   go {`Bool} _ b = BS.show b
   go {_ `× _} p (x , y) = (if p then parens else id) (go 𝕥 x ++ "," ++ go 𝕗 y)


infix 0 _⇨_
record _⇨_ (A B : Ty) : Set where
  constructor mk
  field
    ⟦_⟧ : ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

module ty-instances where

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

    Hₒ : Homomorphismₒ Ty Set
    Hₒ = record { Fₒ = ⟦_⟧ᵗ }

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ { (mk g) (mk f) → mk (g ∘ f) } }

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

    braided : Braided _⇨_
    braided = record { swap = mk swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = mk exl ; exr = mk exr ; dup = mk dup }

    logic : Logic _⇨_
    logic = record { false = mk false ; true = mk true
                   ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                   ; cond = mk cond
                   }


