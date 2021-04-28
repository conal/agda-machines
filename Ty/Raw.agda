{-# OPTIONS --safe --without-K #-}

module Ty.Raw where

open import Data.Bool using (if_then_else_) renaming (false to 𝕗; true to 𝕥)
open import Data.Product using (_,_)
open import Data.String using (String; parens; _++_)

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
   go {`Bool} _ b = show b
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


-- Miscellaneous utilities, perhaps to move elsewhere
module TyUtils {ℓ} {_⇨_ : Ty → Ty → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_) where

  open import Data.Nat
  open ty-instances using (products)

  module _ ⦃ _ : Braided ⦃ products ⦄ _⇨_ ⦄ where

    -- Todo: rename
    replicate′ : ∀ n → (⊤ ⇨ A) → (⊤ ⇨ V A n)
    replicate′ zero    a = !
    replicate′ (suc n) a = a ⦂ replicate′ n a

    shiftR : Bool × A ⇨ A × Bool
    shiftR {`⊤}     = swap
    shiftR {`Bool}  = id
    shiftR {_ `× _} = assocˡ ∘ second shiftR ∘ assocʳ ∘ first shiftR ∘ assocˡ

    -- i , (u , v)
    -- (i , u) , v
    -- (u′ , m) , v
    -- u′ , (m , v)
    -- u′ , (v′ , o)
    -- (u′ , v′) , o

    shiftL : A × Bool ⇨ Bool × A
    shiftL {`⊤}     = swap
    shiftL {`Bool}  = id
    shiftL {_ `× _} = assocʳ ∘ first shiftL ∘ assocˡ ∘ second shiftL ∘ assocʳ

    -- (u , v) , i
    -- u , (v , i)
    -- u , (m , v′)
    -- (u , m) , v′
    -- (o , u′) , v′
    -- o , (u′ , v′)

  module _ ⦃ _ : Cartesian ⦃ products ⦄ _⇨_ ⦄ where

    shiftR⇃ : Bool × A ⇨ A
    shiftR⇃ = exl ∘ shiftR

    shiftL⇃ : A × Bool ⇨ A
    shiftL⇃ = exr ∘ shiftL

    module _ ⦃ _ : Logic _⇨_ ⦄ where

      condᵀ : (A × A) × Bool ⇨ A  -- false , true

      condᵀ {  `⊤  } = !
      condᵀ {`Bool } = ∨ ∘ (∧ ⊗ ∧ ∘ first not) ∘ transpose ∘ second dup
      condᵀ {_ `× _} = (condᵀ ⊗ condᵀ) ∘ transpose ∘ (transpose ⊗ dup)

      -- -- `Bool
      -- (e , t) , c
      -- (e , t) , (c , c)
      -- (e , c) , (t , c)
      -- (e , not c) , (t , c)
      -- e ∧ not c , t ∧ c
      -- (e ∧ not c) ∨ (t ∧ c)

      -- _ `× _:
      -- ((e , e′) , (t , t′)) , c
      -- ((e , t) , (e′ , t′)) , (c , c)
      -- ((e , t) , c) , ((e′ , t′) , c)
      -- r , r′
