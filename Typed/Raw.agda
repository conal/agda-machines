{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw

module Typed.Raw {o ℓ} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
                 (_↠_ : obj → obj → Set ℓ) where

open import Data.Nat

open import Categorical.Instances.Function.Raw

open import Ty -- public

private variable a b c d : Ty

⟦_⟧ : Ty → obj
⟦ `⊤ ⟧     = ⊤
⟦ σ `× τ ⟧ = ⟦ σ ⟧ × ⟦ τ ⟧
⟦ `Bool ⟧  = Bool

infix 0 _⇨_
record _⇨_ (a b : Ty) : Set ℓ where
  constructor mk
  field
    f : ⟦ a ⟧ ↠ ⟦ b ⟧

module typed-instances where

  instance

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    category : ⦃ _ : Category _↠_ ⦄ → Category _⇨_
    category = record { id = mk id ; _∘_ = λ { (mk g) (mk f) → mk (g ∘ f) } }

    monoidal : ⦃ _ : Monoidal _↠_ ⦄ → Monoidal _⇨_
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

    braided : ⦃ _ : Braided _↠_ ⦄ → Braided _⇨_
    braided = record { swap = mk swap }

    cartesian : ⦃ _ : Cartesian _↠_ ⦄ → Cartesian _⇨_
    cartesian = record { exl = mk exl ; exr = mk exr ; dup = mk dup }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

    logic : ⦃ _ : Logic _↠_ ⦄ → Logic ⦃ boolean = boolean ⦄ _⇨_
    logic = record { false = mk false ; true = mk true
                   ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                   ; cond = mk cond
                   }

-- Miscellaneous utilities, perhaps to move elsewhere
module TyUtils {ℓ}
  {_⇨_ : Ty → Ty → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_) where

  open import Data.Nat
  open typed-instances using (products)

  module _ ⦃ _ : Braided ⦃ products ⦄ _⇨_ ⦄ where

    -- Todo: rename
    replicate′ : ∀ n → (⊤ ⇨ a) → (⊤ ⇨ V a n)
    replicate′ zero    a = !
    replicate′ (suc n) a = a ⦂ replicate′ n a

    shiftR : Bool × a ⇨ a × Bool
    shiftR {`⊤}     = swap
    shiftR {`Bool}  = swap
    shiftR {_ `× _} = assocˡ ∘ second shiftR ∘ assocʳ ∘ first shiftR ∘ assocˡ

    -- i , (u , v)
    -- (i , u) , v
    -- (u′ , m) , v
    -- u′ , (m , v)
    -- u′ , (v′ , o)
    -- (u′ , v′) , o

    shiftL : a × Bool ⇨ Bool × a
    shiftL {`⊤}     = swap
    shiftL {`Bool } = swap
    shiftL {_ `× _} = assocʳ ∘ first shiftL ∘ assocˡ ∘ second shiftL ∘ assocʳ

    -- (u , v) , i
    -- u , (v , i)
    -- u , (m , v′)
    -- (u , m) , v′
    -- (o , u′) , v′
    -- o , (u′ , v′)

  module _ ⦃ _ : Cartesian ⦃ products ⦄ _⇨_ ⦄ where

    shiftR⇃ : Bool × a ⇨ a
    shiftR⇃ = exl ∘ shiftR

    shiftL⇃ : a × Bool ⇨ a
    shiftL⇃ = exr ∘ shiftL

    module _ ⦃ _ : Logic _⇨_ ⦄ where

      condᵀ : (a × a) × Bool ⇨ a  -- false , true

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
