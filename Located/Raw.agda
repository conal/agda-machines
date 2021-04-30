{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw

module Located.Raw {o ℓ} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
                   (_↠_ : obj → obj → Set ℓ)
                   {p} (pos : Set p) where

open import Data.Nat

open import Categorical.Instances.Function.Raw

infixr 2 _`×_
data Located : Set p where
  `⊤    : Located
  `Bool : pos → Located
  _`×_  : Located → Located → Located

private variable a b c d : Located

⟦_⟧ : Located → obj
⟦ `⊤ ⟧      = ⊤
⟦ σ `× τ ⟧  = ⟦ σ ⟧ × ⟦ τ ⟧
⟦ `Bool _ ⟧ = Bool

infix 0 _⇨_
record _⇨_ (a b : Located) : Set ℓ where
  constructor mk
  field
    f : ⟦ a ⟧ ↠ ⟦ b ⟧

module located-instances where

  instance

    products : Products Located
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


-- Per-location Boolean & Logic.
-- TODO: evaluate explicit vs implicit Loc argument.
module AtPos (p : pos) where

  instance

      boolean : Boolean Located
      boolean = record { Bool = `Bool p }

      logic : ⦃ _ : Logic _↠_ ⦄ → Logic ⦃ boolean = boolean ⦄ _⇨_
      logic = record { false = mk false ; true = mk true
                     ; ∧ = mk ∧ ; ∨ = mk ∨ ; xor = mk xor ; not = mk not
                     ; cond = mk cond
                     }

      -- The signature `cond : Bool × (a × a) ⇨ a` suggests that the bits in `a`
      -- needn't colocate with the condition bit. The single-bit mux definition
      -- via ∧, ∨, and `xor`, do require colocation.
      --
      -- Oops. The types of all logic operations colocate outputs and inputs (in
      -- time and in space). (This statement is vacuous for false and true.) We
      -- might have to revisit these types. We'll probably want de Morgan's laws
      -- and other boolean algebra equivalences to hold.
      --
      -- We might change the operation types to allow the booleans involved to
      -- be *any* boolean object for the category. Seems much too lax.

-- Miscellaneous utilities, perhaps to move elsewhere
module LocatedUtils {ℓ}
  {_⇨_ : Located → Located → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_)
  (p : pos) where

  open AtPos p

  open import Data.Nat
  open located-instances using (products)

  module _ ⦃ _ : Braided ⦃ products ⦄ _⇨_ ⦄ where

    -- Todo: rename
    replicate′ : ∀ n → (⊤ ⇨ a) → (⊤ ⇨ V a n)
    replicate′ zero    a = !
    replicate′ (suc n) a = a ⦂ replicate′ n a

    shiftR : Bool × a ⇨ a × Bool
    shiftR {`⊤}      = swap
    shiftR {`Bool _} = swap
    shiftR {_ `× _}  = assocˡ ∘ second shiftR ∘ assocʳ ∘ first shiftR ∘ assocˡ

    -- i , (u , v)
    -- (i , u) , v
    -- (u′ , m) , v
    -- u′ , (m , v)
    -- u′ , (v′ , o)
    -- (u′ , v′) , o

    shiftL : a × Bool ⇨ Bool × a
    shiftL {`⊤}      = swap
    shiftL {`Bool _} = swap
    shiftL {_ `× _}  = assocʳ ∘ first shiftL ∘ assocˡ ∘ second shiftL ∘ assocʳ

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
