{-# OPTIONS --safe --without-K #-}

module Categorical.Raw where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function using (_∘′_; const; _on_; flip) renaming (id to id′)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR
import Relation.Binary.Construct.On as On

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

-- Trick to use "tt" as a pattern and value
import Data.Unit as U
pattern tt = lift U.tt


record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public


-- Iterated composition
infixr 8 _↑_
_↑_ : ∀ {a}{A : Set a} → (A → A) → ℕ → (A → A)
f ↑ zero  = id′
f ↑ suc n = f ∘′ (f ↑ n)

record Products (obj : Set o) : Set (lsuc o) where
  infixr 2 _×_
  field
    ⊤ : obj
    _×_ : obj → obj → obj

  infixr 2 _×≡_
  _×≡_ : ∀ {a₁ a₂ b₁ b₂ : obj}
       → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ × b₁) ≡ (a₂ × b₂)
  refl ×≡ refl = refl

  open import Data.Nat

  V T : obj → ℕ → obj
  V A n = ((A ×_) ↑ n) ⊤
  T A n = ((λ z → z × z) ↑ n) A

  -- TODO: redefine via fold etc

open Products ⦃ … ⦄ public


record Monoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _⊗_
  field
    ⦃ ⇨Category ⦄ : Category _⇨_

    ! : a ⇨ ⊤
    _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)

    unitorᵉˡ : ⊤ × a ⇨ a
    unitorᵉʳ : a × ⊤ ⇨ a
    unitorⁱˡ : a ⇨ ⊤ × a
    unitorⁱʳ : a ⇨ a × ⊤

    assocʳ : (a × b) × c ⇨ a × (b × c)
    assocˡ : a × (b × c) ⇨ (a × b) × c

  first : a ⇨ c → a × b ⇨ c × b
  first f = f ⊗ id

  second : b ⇨ d → a × b ⇨ a × d
  second g = id ⊗ g

  inAssocˡ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ f = assocʳ ∘ f ∘ assocˡ

  inAssocˡ′ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
  inAssocˡ′ = inAssocˡ ∘′ first

  inAssocʳ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ f = assocˡ ∘ f ∘ assocʳ

  inAssocʳ′ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
  inAssocʳ′ = inAssocʳ ∘′ second

  -- -- Pseudo values  -- but _⇨_ doesn't get inferred
  -- ⌞_⌟ : obj → Set ℓ
  -- ⌞ A ⌟ = ⊤ ⇨ A

  infixr 4 _⦂_
  -- _⦂_ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ a × b ⌟
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ

open Monoidal ⦃ … ⦄ public


record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Monoidal ⦄ : Monoidal _⇨_
    swap : a × b ⇨ b × a

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ′ (inAssocˡ′ swap)

open Braided ⦃ … ⦄ public


record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Braided ⦄ : Braided _⇨_
    exl : a × b ⇨ a
    exr : a × b ⇨ b
    dup : a ⇨ a × a

  infixr 7 _△_
  _△_ : ∀ {a c d} → a ⇨ c → (a ⇨ d) → (a ⇨ c × d)
  f △ g = (f ⊗ g) ∘ dup

open Cartesian ⦃ … ⦄ public


record Boolean (obj : Set o) : Set (lsuc o) where
  field
    Bool : obj
open Boolean ⦃ … ⦄ public

record Logic {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : ⊤ ⇨ Bool
    not : Bool ⇨ Bool
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    cond : Bool × (a × a) ⇨ a
open Logic ⦃ … ⦄ public


-- Unsure where we want Equivalent

record Equivalent q {obj : Set o} (_⇨_ : obj → obj → Set ℓ)
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  infix 4 _≈_
  field
    _≈_ : Rel (a ⇨ b) q   -- (f g : a ⇨ b) → Set q
    equiv : ∀ {a b} → IsEquivalence (_≈_ {a}{b})

  module Equiv {a b} where
    open IsEquivalence (equiv {a}{b}) public
      renaming (refl to refl≈; sym to sym≈; trans to trans≈)
  open Equiv public

  ≈setoid : obj → obj → Setoid ℓ q
  ≈setoid a b = record { isEquivalence = equiv {a}{b} }

  module ≈-Reasoning {a b} where
    open SetoidR (≈setoid a b) public

-- TODO: Replace Equivalent by Setoid?
-- I think we need _⇨_ as an argument rather than field.

open Equivalent ⦃ … ⦄ public