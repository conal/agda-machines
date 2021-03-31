{-# OPTIONS --safe --without-K #-}

-- Some simple category type classes
-- Start just a few laws, and grow from there.

module Category where

open import Level
import Function as F
open import Relation.Binary.PropositionalEquality


record Category {o ℓ}{obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  infixr 9 _∘_
  -- infix 4 _≈_
  field
    id : ∀ {a} → a ⇨ a
    _∘_ : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
    -- _≈_ : ∀ {a b} (f g : a ⇨ b) → Set

    -- .id-l  : ∀ {a b}{f : a ⇨ b} → id ∘ f ≈ f
    -- .id-r  : ∀ {a b}{f : a ⇨ b} → f ∘ id ≈ f
    -- .assoc : ∀ {a b c d}{h : c ⇨ d} {g : b ⇨ c} {f : a ⇨ b}
    --        → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

open Category ⦃ … ⦄ public

Fun : Set → Set → Set
Fun a b = a → b

instance
  →-Category : Category Fun
  →-Category = record
                 { id    = F.id
                 ; _∘_   = F._∘′_
                 -- ; _≈_   = λ f g → ∀ {x} → f x ≡ g x
                 -- ; id-l  = refl
                 -- ; id-r  = refl
                 -- ; assoc = refl
                 }

private
  variable
    o ℓ : Level
    obj : Set o
    a b c d : obj


record Monoidal {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  infixr 2 _×_
  infixr 7 _⊗_
  field
    ⦃ cat ⦄ : Category _⇨_
    ⊤ : obj
    _×_ : obj → obj → obj
    _⊗_ : (a ⇨ c) → (b ⇨ d) → ((a × b) ⇨ (c × d))

    ! : a ⇨ ⊤

    unitorᵉˡ : (⊤ × a) ⇨ a
    unitorᵉʳ : (a × ⊤) ⇨ a
    unitorⁱˡ : a ⇨ (⊤ × a)
    unitorⁱʳ : a ⇨ (a × ⊤)

    assocʳ : ((a × b) × c) ⇨ (a × (b × c))
    assocˡ : (a × (b × c)) ⇨ ((a × b) × c)
open Monoidal ⦃ … ⦄ public

import Data.Unit as ⊤
import Data.Product as ×
open × using (_,_)

instance
  →-Monoidal : Monoidal Fun
  →-Monoidal = record
                  { ⊤ = ⊤.⊤
                  ; _×_ = ×._×_
                  ; _⊗_ = λ f g (x , y) → (f x , g y)
                  ; unitorᵉˡ = ×.proj₂
                  ; unitorᵉʳ = ×.proj₁
                  ; unitorⁱˡ = λ z → ⊤.tt , z
                  ; unitorⁱʳ = λ z → z , ⊤.tt
                  ; assocʳ = λ { ((x , y) , z) → x , (y , z) }
                  ; assocˡ = λ { (x , (y , z)) → (x , y) , z }
                  }

record Braided {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  field
    ⦃ _⇨_Monoidal ⦄ : Monoidal _⇨_
    swap : (a × b) ⇨ (b × a)

open Braided ⦃ … ⦄ public

instance
  →-Braided : Braided Fun
  →-Braided = record { swap = λ (a , b) → b , a }


record Cartesian {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  field
    ⦃ _⇨_Braided ⦄ : Braided _⇨_
    exl : (a × b) ⇨ a
    exr : (a × b) ⇨ b
    dup : a ⇨ (a × a)

  infixr 7 _△_
  _△_ : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ (c × d))
  f △ g = (f ⊗ g) ∘ dup

  first : a ⇨ c → (a × b) ⇨ (c × b)
  first f = f ⊗ id

  second : b ⇨ d → (a × b) ⇨ (a × d)
  second g = id ⊗ g

  transpose : ((a × b) × (c × d)) ⇨ ((a × c) × (b × d))
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)

open Cartesian ⦃ … ⦄ public

instance
  →-Cartesian : Cartesian Fun
  →-Cartesian = record { exl = ×.proj₁ ; exr = ×.proj₂ ; dup = λ z → z , z }


-- Not really about categories, so maybe move elsewhere

record Meaningful {m} (A : Set o) : Set (suc (m ⊔ o)) where
  field
    Meaning : Set m
    ⟦_⟧ : A → Meaning
open Meaningful ⦃ … ⦄ public

import Data.String as S
open S using (String)

record Show (A : Set o) : Set (suc o) where
  field
    show : A → String
open Show ⦃ … ⦄ public

open import Data.Nat
import Data.Nat.Show as NS

instance

  ℕ-Show : Show ℕ
  ℕ-Show = record { show = NS.show }

  -- etc
