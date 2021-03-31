-- Some simple category type classes
-- Start just a few laws, and grow from there.

module Category where

open import Level
import Function as F
open import Relation.Binary.PropositionalEquality


record Category {o}{obj : Set o} (_↝_ : obj → obj → Set) : Set (suc o) where
  infixr 9 _∘_
  infix 4 _≈_
  field
    id : ∀ {a} → a ↝ a
    _∘_ : ∀ {a b c} → (b ↝ c) → (a ↝ b) → (a ↝ c)
    _≈_ : ∀ {a b} (f g : a ↝ b) → Set

    .id-l  : ∀ {A B}{f : A ↝ B} → id ∘ f ≈ f
    .id-r  : ∀ {A B}{f : A ↝ B} → f ∘ id ≈ f
    .assoc : ∀ {A B C D}{h : C ↝ D} {g : B ↝ C} {f : A ↝ B}
           → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

open Category ⦃ … ⦄ public

Fun : Set → Set → Set
Fun a b = a → b

instance
  →-Category : Category Fun
  →-Category = record
                 { id = F.id
                 ; _∘_ = F._∘′_
                 ; _≈_ = _≗_
                 ; id-l = λ _ → refl
                 ; id-r = λ x → refl
                 ; assoc = λ x → refl
                 }

private
  variable
    o : Level
    obj : Set o
    a b c d : obj


record MonoidalP {obj : Set o} (_↝_ : obj → obj → Set) : Set (suc o) where
  infixr 2 _×_
  infixr 7 _⊗_
  field
    ⦃ cat ⦄ : Category _↝_
    ⊤ : obj
    _×_ : obj → obj → obj
    _⊗_ : (a ↝ c) → (b ↝ d) → ((a × b) ↝ (c × d))

    unitorᵉˡ : (⊤ × a) ↝ a
    unitorᵉʳ : (a × ⊤) ↝ a
    unitorⁱˡ : a ↝ (⊤ × a)
    unitorⁱʳ : a ↝ (a × ⊤)

    assocʳ : ((a × b) × c) ↝ (a × (b × c))
    assocˡ : (a × (b × c)) ↝ ((a × b) × c)
open MonoidalP ⦃ … ⦄ public

import Data.Unit as ⊤
import Data.Product as ×
open × using (_,_)

instance
  →-MonoidalP : MonoidalP Fun
  →-MonoidalP = record
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

record Braided {obj : Set o} (_↝_ : obj → obj → Set) : Set (suc o) where
  field
    ⦃ _↝_MonoidalP ⦄ : MonoidalP _↝_
    swap : (a × b) ↝ (b × a)
open Braided ⦃ … ⦄ public

instance
  →-Braided : Braided Fun
  →-Braided = record { swap = λ (a , b) → b , a }


record Cartesian {obj : Set o} (_↝_ : obj → obj → Set) : Set (suc o) where
  field
    ⦃ _↝_Braided ⦄ : Braided _↝_
    exl : (a × b) ↝ a
    exr : (a × b) ↝ b
    dup : a ↝ (a × a)

  infixr 7 _△_
  _△_ : ∀ {a c d} → (a ↝ c) → (a ↝ d) → (a ↝ (c × d))
  f △ g = (f ⊗ g) ∘ dup

  first : a ↝ c → (a × b) ↝ (c × b)
  first f = f ⊗ id

  second : b ↝ d → (a × b) ↝ (a × d)
  second g = id ⊗ g

  transpose : ((a × b) × (c × d)) ↝ ((a × c) × (b × d))
  transpose = (exl ⊗ exl) △ (exr ⊗ exr)

open Cartesian ⦃ … ⦄ public

instance
  →-Cartesian : Cartesian Fun
  →-Cartesian = record { exl = ×.proj₁ ; exr = ×.proj₂ ; dup = λ z → z , z }
