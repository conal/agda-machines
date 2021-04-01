{-# OPTIONS --safe --without-K #-}

-- Some simple category type classes
-- Start just a few laws, and grow from there.

module Category where

open import Level
open import Function using (_∘′_) renaming (id to id′; const to const′)
open import Relation.Binary.PropositionalEquality

private variable o ℓ : Level

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  infixr 9 _∘_
  -- infix 4 _≈_
  field
    id : ∀ {a} → a ⇨ a
    _∘_ : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
    -- _≈_ : ∀ {a b} (f g : a ⇨ b) → Set

    -- .identityˡ : ∀ {a b}{f : a ⇨ b} → id ∘ f ≈ f
    -- .identityʳ : ∀ {a b}{f : a ⇨ b} → f ∘ id ≈ f
    -- .assoc : ∀ {a b c d}{h : c ⇨ d} {g : b ⇨ c} {f : a ⇨ b}
    --        → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

open Category ⦃ … ⦄ public

Function : Set o → Set o → Set o
Function a b = a → b

private
  variable
    obj : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Products (obj : Set o) : Set (suc o) where
  infixr 2 _×_
  field
    ⊤ : obj
    _×_ : obj → obj → obj

  open import Data.Nat
  infixl 8 _↑_
  _↑_ : obj → ℕ → obj
  A ↑ zero  = ⊤
  A ↑ suc n = A × A ↑ n

open Products ⦃ … ⦄ public

record Monoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _⊗_
  field
    ⦃ ⇨cat ⦄ : Category _⇨_
    -- ⊤ : obj
    -- _×_ : obj → obj → obj
    _⊗_ : (a ⇨ c) → (b ⇨ d) → ((a × b) ⇨ (c × d))

    ! : a ⇨ ⊤

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

  inAssocˡ : ((a × b) × c ⇨ (a′ × b′) × c′)
           → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ f = assocʳ ∘ f ∘ assocˡ

  inAssocʳ : (a × (b × c) ⇨ a′ × (b′ × c′))
           → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ f = assocˡ ∘ f ∘ assocʳ

open Monoidal ⦃ … ⦄ public

open import Data.Unit using (tt) renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Monoidal ⦄ : Monoidal _⇨_
    swap : a × b ⇨ b × a

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = (inAssocʳ ∘′ second ∘′ inAssocˡ ∘′ first) swap

  -- transpose = inAssocʳ (second (inAssocˡ (first swap)))
  -- transpose = assocˡ ∘ second (assocʳ ∘ first swap ∘ assocˡ) ∘ assocʳ

  -- (a × b) × (c × d)
  -- a × (b × (c × d))
  -- a × ((b × c) × d)
  -- a × ((c × b) × d)
  -- a × (c × (b × d))
  -- (a × c) × (b × d)

open Braided ⦃ … ⦄ public


record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
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


record Meaningful {m} {μ : Set m} (A : Set o) : Set (suc (m ⊔ o)) where
  field
    ⟦_⟧ : A → μ
open Meaningful ⦃ … ⦄ public

record Constants {obj : Set o} ⦃ _ : Products obj ⦄
         {m} ⦃ _ : Meaningful {μ = Set m} obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ ⊔ m) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    -- Maybe add a constraint
    -- constraint : obj → Set -- level?
    const : ∀ {A : obj} {- → constraint A -} → ⟦ A ⟧ → ⊤ ⇨ A  -- In another class
open Constants ⦃ … ⦄ public


record Boolean {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (suc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    Bool : obj
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    not : Bool ⇨ Bool
open Boolean ⦃ … ⦄ public



import Data.String as S
open S using (String)

-- Not really about categories, so maybe move elsewhere
record Show (A : Set o) : Set (suc o) where
  field
    show : A → String
open Show ⦃ … ⦄ public

open import Data.Nat
import Data.Nat.Show as NS


module →Instances where

  instance

    category : Category (Function {o})
    category = record
                  { id    = id′
                  ; _∘_   = _∘′_
                  -- ; _≈_   = λ f g → ∀ {x} → f x ≡ g x
                  -- ; id-l  = refl
                  -- ; id-r  = refl
                  -- ; assoc = refl
                  }

    products : Products Set
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    monoidal : Monoidal Function
    monoidal = record
                  { _⊗_ = λ f g (x , y) → (f x , g y)
                  ; unitorᵉˡ = proj₂
                  ; unitorᵉʳ = proj₁
                  ; unitorⁱˡ = tt ,_
                  ; unitorⁱʳ = _, tt
                  ; assocʳ = λ ((x , y) , z) → x , (y , z)
                  ; assocˡ = λ (x , (y , z)) → (x , y) , z
                  }

    braided : Braided Function
    braided = record { swap = λ (a , b) → b , a }

    cartesian : Cartesian Function
    cartesian = record { exl = proj₁ ; exr = proj₂ ; dup = λ z → z , z }

    meaningful : Meaningful (Set ℓ)
    meaningful = record { ⟦_⟧ = id }

    constants : Constants Function
    constants = record { const = const′ }

    import Data.Bool as B

    boolean : Boolean Function
    boolean = record
                 { Bool  = B.Bool
                 ; ∧     = uncurry B._∧_
                 ; ∨     = uncurry B._∨_
                 ; xor   = uncurry B._xor_
                 ; not   = B.not
                 }

    ℕ-Show : Show ℕ
    ℕ-Show = record { show = NS.show }

    -- etc

-- Some category-polymorphic idioms
module CartUtils ⦃ _ : Products obj ⦄
  {_⇨_ : obj → obj → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_) -- Note
  ⦃ cart : Cartesian _⇨_ ⦄ where

  -- Note: fixity hack. See https://github.com/agda/agda/issues/1235

  -- Like _∘_, but accumulating extra outputs
  -- (g ◂ f) a = let u , b = f a ; v , c = g b in (u , v) , c
  infixr 9 _◂_
  _◂_ : ∀ {u v} → (b ⇨ v × c) → (a ⇨ u × b) → (a ⇨ (u × v) × c)
  g ◂ f = assocˡ ∘ second g ∘ f

  -- Repeated _◂_
  infixl 5 _↱_
  _↱_ : (a ⇨ b × a) → (n : ℕ) → (a ⇨ b ↑ n × a)
  f ↱ zero  = unitorⁱˡ
  f ↱ suc n = (f ↱ n) ◂ f
