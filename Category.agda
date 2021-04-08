{-# OPTIONS --safe --without-K #-}
-- Some simple category type classes
-- Start just a few laws, and grow from there.

module Category where

open import Level renaming (suc to lsuc)
open import Function using (_∘′_; const) renaming (id to id′)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public

open import Relation.Binary

record Equivalent {e} {obj : Set o} (_⇨_ : obj → obj → Set ℓ)
       : Set (lsuc o ⊔ ℓ ⊔ lsuc e) where
  infix 4 _≈_
  field
    _≈_ : Rel (a ⇨ b) e      -- (f g : a ⇨ b) → Set e
    equiv : ∀ {a b} → IsEquivalence (_≈_ {a}{b})

  module Equiv {a b} where
    open IsEquivalence (equiv {a}{b}) public
      renaming (refl to refl≈; sym to sym≈; trans to trans≈)
  open Equiv public

  ≈setoid : obj → obj → Setoid ℓ e
  ≈setoid a b = record { isEquivalence = equiv {a}{b} }

open Equivalent ⦃ … ⦄ public

record LawfulCategory {e} {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
       : Set (lsuc o ⊔ ℓ ⊔ lsuc e) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ cat ⦄ : Category _⇨_
    ⦃ cat-equiv ⦄ : Equivalent {e = e} _⇨_

    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d}
              → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    ∘-resp-≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  ∘-resp-≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘-resp-≈ˡ h≈k = ∘-resp-≈ h≈k refl≈

open LawfulCategory ⦃ … ⦄ public

record Functor {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
               {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
               {e₁} ⦃ equiv₁ : Equivalent {e = e₁} _⇨₁_ ⦄
               {e₂} ⦃ equiv₂ : Equivalent {e = e₂} _⇨₂_ ⦄
               ⦃ cat₁ : Category _⇨₁_ ⦄
               ⦃ cat₂ : Category _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  field
    Fₒ : obj₁ → obj₂
    Fₘ : ∀ {a b} → (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

    F-id : Fₘ (id {a = a}) ≈ id {a = Fₒ a}
    F-∘  : ∀ {f : a ⇨₁ b}{g : b ⇨₁ c} → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

open Functor ⦃ … ⦄ public

record Products (obj : Set o) : Set (lsuc o) where
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
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _⊗_
  field
    ⦃ ⇨cat ⦄ : Category _⇨_
    _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)

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

  -- -- Pseudo values  -- but _⇨_ doesn't get inferred
  -- ⌞_⌟ : obj → Set ℓ
  -- ⌞ A ⌟ = ⊤ ⇨ A

  infixr 4 _⦂_
  -- _⦂_ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ a × b ⌟
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ

open Monoidal ⦃ … ⦄ public

open import Data.Unit using (tt) renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
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


record Meaningful {m} {μ : Set m} (A : Set o) : Set (lsuc (m ⊔ o)) where
  field
    ⟦_⟧ : A → μ
open Meaningful ⦃ … ⦄ public

record Boolean (obj : Set o) : Set (lsuc o) where
  field
    Bool : obj
open Boolean ⦃ … ⦄ public

record Logic {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ∧ ∨ xor : Bool × Bool ⇨ Bool
    not : Bool ⇨ Bool
    true false : ⊤ ⇨ Bool
open Logic ⦃ … ⦄ public


import Data.String as S
open S using (String)

-- Not really about categories, so maybe move elsewhere
record Show (A : Set o) : Set (lsuc o) where
  field
    show : A → String
open Show ⦃ … ⦄ public

-- TODO: Consider using setoid functions instead
Function : Set o → Set o → Set o
Function a b = a → b

module →Instances where

  instance

    category : Category (Function {o})
    category = record { id = id′ ; _∘_ = _∘′_ }

    equivalent : Equivalent {e = o} (Function {o})
    equivalent = record
      { _≈_ = λ f g → ∀ {x} → f x ≡ g x
      ; equiv = λ {a}{b} → record
          { refl  = refl
          ; sym   = λ fx≡gx → sym fx≡gx
          ; trans = λ fx≡gx gx≡hx → trans fx≡gx gx≡hx
          }
      }

    lawful-category : LawfulCategory {e = o} (Function {o})
    lawful-category = record
      { identityˡ = λ {a b}{f}{x} → refl
      ; identityʳ = λ {a b}{f}{x} → refl
      ; assoc     = λ {c d b a}{f g h}{x} → refl
      ; ∘-resp-≈  = λ {a b c}{f g}{h k} h≈k f≈g {x} → let open ≡-Reasoning in
          begin
            h (f x)
          ≡⟨ h≈k {f x} ⟩
            k (f x)
          ≡⟨ cong k (f≈g {x}) ⟩
            k (g x)
          ∎
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
                  ; assocʳ   = λ ((x , y) , z) → x , (y , z)
                  ; assocˡ   = λ (x , (y , z)) → (x , y) , z
                  }

    braided : Braided Function
    braided = record { swap = λ (a , b) → b , a }

    cartesian : Cartesian Function
    cartesian = record { exl = proj₁ ; exr = proj₂ ; dup = λ z → z , z }

    meaningful : Meaningful (Set ℓ)
    meaningful = record { ⟦_⟧ = id }

    import Data.Bool as B

    boolean : Boolean Set
    boolean = record { Bool  = B.Bool }

    logic : Logic Function
    logic = record
              { ∧     = uncurry B._∧_
              ; ∨     = uncurry B._∨_
              ; xor   = uncurry B._xor_
              ; not   = B.not
              ; true  = const B.true
              ; false = const B.false
              }

    import Data.Bool.Show as BS
    import Data.Nat.Show as NS
    open import Data.Fin using (Fin)
    import Data.Fin.Show as FS

    Bool-Show : Show Bool
    Bool-Show = record { show = BS.show }

    ℕ-Show : Show ℕ
    ℕ-Show = record { show = NS.show }

    Fin-Show : ∀ {n} → Show (Fin n)
    Fin-Show = record { show = FS.show }

    import Data.String as S
    String-Show : Show S.String
    String-Show = record { show = S.show }

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
