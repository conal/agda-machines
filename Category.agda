{-# OPTIONS --safe --without-K #-}
-- Some simple category type classes
-- Start with a few laws, and grow from there.

module Category where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function using (_∘′_; const; _on_) renaming (id to id′)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR
import Relation.Binary.Construct.On as On

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

-- Trick to use "tt" as a pattern and value
import Data.Unit as U
pattern tt = lift U.tt

-- Utilities to go elsewhere

subst′ : ∀ {ℓ a}{A : Set a}
           (P : A → Set ℓ) {x y} → y ≡ x → P x → P y
subst′ P y≡x = subst P (sym y≡x)

subst₂′ : ∀ {ℓ a b}{A : Set a}{B : Set b}
            (_∼_ : REL A B ℓ) {x y u v} → y ≡ x → v ≡ u → x ∼ u → y ∼ v
subst₂′ _∼_ y≡x v≡u = subst₂ _∼_ (sym y≡x) (sym v≡u)


record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)

open Category ⦃ … ⦄ public

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

open Equivalent ⦃ … ⦄ public

record LawfulCategory q {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ cat ⦄ : Category _⇨_
    ⦃ cat-equiv ⦄ : Equivalent q _⇨_

    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d}
              → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    ∘-resp-≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  ∘-resp-≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘-resp-≈ˡ h≈k = ∘-resp-≈ h≈k refl≈

  ∘-resp-≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘-resp-≈ʳ f≈g = ∘-resp-≈ refl≈ f≈g

open LawfulCategory ⦃ … ⦄ public

record Homomorphismₒ (obj₁ : Set o₁) (obj₂ : Set o₂) : Set (o₁ ⊔ o₂) where
  field
    Fₒ : obj₁ → obj₂

id-homomorphismₒ : Homomorphismₒ obj obj
id-homomorphismₒ = record { Fₒ = id′ }

record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    ⦃ homomorphismₒ ⦄ : Homomorphismₒ obj₁ obj₂
  open Homomorphismₒ homomorphismₒ public
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

-- open Homomorphism ⦃ … ⦄ public  -- yes or no?

-- Category homomorphism (functor)
record CategoryH {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
                 {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                 q₂ ⦃ equiv₂ : Equivalent q₂ _⇨₂_ ⦄
                 ⦃ cat₁ : Category _⇨₁_ ⦄
                 ⦃ cat₂ : Category _⇨₂_ ⦄
                 ⦃ homomorphism : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  open Homomorphism homomorphism public
  field
    F-id : Fₘ {a = a} id ≈ id
    F-∘  : ∀ (g : b ⇨₁ c) (f : a ⇨₁ b) → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

-- open CategoryH ⦃ … ⦄ public

-- I don't know whether to open CategoryH and use it with instances or keep it
-- closed and open explicitly where used. I guess the main question is whether
-- we'll usually have a single special CategoryH instance per pairs of
-- categories or not. For now, keep it explicit, and see what we learn.

F-equiv : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
          {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
          {q₂ : Level} ⦃ equiv₂ : Equivalent q₂ _⇨₂_ ⦄
          ⦃ cat₁ : Category _⇨₁_ ⦄
          ⦃ cat₂ : Category _⇨₂_ ⦄
          ⦃ homomorphism : Homomorphism _⇨₁_ _⇨₂_ ⦄
          (F : CategoryH _⇨₁_ _⇨₂_ q₂)  -- note explicit/visible argument
        → Equivalent q₂ _⇨₁_
F-equiv F = record { equiv = On.isEquivalence (CategoryH.Fₘ F) equiv }


LawfulCategoryᶠ : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
                  {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
                  {q₂ : Level} ⦃ equiv₂ : Equivalent q₂ _⇨₂_ ⦄
                  ⦃ cat₁ : Category _⇨₁_ ⦄
                  ⦃ cat₂ : Category _⇨₂_ ⦄
                  ⦃ lawful₂ : LawfulCategory q₂ _⇨₂_ ⦄
                  ⦃ homomorphism : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  (F : CategoryH _⇨₁_ _⇨₂_ q₂)
                → LawfulCategory q₂ _⇨₁_
LawfulCategoryᶠ F = record
  { identityˡ = λ {a b} {f} →
      begin
        Fₘ (id ∘ f)
      ≈⟨ F-∘ id f ⟩
        Fₘ id ∘ Fₘ f
      ≈⟨ ∘-resp-≈ˡ F-id  ⟩
        id ∘ Fₘ f
      ≈⟨ identityˡ ⟩
        Fₘ f
      ∎
  ; identityʳ = λ {a b} {f} →
      begin
        Fₘ (f ∘ id)
      ≈⟨ F-∘ f id ⟩
        Fₘ f ∘ Fₘ id
      ≈⟨ ∘-resp-≈ʳ F-id  ⟩
        Fₘ f ∘ id
      ≈⟨ identityʳ ⟩
        Fₘ f
      ∎
  ; assoc = λ {a b c d} {f g h} →
      begin
        Fₘ ((h ∘ g) ∘ f)
      ≈⟨ F-∘ _ _ ⟩
        Fₘ (h ∘ g) ∘ Fₘ f
      ≈⟨ ∘-resp-≈ˡ (F-∘ _ _) ⟩
        (Fₘ h ∘ Fₘ g) ∘ Fₘ f
      ≈⟨ assoc ⟩
        Fₘ h ∘ (Fₘ g ∘ Fₘ f)
      ≈˘⟨ ∘-resp-≈ʳ (F-∘ _ _) ⟩
        Fₘ h ∘ (Fₘ (g ∘ f))
      ≈˘⟨ F-∘ _ _ ⟩
        Fₘ (h ∘ (g ∘ f))
      ∎
  ; ∘-resp-≈ = λ {a b c}{f g h k} h∼k f∼g →
      begin
        Fₘ (h ∘ f)
      ≈⟨ F-∘ h f ⟩
        Fₘ h ∘ Fₘ f
      ≈⟨ ∘-resp-≈ h∼k f∼g ⟩
        Fₘ k ∘ Fₘ g
      ≈˘⟨ F-∘ k g ⟩
        Fₘ (k ∘ g)
      ∎
  }
 where open CategoryH F
       instance f-equiv = F-equiv F
       open ≈-Reasoning

-- TODO: LawfulMonoidalᶠ etc.

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
    ⦃ ⇨cat ⦄ : Category _⇨_
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


record ProductsH {obj₁ : Set o₁} ⦃ prod₁ : Products obj₁ ⦄
                 {obj₂ : Set o₂} ⦃ prod₂ : Products obj₂ ⦄
                 ⦃ homomorphismₒ : Homomorphismₒ obj₁ obj₂ ⦄
       : Set (o₁ ⊔ o₂) where
  open Homomorphismₒ homomorphismₒ -- public
  field
    F-⊤ : Fₒ ⊤ ≡ ⊤
    F-× : ∀ {a b} → Fₒ (a × b) ≡ (Fₒ a × Fₒ b)
    -- TODO: isomorphisms instead of equalities for F-⊤ & F-×?

id-productsH : {obj : Set o} ⦃ prod : Products obj ⦄
             → ProductsH ⦃ homomorphismₒ = id-homomorphismₒ ⦄
id-productsH = record { F-⊤ = refl ; F-× = refl }

record MonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q₂ ⦃ equiv₂ : Equivalent q₂ _⇨₂′_ ⦄
    ⦃ prod₁ : Products obj₁ ⦄ ⦃ cat₁ : Monoidal _⇨₁′_ ⦄
    ⦃ prod₂ : Products obj₂ ⦄ ⦃ cat₂ : Monoidal _⇨₂′_ ⦄
    ⦃ homomorphism : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ categoryH ⦄ : CategoryH _⇨₁_ _⇨₂_ q₂
    ⦃ productsH ⦄ : ProductsH -- obj₁ obj₂
  -- open Homomorphism homomorphism
  open CategoryH categoryH public
  open ProductsH productsH public
  field
    -- F-⊤ : Fₒ ⊤ ≡ ⊤
    -- F-× : ∀ {a b} → Fₒ (a × b) ≡ (Fₒ a × Fₒ b)
    -- -- TODO: isomorphisms instead of equalities for F-⊤ & F-×?
    F-! : ∀ {a} → Fₘ (! {a = a}) ≈ subst′ (Fₒ a ⇨₂_) F-⊤ !
    F-⊗ : ∀ {f : a ⇨₁ c}{g : b ⇨₁ d}
        → Fₘ (f ⊗ g) ≈ subst₂′ _⇨₂_ F-× F-× (Fₘ f ⊗ Fₘ g)

record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ ⇨Monoidal ⦄ : Monoidal _⇨_
    swap : a × b ⇨ b × a

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ′ (inAssocˡ′ swap)

  -- transpose = inAssocʳ (second (inAssocˡ (first swap)))
  -- transpose = assocˡ ∘ second (assocʳ ∘ first swap ∘ assocˡ) ∘ assocʳ

  -- (a × b) × (c × d)
  -- a × (b × (c × d))
  -- a × ((b × c) × d)
  -- a × ((c × b) × d)
  -- a × (c × (b × d))
  -- (a × c) × (b × d)

open Braided ⦃ … ⦄ public

record BraidedH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q₂ ⦃ equiv₂ : Equivalent q₂ _⇨₂′_ ⦄
    ⦃ prod₁ : Products obj₁ ⦄ ⦃ cat₁ : Braided _⇨₁′_ ⦄
    ⦃ prod₂ : Products obj₂ ⦄ ⦃ cat₂ : Braided _⇨₂′_ ⦄
    ⦃ homomorphism : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ monoidalH ⦄ : MonoidalH _⇨₁_ _⇨₂_ q₂
  open MonoidalH monoidalH public
  field
    F-swap : Fₘ (swap {_⇨′_ = _⇨₁_}{a}{b}) ≈ subst₂′ _⇨₂_ F-× F-× swap

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

record CartesianH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                  {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                  q₂ ⦃ equiv₂ : Equivalent q₂ _⇨₂′_ ⦄
                  ⦃ prod₁ : Products obj₁ ⦄ ⦃ cat₁ : Cartesian _⇨₁′_ ⦄
                  ⦃ prod₂ : Products obj₂ ⦄ ⦃ cat₂ : Cartesian _⇨₂′_ ⦄
                  ⦃ homomorphism : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ braidedH ⦄ : BraidedH _⇨₁_ _⇨₂_ q₂
  open BraidedH braidedH public
  field
    F-exl : Fₘ (exl {a = a}{b}) ≈ subst′ (_⇨₂ Fₒ a) F-× exl
    F-exr : Fₘ (exr {a = a}{b}) ≈ subst′ (_⇨₂ Fₒ b) F-× exr
    F-dup : Fₘ (dup {a = a}   ) ≈ subst′ (Fₒ a ⇨₂_) F-× dup


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
    false true : ⊤ ⇨ Bool
    not : Bool ⇨ Bool
    ∧ ∨ xor : Bool × Bool ⇨ Bool
open Logic ⦃ … ⦄ public

record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q₂ ⦃ equiv₂ : Equivalent q₂ _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ homomorphism : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ productsH : ProductsH ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  open Homomorphism homomorphism public
  open ProductsH    productsH    public

  field
    F-Bool : Fₒ Bool ≡ Bool

  F-n⇨1 : Fₒ a ≡ b → (b ⇨₂ Bool) → (Fₒ a ⇨₂ Fₒ Bool)
  F-n⇨1 Fₒa≡b f₂ = subst₂′ _⇨₂_ Fₒa≡b F-Bool f₂

  F-0⇨1 : (⊤ ⇨₂ Bool) → (Fₒ ⊤ ⇨₂ Fₒ Bool)
  F-0⇨1 = F-n⇨1 F-⊤

  F-1⇨1 : (Bool ⇨₂ Bool) → (Fₒ Bool ⇨₂ Fₒ Bool)
  F-1⇨1 = F-n⇨1 F-Bool

  F-2⇨1 : (Bool × Bool ⇨₂ Bool) → (Fₒ (Bool × Bool) ⇨₂ Fₒ Bool)
  F-2⇨1 = F-n⇨1 (trans F-× (cong₂ _×_ F-Bool F-Bool))

  F-n⇨1′ : Fₒ a ≡ b → (Fₒ a ⇨₂ Fₒ Bool) → (b ⇨₂ Bool)
  F-n⇨1′ Fₒa≡b f₂ = subst₂ _⇨₂_ Fₒa≡b F-Bool f₂

  F-0⇨1′ : (Fₒ ⊤ ⇨₂ Fₒ Bool) → (⊤ ⇨₂ Bool)
  F-0⇨1′ = F-n⇨1′ F-⊤

  F-1⇨1′ : (Fₒ Bool ⇨₂ Fₒ Bool) → (Bool ⇨₂ Bool)
  F-1⇨1′ = F-n⇨1′ F-Bool

  F-2⇨1′ : (Fₒ (Bool × Bool) ⇨₂ Fₒ Bool) → (Bool × Bool ⇨₂ Bool)
  F-2⇨1′ = F-n⇨1′ (trans F-× (cong₂ _×_ F-Bool F-Bool))

  field
    F-false : Fₘ false ≈ F-0⇨1 false
    F-true  : Fₘ true  ≈ F-0⇨1 true
    F-not   : Fₘ not   ≈ F-1⇨1 not
    F-∧     : Fₘ ∧     ≈ F-2⇨1 ∧
    F-∨     : Fₘ ∨     ≈ F-2⇨1 ∨
    F-xor   : Fₘ xor   ≈ F-2⇨1 xor

-- I may need to move F-Bool out to a new BooleanH as with ProductsH.
-- If so, bring along F-0⇨1 etc.

record Conditional {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
         (_⇨′_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    cond : Bool × (a × a) ⇨ a
open Conditional ⦃ … ⦄ public

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

    equivalent : Equivalent o Function
    equivalent = record
      { _≈_ = _≗_
      ; equiv = λ {a}{b} → record
          { refl  = λ x → refl
          ; sym   = λ f∼g x → sym (f∼g x)
          ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
          }
      }

    lawful-category : LawfulCategory o Function
    lawful-category = record
      { identityˡ = λ x → refl
      ; identityʳ = λ x → refl
      ; assoc     = λ x → refl
      ; ∘-resp-≈  = λ {a b c}{f g}{h k} h∼k f∼g x
                      → trans (h∼k (f x)) (cong k (f∼g x))
      }

    products : Products (Set o)
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    monoidal : Monoidal (Function {o})
    monoidal = record
                  { _⊗_ = λ f g (x , y) → (f x , g y)
                  ; unitorᵉˡ = λ (tt , y) → y
                  ; unitorᵉʳ = λ (x , tt) → x
                  ; unitorⁱˡ = tt ,_
                  ; unitorⁱʳ = _, tt
                  ; assocʳ   = λ ((x , y) , z) → x , (y , z)
                  ; assocˡ   = λ (x , (y , z)) → (x , y) , z
                  }

    braided : Braided (Function {o})
    braided = record { swap = λ (a , b) → b , a }

    cartesian : Cartesian (Function {o})
    cartesian = record { exl = proj₁ ; exr = proj₂ ; dup = λ z → z , z }

    meaningful : Meaningful (Set ℓ)
    meaningful = record { ⟦_⟧ = id }

    import Data.Bool as B

    boolean : Boolean Set  -- Can I make level-polymorphic?
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

    conditional : Conditional Function
    conditional = record { cond  = λ (c , (a , b)) → B.if c then b else a }

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
  infixl 5 _◂↑_
  _◂↑_ : (a ⇨ b × a) → (n : ℕ) → (a ⇨ V b n × a)
  f ◂↑ zero  = unitorⁱˡ
  f ◂↑ suc n = (f ◂↑ n) ◂ f
