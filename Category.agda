{-# OPTIONS --safe --without-K #-}
-- Some simple category type classes
-- Start with a few laws, and grow from there.

module Category where

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

  subst≈ : ∀ {f g : a ⇨ b} {a≡c : a ≡ c} {b≡d : b ≡ d}
         → f ≈ g → subst₂ _⇨_ a≡c b≡d f ≈ subst₂ _⇨_ a≡c b≡d g
  subst≈ {a≡c = refl} {b≡d = refl} f≈g = f≈g

  -- subst≈′ : ∀ {f g : a ⇨ b} {a≡c : a ≡ c} {b≡d : b ≡ d}
  --         → g ≈ f → subst₂ _⇨_ a≡c b≡d f ≈ subst₂ _⇨_ a≡c b≡d g
  -- subst≈′ g≈f = subst≈ (sym≈ g≈f)
  -- -- subst≈′ a≡c b≡d g≈f = subst≈ a≡c b≡d (sym≈ g≈f)

-- TODO: Replace Equivalent by Setoid?
-- I think we need _⇨_ as an argument rather than field.

open Equivalent ⦃ … ⦄ public

open ≈-Reasoning  -- (not public)

record Homomorphismₒ (obj₁ : Set o₁) (obj₂ : Set o₂) : Set (o₁ ⊔ o₂) where
  field
    Fₒ : obj₁ → obj₂

id-Hₒ : Homomorphismₒ obj obj
id-Hₒ = record { Fₒ = id′ }

record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  open Homomorphismₒ Hₒ public
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

-- open Homomorphism ⦃ … ⦄ public  -- yes or no?

H-equiv : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
          {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
          {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
          ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
          (H : Homomorphism _⇨₁_ _⇨₂_)  -- note explicit/visible argument
        → Equivalent q _⇨₁_
H-equiv H = record { equiv = On.isEquivalence (Homomorphism.Fₘ H) equiv }


record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (lsuc o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)

  subst-id : ∀ {a₁ a₂} {a₁≡a₂ : a₁ ≡ a₂}
             → subst₂ _⇨_ a₁≡a₂ a₁≡a₂ (id {a = a₁}) ≡ id {a = a₂}
  subst-id { a₁≡a₂ = refl } = refl
  -- Useful?

  subst∘ : ∀ {a₁ a₂} {a₁≡a₂ : a₁ ≡ a₂}
             {b₁ b₂} {b₁≡b₂ : b₁ ≡ b₂}
             {c₁ c₂} {c₁≡c₂ : c₁ ≡ c₂}
             {f : a₁ ⇨ b₁}{g : b₁ ⇨ c₁}
         → subst₂ _⇨_ b₁≡b₂ c₁≡c₂ g ∘ subst₂ _⇨_ a₁≡a₂ b₁≡b₂ f
             ≡ subst₂ _⇨_ a₁≡a₂ c₁≡c₂ (g ∘ f)
  subst∘ {a₁≡a₂ = refl} {b₁≡b₂ = refl} {c₁≡c₂ = refl} = refl


open Category ⦃ … ⦄ public

record LawfulCategory {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                      q ⦃ equiv : Equivalent q _⇨′_ ⦄
                      ⦃ ⇨Category : Category _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
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

-- Category homomorphism (functor)
record CategoryH {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
                 {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                 q ⦃ _ : Equivalent q _⇨₂_ ⦄
                 ⦃ _ : Category _⇨₁_ ⦄
                 ⦃ _ : Category _⇨₂_ ⦄
                 ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                 ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  open Homomorphism H public
  field
    F-id : Fₘ {a = a} id ≈ id
    F-∘  : ∀ (g : b ⇨₁ c) (f : a ⇨₁ b) → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

-- open CategoryH ⦃ … ⦄ public

-- I don't know whether to open CategoryH and use it with instances or keep it
-- closed and open explicitly where used. I guess the main question is whether
-- we'll usually have a single special CategoryH instance per pairs of
-- categories or not. For now, keep it explicit, and see what we learn.

LawfulCategoryᶠ : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
                  {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
                  {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
                  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄
                  ⦃ _ : LawfulCategory _⇨₂_ q ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  (F : CategoryH _⇨₁_ _⇨₂_ q)
                → LawfulCategory _⇨₁_ q ⦃ equiv = H-equiv H ⦄
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

-- TODO: LawfulMonoidalᶠ etc.

-- instance
--   ≡-category : Category {obj = Set o} _≡_
--   ≡-category = record { id = refl ; _∘_ = flip trans }

--   open import Relation.Binary.PropositionalEquality.Properties

--   ≡-equiv : Equivalent (lsuc o) {obj = Set o} _≡_
--   ≡-equiv = record { _≈_ = _≡_ ; equiv = isEquivalence }

--   ≡-lawful-category : LawfulCategory (lsuc o) {obj = Set o} _≡_
--   ≡-lawful-category = record
--     { identityˡ = trans-reflʳ _
--     ; identityʳ = refl
--     ; assoc = λ {_ _ _ _}{f} → sym (trans-assoc f)
--     ; ∘-resp-≈ = λ h≡k f≡g → cong₂ trans f≡g h≡k
--     } 


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

  -- mapⱽ : (n : ℕ) → (a ⇨ b) → (V a n ⇨ V b n)
  -- mapⱽ  zero   f = id
  -- mapⱽ (suc n) f = f ⊗ mapⱽ n f

  -- mapᵀ : (n : ℕ) → (a ⇨ b) → (T a n ⇨ T b n)
  -- mapᵀ  zero   f = f
  -- mapᵀ (suc n) f = mapᵀ n f ⊗ mapᵀ n f

open Monoidal ⦃ … ⦄ public

record LawfulMonoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         q ⦃ _ : Equivalent q _⇨′_ ⦄
         ⦃ _ : Monoidal _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ lawful-cat ⦄ : LawfulCategory _⇨_ q

    id⊗id : ∀ {a b : obj} → id {a = a} ⊗ id {a = b} ≈ id

    ∘⊗ : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : obj}
           {f : a₁ ⇨ a₂}{g : b₁ ⇨ b₂}
           {h : a₂ ⇨ a₃}{k : b₂ ⇨ b₃}
       → (h ⊗ k) ∘ (f ⊗ g) ≈ (h ∘ f) ⊗ (k ∘ g)

    unitorᵉˡ∘unitorⁱˡ : ∀ {a : obj} → unitorᵉˡ ∘ unitorⁱˡ {a = a} ≈ id
    unitorⁱˡ∘unitorᵉˡ : ∀ {a : obj} → unitorⁱˡ ∘ unitorᵉˡ {a = a} ≈ id

    unitorᵉʳ∘unitorⁱʳ : ∀ {a : obj} → unitorᵉʳ ∘ unitorⁱʳ {a = a} ≈ id
    unitorⁱʳ∘unitorᵉʳ : ∀ {a : obj} → unitorⁱʳ ∘ unitorᵉʳ {a = a} ≈ id

    assocʳ∘assocˡ : ∀ {a b c : obj} → assocʳ ∘ assocˡ ≈ id {a = a × (b × c)}
    assocˡ∘assocʳ : ∀ {a b c : obj} → assocˡ ∘ assocʳ ≈ id {a = (a × b) × c}

    assocˡ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
             → assocˡ ∘ (f ⊗ (g ⊗ h)) ≈ ((f ⊗ g) ⊗ h) ∘ assocˡ

    ⊗-resp-≈ : ∀ {f h : a ⇨ c} {g k : b ⇨ d} → f ≈ h → g ≈ k → f ⊗ g ≈ h ⊗ k

    assocʳ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
             → assocʳ ∘ ((f ⊗ g) ⊗ h) ≈ (f ⊗ (g ⊗ h)) ∘ assocʳ

  assocˡ∘⊗∘assocʳ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
                  → assocˡ ∘ (f ⊗ (g ⊗ h)) ∘ assocʳ ≈ (f ⊗ g) ⊗ h
  assocˡ∘⊗∘assocʳ {f = f}{g}{h} =
    begin
      assocˡ ∘ (f ⊗ (g ⊗ h)) ∘ assocʳ
    ≈˘⟨ ∘-resp-≈ʳ assocʳ∘⊗ ⟩
      assocˡ ∘ assocʳ ∘ ((f ⊗ g) ⊗ h)
    ≈˘⟨ assoc ⟩
      (assocˡ ∘ assocʳ) ∘ ((f ⊗ g) ⊗ h)
    ≈⟨ ∘-resp-≈ˡ (assocˡ∘assocʳ) ⟩
      id ∘ ((f ⊗ g) ⊗ h)
    ≈⟨ identityˡ ⟩
      (f ⊗ g) ⊗ h
    ∎

  assocʳ∘⊗∘assocˡ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
                  → assocʳ ∘ ((f ⊗ g) ⊗ h) ∘ assocˡ ≈ f ⊗ (g ⊗ h)
  assocʳ∘⊗∘assocˡ {f = f}{g}{h} =
    begin
      assocʳ ∘ ((f ⊗ g) ⊗ h) ∘ assocˡ
    ≈˘⟨ ∘-resp-≈ʳ assocˡ∘⊗ ⟩
      assocʳ ∘ assocˡ ∘ (f ⊗ (g ⊗ h))
    ≈˘⟨ assoc ⟩
      (assocʳ ∘ assocˡ) ∘ (f ⊗ (g ⊗ h))
    ≈⟨ ∘-resp-≈ˡ (assocʳ∘assocˡ) ⟩
      id ∘ (f ⊗ (g ⊗ h))
    ≈⟨ identityˡ ⟩
      f ⊗ (g ⊗ h)
    ∎

  first-first : ∀ {a a′ b c} {f : a ⇨ a′}
              → first {b = c} (first {b = b} f) ≈ assocˡ ∘ first f ∘ assocʳ
  first-first {f = f} =
    begin
      first (first f)
    ≡⟨⟩
      (f ⊗ id) ⊗ id
    ≈˘⟨ assocˡ∘assocʳ ⟩
      assocˡ ∘ (f ⊗ (id ⊗ id)) ∘ assocʳ
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (∘-resp-≈ʳ id⊗id)) ⟩
      assocˡ ∘ (f ⊗ id) ∘ assocʳ
    ≡⟨⟩
      assocˡ ∘ first f ∘ assocʳ
    ∎

  second-second : ∀ {a b c c′} {g : c ⇨ c′}
                → second {a = a} (second {a = b} g) ≈ assocʳ ∘ second g ∘ assocˡ
  second-second {g = g} = ?

  -- second-second {g = g} =
  --   begin
  --     second (second g)
  --   ≡⟨⟩
  --     (g ⊗ id) ⊗ id
  --   ≈˘⟨ assocˡ∘assocʳ ⟩
  --     assocˡ ∘ (g ⊗ (id ⊗ id)) ∘ assocʳ
  --   ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (∘-resp-≈ʳ id⊗id)) ⟩
  --     assocˡ ∘ (g ⊗ id) ∘ assocʳ
  --   ≡⟨⟩
  --     assocˡ ∘ second g ∘ assocʳ
  --   ∎

  ⊗-resp-≈ˡ : ∀ {f : a ⇨ c} {g k : b ⇨ d} → g ≈ k → f ⊗ g ≈ f ⊗ k
  ⊗-resp-≈ˡ g≈k = ⊗-resp-≈ refl≈ g≈k

  ⊗-resp-≈ʳ : ∀ {f h : a ⇨ c} {g : b ⇨ d} → f ≈ h → f ⊗ g ≈ h ⊗ g
  ⊗-resp-≈ʳ f≈h = ⊗-resp-≈ f≈h refl≈

  first∘second : ∀ {a b c d : obj} {f : a ⇨ c} {g : b ⇨ d}
               → first f ∘ second g ≈ f ⊗ g
  first∘second {f = f}{g = g} =
    begin
      first f ∘ second g
    ≡⟨⟩
      (f ⊗ id) ∘ (id ⊗ g)
    ≈⟨ ∘⊗ ⟩
      (f ∘ id) ⊗ (id ∘ g)
    ≈⟨ ⊗-resp-≈ identityʳ identityˡ ⟩
      f ⊗ g
    ∎

  second∘first : ∀ {a b c d : obj} {f : a ⇨ c} {g : b ⇨ d}
               → second g ∘ first f ≈ f ⊗ g
  second∘first {f = f}{g = g} =
    begin
      second g ∘ first f
    ≡⟨⟩
      (id ⊗ g) ∘ (f ⊗ id)
    ≈⟨ ∘⊗ ⟩
      (id ∘ f) ⊗ (g ∘ id)
    ≈⟨ ⊗-resp-≈ identityˡ identityʳ ⟩
      f ⊗ g
    ∎

  first∘first : ∀ {f : a ⇨ b} {g : b ⇨ c} {z : obj}
              → first g ∘ first f ≈ first {b = z} (g ∘ f)
  first∘first {f = f}{g} =
    begin
      first g ∘ first f
    ≡⟨⟩
      (g ⊗ id) ∘ (f ⊗ id)
    ≈⟨ ∘⊗ ⟩
     (g ∘ f) ⊗ (id ∘ id)
    ≈⟨ ⊗-resp-≈ˡ identityʳ ⟩
      (g ∘ f) ⊗ id
    ≡⟨⟩
      first (g ∘ f)
    ∎

  second∘second : ∀ {f : a ⇨ b} {g : b ⇨ c} {z : obj}
                → second g ∘ second f ≈ second {a = z} (g ∘ f)
  second∘second {f = f}{g} =
    begin
      second g ∘ second f
    ≡⟨⟩
      (id ⊗ g) ∘ (id ⊗ f)
    ≈⟨ ∘⊗ ⟩
     (id ∘ id) ⊗ (g ∘ f)
    ≈⟨ ⊗-resp-≈ʳ identityʳ ⟩
      id ⊗ (g ∘ f)
    ≡⟨⟩
      second (g ∘ f)
    ∎

open LawfulMonoidal ⦃ … ⦄ public

-- I don't think there's a Monoidal instance for _≡_

record ProductsH {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄
                 {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
                 (Hₒ : Homomorphismₒ obj₁ obj₂)
       : Set (o₁ ⊔ o₂) where
  open Homomorphismₒ Hₒ -- public
  field
    F-⊤ : Fₒ ⊤ ≡ ⊤
    F-× : ∀ {a b} → Fₒ (a × b) ≡ (Fₒ a × Fₒ b)
    -- TODO: isomorphisms instead of equalities for F-⊤ & F-×?
    -- Equality seems to be working out and is easier to manage.

id-productsH : {obj : Set o} ⦃ _ : Products obj ⦄ → ProductsH id-Hₒ
id-productsH = record { F-⊤ = refl ; F-× = refl }

-- Helpers for monoidal operations with homomorphisms.
-- Needs a better module name and some experience using it.
module ᴴ
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)(let infix 0 _⇨₂_; _⇨₂_ = _⇨₂_)
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ productsH : ProductsH Hₒ ⦄
 where
  open ProductsH productsH
  open Homomorphismₒ Hₒ

  !ᴴ : ∀ {a : obj₁} → Fₒ a ⇨₂ Fₒ ⊤
  !ᴴ {a} = subst′ (Fₒ a ⇨₂_) F-⊤ !

  infixr 7 _⊗ᴴ_
  _⊗ᴴ_ : (f : Fₒ a ⇨₂ Fₒ c) (g : Fₒ b ⇨₂ Fₒ d) → Fₒ (a × b) ⇨₂ Fₒ (c × d)
  f ⊗ᴴ g = subst₂′ _⇨₂_ F-× F-× (f ⊗ g)

  firstᴴ  : (f : Fₒ a ⇨₂ Fₒ c) → Fₒ (a × b) ⇨₂ Fₒ (c × b)
  firstᴴ  f = f ⊗ᴴ id

  secondᴴ : (g : Fₒ b ⇨₂ Fₒ d) → Fₒ (a × b) ⇨₂ Fₒ (a × d)
  secondᴴ g = id ⊗ᴴ g

  unitorᴴᵉˡ : Fₒ (⊤ × a) ⇨₂ Fₒ a
  unitorᴴᵉˡ {a} = subst′ (_⇨₂ Fₒ a) (trans F-× (cong (_× Fₒ a) F-⊤)) unitorᵉˡ

  unitorᴴᵉʳ : Fₒ (a × ⊤) ⇨₂ Fₒ a
  unitorᴴᵉʳ {a} = subst′ (_⇨₂ Fₒ a) (trans F-× (cong (Fₒ a ×_) F-⊤)) unitorᵉʳ

  unitorᴴⁱˡ : Fₒ a ⇨₂ Fₒ (⊤ × a)
  unitorᴴⁱˡ {a} = subst′ (Fₒ a ⇨₂_) (trans F-× (cong (_× Fₒ a) F-⊤)) unitorⁱˡ

  unitorᴴⁱʳ : Fₒ a ⇨₂ Fₒ (a × ⊤)
  unitorᴴⁱʳ {a} = subst′ (Fₒ a ⇨₂_) (trans F-× (cong (Fₒ a ×_) F-⊤)) unitorⁱʳ

  assocᴴʳ : Fₒ ((a × b) × c) ⇨₂ Fₒ (a × (b × c))
  assocᴴʳ {a}{b}{c} = subst₂′ _⇨₂_ (trans F-× (cong (_× Fₒ c) F-×))
                                   (trans F-× (cong (Fₒ a ×_) F-×))
                                   assocʳ

  assocᴴˡ : Fₒ (a × (b × c)) ⇨₂ Fₒ ((a × b) × c)
  assocᴴˡ {a}{b}{c} = subst₂′ _⇨₂_ (trans F-× (cong (Fₒ a ×_) F-×))
                                   (trans F-× (cong (_× Fₒ c) F-×))
                                   assocˡ

  -- To do: Is there a suitable category for easing these substitutions?

module Lawfulᴴ
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)(let infix 0 _⇨₂_; _⇨₂_ = _⇨₂_)
    ⦃ _ : Products obj₂ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ productsH : ProductsH Hₒ ⦄
    q ⦃ equiv : Equivalent q _⇨₂_ ⦄
    ⦃ _ : Monoidal _⇨₂_ ⦄ ⦃ _ : LawfulMonoidal _⇨₂_ q ⦄
 where
  open ProductsH productsH
  open Homomorphismₒ Hₒ
  open ᴴ obj₁ _⇨₂_

  ⊗ᴴ-resp-≈ : ∀ {f h : Fₒ a ⇨₂ Fₒ c} {g k : Fₒ b ⇨₂ Fₒ d}
            → f ≈ h → g ≈ k → f ⊗ᴴ g ≈ h ⊗ᴴ k
  ⊗ᴴ-resp-≈ f≈h g≈k = subst≈ (⊗-resp-≈ f≈h g≈k)

  ⊗ᴴ-resp-≈ˡ : ∀ {f h : Fₒ a ⇨₂ Fₒ c} {g : Fₒ b ⇨₂ Fₒ d}
             → f ≈ h → f ⊗ᴴ g ≈ h ⊗ᴴ g
  ⊗ᴴ-resp-≈ˡ f≈h = ⊗ᴴ-resp-≈ f≈h refl≈

  ⊗ᴴ-resp-≈ʳ : ∀ {f : Fₒ a ⇨₂ Fₒ c} {g k : Fₒ b ⇨₂ Fₒ d}
             → g ≈ k → f ⊗ᴴ g ≈ f ⊗ᴴ k
  ⊗ᴴ-resp-≈ʳ g≈k = ⊗ᴴ-resp-≈ refl≈ g≈k

  first∘secondᴴ : ∀ {a b c d} {f : Fₒ a ⇨₂ Fₒ c} {g : Fₒ b ⇨₂ Fₒ d}
                → firstᴴ f ∘ secondᴴ g ≈ f ⊗ᴴ g
  first∘secondᴴ {f = f}{g = g} =
    begin
      firstᴴ f ∘ secondᴴ g
    ≡⟨⟩
       subst₂′ _⇨₂_ F-× F-× (first f) ∘ subst₂′ _⇨₂_ F-× F-× (second g)
    ≡⟨ subst∘ ⟩
       subst₂′ _⇨₂_ F-× F-× (first f ∘ second g)
    ≈⟨ subst≈ first∘second ⟩
       subst₂′ _⇨₂_ F-× F-× (f ⊗ g)
    ≡⟨⟩
      f ⊗ᴴ g
    ∎

  second∘firstᴴ : ∀ {a b c d} {f : Fₒ a ⇨₂ Fₒ c} {g : Fₒ b ⇨₂ Fₒ d}
                → secondᴴ g ∘ firstᴴ f ≈ f ⊗ᴴ g
  second∘firstᴴ {f = f}{g = g} =
    begin
      secondᴴ g ∘ firstᴴ f
    ≡⟨⟩
       (subst₂′ _⇨₂_ F-× F-× (second g)) ∘ (subst₂′ _⇨₂_ F-× F-× (first f))
    ≡⟨ subst∘ ⟩
       subst₂′ _⇨₂_ F-× F-× (second g ∘ first f)
    ≈⟨ subst≈ second∘first ⟩
       subst₂′ _⇨₂_ F-× F-× (f ⊗ g)
    ≡⟨⟩
      f ⊗ᴴ g
    ∎

  first∘firstᴴ : ∀ {f : Fₒ a ⇨₂ Fₒ b} {g : Fₒ b ⇨₂ Fₒ c} {z}
               → firstᴴ g ∘ firstᴴ f ≈ firstᴴ {b = z} (g ∘ f)
  first∘firstᴴ {f = f}{g} =
    begin
      firstᴴ g ∘ firstᴴ f
    ≡⟨⟩
       (subst₂′ _⇨₂_ F-× F-× (first g)) ∘ (subst₂′ _⇨₂_ F-× F-× (first f))
    ≡⟨ subst∘ ⟩
       subst₂′ _⇨₂_ F-× F-× (first g ∘ first f)
    ≈⟨ subst≈ first∘first ⟩
       subst₂′ _⇨₂_ F-× F-× (first (g ∘ f))
    ≡⟨⟩
      firstᴴ (g ∘ f)
    ∎

  second∘secondᴴ : ∀ {f : Fₒ a ⇨₂ Fₒ b} {g : Fₒ b ⇨₂ Fₒ c} {z}
                 → secondᴴ g ∘ secondᴴ f ≈ secondᴴ {a = z} (g ∘ f)
  second∘secondᴴ {f = f}{g} =
    begin
      secondᴴ g ∘ secondᴴ f
    ≡⟨⟩
       (subst₂′ _⇨₂_ F-× F-× (second g)) ∘ (subst₂′ _⇨₂_ F-× F-× (second f))
    ≡⟨ subst∘ ⟩
       subst₂′ _⇨₂_ F-× F-× (second g ∘ second f)
    ≈⟨ subst≈ second∘second ⟩
       subst₂′ _⇨₂_ F-× F-× (second (g ∘ f))
    ≡⟨⟩
      secondᴴ (g ∘ f)
    ∎

  -- TODO: Refactor these last few to make them all one-liners.


record MonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂′_ ⦄ ⦃ _ : LawfulMonoidal _⇨₂′_ q ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ -categoryH ⦄ : CategoryH _⇨₁_ _⇨₂_ q
    ⦃ -productsH ⦄ : ProductsH Hₒ
  open CategoryH -categoryH public
  open ProductsH -productsH public
  -- open Homomorphismₒ Hₒ
  open ᴴ obj₁ _⇨₂_
  open Lawfulᴴ obj₁ _⇨₂_ q
  field
    F-! : Fₘ (! {a = a}) ≈ !ᴴ {a}
    F-⊗ : ∀ (f : a ⇨₁ c)(g : b ⇨₁ d) → Fₘ (f ⊗ g) ≈ Fₘ f ⊗ᴴ Fₘ g

    F-unitorᵉˡ : Fₘ unitorᵉˡ ≈ unitorᴴᵉˡ {a}
    F-unitorⁱˡ : Fₘ unitorⁱˡ ≈ unitorᴴⁱˡ {a}
    F-unitorᵉʳ : Fₘ unitorᵉʳ ≈ unitorᴴᵉʳ {a}
    F-unitorⁱʳ : Fₘ unitorⁱʳ ≈ unitorᴴⁱʳ {a}

    F-assocˡ : Fₘ assocˡ ≈ assocᴴˡ {a}{b}{c}
    F-assocʳ : Fₘ assocʳ ≈ assocᴴʳ {a}{b}{c}

  F-first  : ∀ {b : obj₁}(f : a ⇨₁ c) → Fₘ (first {b = b} f) ≈ firstᴴ (Fₘ f)
  F-first f =
    begin
      Fₘ (first f)
    ≡⟨⟩
      Fₘ (f ⊗ id)
    ≈⟨ F-⊗ f id ⟩
      Fₘ f ⊗ᴴ Fₘ id
    ≈⟨ ⊗ᴴ-resp-≈ʳ F-id ⟩
      Fₘ f ⊗ᴴ id
    ≡⟨⟩
      firstᴴ (Fₘ f)
    ∎

  F-second  : ∀ {a : obj₁}(g : b ⇨₁ d) → Fₘ (second {a = a} g) ≈ secondᴴ (Fₘ g)
  F-second g =
    begin
      Fₘ (second g)
    ≡⟨⟩
      Fₘ (id ⊗ g)
    ≈⟨ F-⊗ id g ⟩
      Fₘ id ⊗ᴴ Fₘ g
    ≈⟨ ⊗ᴴ-resp-≈ˡ F-id ⟩
      id ⊗ᴴ Fₘ g
    ≡⟨⟩
      secondᴴ (Fₘ g)
    ∎


-- LawfulMonoidalᶠ : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
--                   {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
--                   {q : Level} ⦃ equiv₂ : Equivalent q _⇨₂_ ⦄
--                   ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁_ ⦄
--                   ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂_ ⦄
--                   ⦃ _ : LawfulMonoidal q _⇨₂_ ⦄
--                   ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
--                   ⦃ _ : Equivalent q _⇨₁_ ⦄
--                   -- Uh oh. LawfulCategory and Monoidal both carry a category
--                   ⦃ lawful-cat₁ : LawfulCategory q _⇨₁_ ⦄
--                   ⦃ lawful-cat₂ : LawfulCategory q _⇨₂_ ⦃ equiv = equiv₂ ⦄ ⦄
--                   (F : MonoidalH _⇨₁_ _⇨₂_ q
--                                  ⦃ equiv₂ = equiv₂ ⦄ ⦃ monoidal₂ = monoidal₂ ⦄)
--                 → LawfulMonoidal q _⇨₁_
-- LawfulMonoidalᶠ F = record
--   { unitorᵉˡ∘unitorⁱˡ = λ {a} → {!!}
--       -- {!!}
--       -- begin
--       --   Fₘ (unitorᵉˡ ∘ unitorⁱˡ {a = a})
--       -- ≈⟨ F-∘ unitorᵉˡ unitorⁱˡ ⟩
--       --   Fₘ unitorᵉˡ ∘ Fₘ (unitorⁱˡ {a = a})
--       -- ≈⟨ ∘-resp-≈ F-unitorᵉˡ F-unitorⁱˡ ⟩
--       --   unitorᵉˡ ∘ unitorⁱˡ {a = a}
--       -- ≈⟨ {!!} ⟩
--       --   id
--       -- ≈˘⟨ F-id ⟩
--       --   Fₘ id
--       -- ∎
--   ; unitorⁱˡ∘unitorᵉˡ = {!!}
--   ; unitorᵉʳ∘unitorⁱʳ = {!!}
--   ; unitorⁱʳ∘unitorᵉʳ = {!!}
--   }
--  where open MonoidalH F
--        -- instance _ = H-equiv ⦃ equiv₂ = equiv₂ ⦄ H


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

record LawfulBraided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         q ⦃ _ : Equivalent q _⇨′_ ⦄
         ⦃ _ : Braided _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ lawful-monoidal ⦄ : LawfulMonoidal _⇨_ q
    -- Laws go here

record BraidedH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Braided _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Braided _⇨₂′_ ⦄ ⦃ _ : LawfulBraided _⇨₂′_ q ⦄
    ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ monoidalH ⦄ : MonoidalH _⇨₁_ _⇨₂_ q
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

record LawfulCartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         q ⦃ _ : Equivalent q _⇨′_ ⦄
         ⦃ _ : Cartesian _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ lawful-braided ⦄ : LawfulBraided _⇨_ q
    -- Laws go here

record CartesianH
  {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
  q ⦃ _ : Equivalent q _⇨₂′_ ⦄
  ⦃ _ : Products obj₁ ⦄ ⦃ _ : Cartesian _⇨₁′_ ⦄
  ⦃ _ : Products obj₂ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄ ⦃ _ : LawfulCartesian _⇨₂′_ q ⦄
  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
  ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ braidedH ⦄ : BraidedH _⇨₁_ _⇨₂_ q
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
    cond : Bool × (a × a) ⇨ a
open Logic ⦃ … ⦄ public

record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ productsH : ProductsH Hₒ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  open Homomorphism H public
  open ProductsH productsH public

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

    lawful-category : LawfulCategory Function o
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
              ; cond  = λ (c , (a , b)) → B.if c then b else a
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
  ⦃ _ : Cartesian _⇨_ ⦄ where

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

