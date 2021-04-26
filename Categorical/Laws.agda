{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function using (_∘′_; const; _on_; flip; case_of_) renaming (id to id′)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR
import Relation.Binary.Construct.On as On

open import Miscellany
open import Categorical.Raw

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

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

  assoc-middle : {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{k : d ⇨ e}
               → (k ∘ h) ∘ (g ∘ f) ≈ k ∘ (h ∘ g) ∘ f
  assoc-middle = trans≈ assoc (∘-resp-≈ʳ (sym≈ assoc))

open LawfulCategory ⦃ … ⦄ public


record LawfulMonoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         q ⦃ equiv : Equivalent q _⇨′_ ⦄
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

    assocʳ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
             → assocʳ ∘ ((f ⊗ g) ⊗ h) ≈ (f ⊗ (g ⊗ h)) ∘ assocʳ

    ⊗-resp-≈ : ∀ {f h : a ⇨ c} {g k : b ⇨ d} (f≈h : f ≈ h) (g≈k : g ≈ k) → f ⊗ g ≈ h ⊗ k

  ⊗-resp-≈ʳ : ∀ {f : a ⇨ c} {g k : b ⇨ d} → g ≈ k → f ⊗ g ≈ f ⊗ k
  ⊗-resp-≈ʳ g≈k = ⊗-resp-≈ refl≈ g≈k

  ⊗-resp-≈ˡ : ∀ {f h : a ⇨ c} {g : b ⇨ d} → f ≈ h → f ⊗ g ≈ h ⊗ g
  ⊗-resp-≈ˡ f≈h = ⊗-resp-≈ f≈h refl≈

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
    ≈⟨ ⊗-resp-≈ʳ identityʳ ⟩
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
    ≈⟨ ⊗-resp-≈ˡ identityʳ ⟩
      id ⊗ (g ∘ f)
    ≡⟨⟩
      second (g ∘ f)
    ∎

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

  first-first : ∀ {a a′ b c : obj} {f : a ⇨ a′}
              → first {b = c} (first {b = b} f) ≈ assocˡ ∘ first f ∘ assocʳ
  first-first {f = f} =
    begin
      first (first f)
    ≡⟨⟩
      (f ⊗ id) ⊗ id
    ≈˘⟨ assocˡ∘⊗∘assocʳ ⟩
      assocˡ ∘ (f ⊗ (id ⊗ id)) ∘ assocʳ
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ id⊗id)) ⟩
      assocˡ ∘ (f ⊗ id) ∘ assocʳ
    ≡⟨⟩
      assocˡ ∘ first f ∘ assocʳ
    ∎

  second-second : ∀ {a b c c′ : obj} {g : c ⇨ c′}
                → second {a = a} (second {a = b} g) ≈ assocʳ ∘ second g ∘ assocˡ
  second-second {g = g} =
    begin
      second (second g)
    ≡⟨⟩
      id ⊗ (id ⊗ g)
    ≈˘⟨ assocʳ∘⊗∘assocˡ ⟩
      assocʳ ∘ ((id ⊗ id) ⊗ g) ∘ assocˡ
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ id⊗id)) ⟩
      assocʳ ∘ (id ⊗ g) ∘ assocˡ
    ≡⟨⟩
      assocʳ ∘ second g ∘ assocˡ
    ∎

open LawfulMonoidal ⦃ … ⦄ public
