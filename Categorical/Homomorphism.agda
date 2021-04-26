{-# OPTIONS --safe --without-K #-}

module Categorical.Homomorphism where

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

open import Categorical.Raw

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

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


record ProductsH
    {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ equiv₂ : Equivalent q _⇨₂′_ ⦄
    -- ⦃ cat₁ : Category _⇨₁′_ ⦄
    ⦃ cat₂ : Category _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  open Homomorphismₒ Hₒ -- public
  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    -- *Strong*
    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b

    ε∘ε⁻¹ : ε ∘ ε⁻¹ ≈ id
    ε⁻¹∘ε : ε⁻¹ ∘ ε ≈ id

    μ∘μ⁻¹ : μ{a}{b} ∘ μ⁻¹ ≈ id
    μ⁻¹∘μ : μ⁻¹{a}{b} ∘ μ ≈ id

    -- TODO: Package as isomorphisms.

record MonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ -categoryH ⦄ : CategoryH _⇨₁_ _⇨₂_ q
  open CategoryH -categoryH public
  open ProductsH pH public
  -- open Homomorphismₒ Hₒ

  field
    F-unitorᵉˡ : Fₘ unitorᵉˡ ∘ μ{⊤}{a} ∘ first  ε ≈ unitorᵉˡ
    F-unitorⁱˡ : Fₘ unitorⁱˡ ≈ μ{⊤}{a} ∘ first  ε ∘ unitorⁱˡ
    F-unitorᵉʳ : Fₘ unitorᵉʳ ∘ μ{a}{⊤} ∘ second ε ≈ unitorᵉʳ
    F-unitorⁱʳ : Fₘ unitorⁱʳ ≈ μ{a}{⊤} ∘ second ε ∘ unitorⁱʳ

    F-assocˡ :
      Fₘ assocˡ ∘ μ{a}{b × c} ∘ second μ ≈ μ{a × b}{c} ∘ first  μ ∘ assocˡ
    F-assocʳ :
      Fₘ assocʳ ∘ μ{a × b}{c} ∘ first  μ ≈ μ{a}{b × c} ∘ second μ ∘ assocʳ

    -- Are the next two properties theorems? I don't see them on nlab.
    F-! : Fₘ {a} ! ≈ ε ∘ !
    F-⊗ : ∀ (f : a ⇨₁ c)(g : b ⇨₁ d) → Fₘ (f ⊗ g) ∘ μ ≈ μ ∘ (Fₘ f ⊗ Fₘ g)


record BraidedH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                q ⦃ _ : Equivalent q _⇨₂′_ ⦄
                ⦃ _ : Products obj₁ ⦄ ⦃ _ : Braided _⇨₁′_ ⦄
                ⦃ _ : Products obj₂ ⦄ ⦃ _ : Braided _⇨₂′_ ⦄
                ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
                ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ monoidalH ⦄ : MonoidalH _⇨₁_ _⇨₂_ q
  -- open ProductsH pH
  open MonoidalH monoidalH public
  field
    F-swap : Fₘ swap ∘ μ{a}{b} ≈ μ{b}{a} ∘ swap

record CartesianH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                  {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                  q ⦃ _ : Equivalent q _⇨₂′_ ⦄
                  ⦃ _ : Products obj₁ ⦄ ⦃ _ : Cartesian _⇨₁′_ ⦄
                  ⦃ _ : Products obj₂ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
                  ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ braidedH ⦄ : BraidedH _⇨₁_ _⇨₂_ q
  -- open ProductsH pH
  open BraidedH braidedH public
  field
    F-exl : Fₘ exl ∘ μ{a}{b} ≈ exl
    F-exr : Fₘ exr ∘ μ{a}{b} ≈ exr
    F-dup : Fₘ dup ≈ μ{a}{a} ∘ dup


record BooleanH
    {obj₁ : Set o₁} ⦃ _ : Boolean obj₁ ⦄ (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  open Homomorphismₒ Hₒ public
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β : Bool ⇨₂ Fₒ Bool

record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ _ : Monoidal _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄ ⦃ bH : BooleanH _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  open Homomorphism H public
  open ProductsH pH
  open BooleanH  bH

  field
    F-false : Fₘ false ∘ ε ≈ β ∘ false
    F-true  : Fₘ true  ∘ ε ≈ β ∘ true
    F-not   : Fₘ not   ∘ β ≈ β ∘ not
    F-∧     : Fₘ ∧   ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∧
    F-∨     : Fₘ ∨   ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∨
    F-xor   : Fₘ xor ∘ μ ∘ (β ⊗ β) ≈ β ∘ xor
