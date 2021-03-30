{-# OPTIONS --safe --without-K #-}

module Ty where

open import Data.Unit renaming (⊤ to ⊤ᵗ) public
open import Data.Bool using () renaming (Bool to Boolᵗ) public
open import Data.Product using (_,_; uncurry) renaming (_×_ to _×ᵗ_) public

import Misc as F

infixr 2 _×_
data Ty : Set where
  ⊤    : Ty
  Bool : Ty
  _×_  : Ty → Ty → Ty

private variable A B C D : Ty

⟦_⟧ᵗ : Ty → Set
⟦ ⊤ ⟧ᵗ     = ⊤ᵗ
⟦ σ × τ ⟧ᵗ = ⟦ σ ⟧ᵗ ×ᵗ ⟦ τ ⟧ᵗ
⟦ Bool ⟧ᵗ  = Boolᵗ

infix 0 _→ᵗ_
_→ᵗ_ : Ty → Ty → Set
A →ᵗ B = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

-- Index of a bit in a type
data BitIx : Ty → Set where
  here : BitIx Bool
  left  : BitIx A → BitIx (A × B)
  right : BitIx B → BitIx (A × B)

-- Extract a bit
⟦_⟧ᵇ : ∀ {A} → BitIx A → A →ᵗ Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

tabulate : (BitIx A → Boolᵗ) → ⟦ A ⟧ᵗ
tabulate {⊤} f = tt
tabulate {Bool} f = f here
tabulate {_ × _} f = tabulate (f F.∘ left) , tabulate (f F.∘ right)

lookup : ⟦ A ⟧ᵗ → (BitIx A → Boolᵗ)
lookup a i = ⟦ i ⟧ᵇ a

private variable X : Set

-- Ty-indexed container
data BitF (X : Set) : Ty → Set where
  unit : BitF X ⊤
  bit  : X → BitF X Bool
  pair : BitF X A → BitF X B → BitF X (A × B)

tabulate′ : (BitIx A → X) → BitF X A
tabulate′ {⊤} f = unit
tabulate′ {Bool} f = bit (f here)
tabulate′ {_ × _} f = pair (tabulate′ (f F.∘ left)) (tabulate′ (f F.∘ right))

lookup′ : BitF X A → (BitIx A → X)
lookup′ (bit x) here = x
lookup′ (pair l r) (left  a) = lookup′ l a
lookup′ (pair l r) (right b) = lookup′ r b

swizzleF : (BitIx B → BitIx A) → BitF X A → BitF X B
swizzleF r a = tabulate′ (lookup′ a F.∘ r)

→BitF : ⟦ A ⟧ᵗ → BitF Boolᵗ A
→BitF {⊤} tt = unit
→BitF {Bool} b = bit b
→BitF {_ × _} (x , y) = pair (→BitF x) (→BitF y)

BitF→ : BitF Boolᵗ A → ⟦ A ⟧ᵗ
BitF→ unit = tt
BitF→ (bit b) = b
BitF→ (pair x y) = BitF→ x , BitF→ y

-- Agsy synthesized all of the BitF operations above. (Tidying needed for most,
-- -c for all but swizzleF, and tabulate′ and lookup′ hints for swizzleF.)

-- Relate Ty values to vectors

open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties using (++-injective)
open import Function using (_↔_; mk↔′)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

size : Ty → ℕ
size ⊤       = 0
size Bool    = 1
size (A × B) = size A + size B

→Vec : ⟦ A ⟧ᵗ → Vec Boolᵗ (size A)
→Vec {⊤} tt = []
→Vec {Bool} b = b ∷ []
→Vec {_ × _} (x , y) = →Vec x ++ →Vec y

Vec→ : Vec Boolᵗ (size A) → ⟦ A ⟧ᵗ
Vec→ {⊤} [] = tt
Vec→ {Bool} (b ∷ []) = b
Vec→ {A × B} bs = let u , v , _ = splitAt (size A) bs in Vec→ u , Vec→ v

→Vec∘Vec→ : ∀ (bs : Vec Boolᵗ (size A)) → →Vec (Vec→ {A} bs) ≡ bs
→Vec∘Vec→ {⊤} [] = refl
→Vec∘Vec→ {Bool} (b ∷ []) = refl
→Vec∘Vec→ {A × B} uv with splitAt (size A) uv
... | u , v , refl = cong₂ _++_ (→Vec∘Vec→ {A} u) (→Vec∘Vec→ {B} v)

{-
-- In progress
Vec→∘→Vec : ∀ (x : ⟦ A ⟧ᵗ) → Vec→ (→Vec x) ≡ x
Vec→∘→Vec {⊤} tt = refl
Vec→∘→Vec {Bool} b = refl
Vec→∘→Vec {A × B} (x , y) =
  let u , v , eq = splitAt (size A) (→Vec x ++ →Vec y)
      →Vec_x≡u , →Vec_y≡v = ++-injective (→Vec x) u eq in
    begin
      Vec→ (→Vec (x , y))
    ≡⟨⟩
      Vec→ (→Vec x ++ →Vec y)
    ≡⟨ cong₂ (λ u v → Vec→ (u ++ v)) →Vec_x≡u →Vec_y≡v ⟩
      Vec→ (u ++ v)
    ≡⟨ {!!} ⟩
      Vec→ (→Vec x) , Vec→ (→Vec y)
    ≡⟨ cong₂ _,_ (Vec→∘→Vec {A} x) (Vec→∘→Vec {B} y) ⟩
      x , y
    ∎

↔Vec : ⟦ A ⟧ᵗ ↔ Vec Boolᵗ (size A)
↔Vec {A} = mk↔′ →Vec Vec→ (→Vec∘Vec→ {A}) (Vec→∘→Vec {A})
-}

-- TODO: rework ↔Vec as a equational style proof.


-- TODO: Maybe phase out BitIx and ⟦_⟧ᵇ. More likely, drop its
-- generalization below.

-- Index of a subvalue in a type
infix 1 _∈ᵗ_
data _∈ᵗ_ : Ty → Ty → Set where
  here  : A ∈ᵗ A
  left  : A ∈ᵗ B → A ∈ᵗ B × C
  right : A ∈ᵗ C → A ∈ᵗ B × C

-- Extract a subvalue
⟦_∈ᵗ⟧ : ∀ {A} → B ∈ᵗ A → A →ᵗ B
⟦ here    ∈ᵗ⟧ = F.id
⟦ left  i ∈ᵗ⟧ = ⟦ i ∈ᵗ⟧ F.∘ F.exl
⟦ right i ∈ᵗ⟧ = ⟦ i ∈ᵗ⟧ F.∘ F.exr

-- ⟦ here    ∈ᵗ⟧ x = x
-- ⟦ left  i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ x
-- ⟦ right i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ y

infixr 9 _∘∈ᵗ_
_∘∈ᵗ_ : B ∈ᵗ C → A ∈ᵗ B → A ∈ᵗ C
here    ∘∈ᵗ f = f
left  i ∘∈ᵗ f = left  (i ∘∈ᵗ f)
right i ∘∈ᵗ f = right (i ∘∈ᵗ f)
-- Fully synthesized from {! -c !}

-- TODO: Prove that ⟦_∈ᵗ⟧  is a functor. Probably easy.
