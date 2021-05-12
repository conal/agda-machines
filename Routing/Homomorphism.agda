{-# OPTIONS --safe --without-K #-}

-- TODO: parametrize module by level

module Routing.Homomorphism where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categorical.Raw
open import Categorical.Homomorphism

open import Miscellany using (Function)
open import Categorical.Instances.Function.Raw  0ℓ
open import Categorical.Instances.Function.Laws 0ℓ

-- open import Categorical.Instances.Setoid.Raw  0ℓ
-- open import Categorical.Instances.Setoid.Laws 0ℓ

open import Ty

-- open import Typed.Raw _⟶_ renaming (_⇨_ to _⇨ₜ_)
-- open import Typed.Homomorphism _⟶_ 0ℓ
-- open import Typed.Laws         _⟶_ 0ℓ

open import Typed.Raw (Function {0ℓ}) renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism (Function {0ℓ}) 0ℓ
open import Typed.Laws         (Function {0ℓ}) 0ℓ

-- -- I don't know why the following alternative leads to problems
-- open import Typed (Function {0ℓ}) 0ℓ renaming (_⇨_ to _⇨ₜ_)

open import Routing.Raw

private variable a b c d : Ty

eqᵗ : ∀ a → ⟦ a ⟧ → ⟦ a ⟧ → Set
eqᵗ `⊤ = _≡_
eqᵗ `Bool = _≡_
eqᵗ (a `× b) (x , y) (x′ , y′) = eqᵗ a x x′ × eqᵗ b y y′
eqᵗ (a `⇛ b) f g = ∀ {x} → eqᵗ b (f x) (g x)

infix 4 eqᵗ-syntax
eqᵗ-syntax : ∀ a → ⟦ a ⟧ → ⟦ a ⟧ → Set
eqᵗ-syntax = eqᵗ

syntax eqᵗ-syntax a x y = x ≈[ a ] y

-- infix 4 _≈ᵗ_
-- _≈ᵗ_ : ⟦ a ⟧ → ⟦ a ⟧ → Set
-- _≈ᵗ_ {a} = eqᵗ a

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties as EP
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-isEquivalence)

isEquiv : ∀ a → IsEquivalence (eqᵗ a)
isEquiv `⊤       = EP.isEquivalence
isEquiv `Bool    = EP.isEquivalence
isEquiv (a `× b) = ×-isEquivalence (isEquiv a) (isEquiv b)
isEquiv (_ `⇛ b) = record
  { refl  =             b.refl
  ; sym   = λ f≈g     → b.sym f≈g
  ; trans = λ f≈g g≈h → b.trans f≈g g≈h
  }
 where module b = IsEquivalence (isEquiv b)
-- Is function-lifting of IsEquivalence already defined somewhere?

lookup : ⟦ a ⟧ → (TyIx a → Bool)
lookup x       here      = x
lookup (x , y) (left  i) = lookup x i
lookup (x , y) (right j) = lookup y j
lookup f       (arg x i) = lookup (f x) i

tabulate : (TyIx a → Bool) → ⟦ a ⟧
tabulate {`⊤}     f = tt
tabulate {`Bool}  f = f here
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)
tabulate {a `⇛ b} f = λ z → tabulate (f ∘ arg z)

--   arg : ⟦ a ⟧ → TyIx b → TyIx (a ⇛ b)

-- tabulate∘lookup : ∀ a {x : ⟦ a ⟧} → eqᵗ a (tabulate {a = a} (lookup x)) x
tabulate∘lookup : ∀ a {x : ⟦ a ⟧} → tabulate {a = a} (lookup x) ≈[ a ] x
tabulate∘lookup `⊤ = refl≡
tabulate∘lookup `Bool = refl≡
tabulate∘lookup (a `× b) = tabulate∘lookup a , tabulate∘lookup b
tabulate∘lookup (a `⇛ b) = tabulate∘lookup b

lookup∘tabulate : ∀ (f : TyIx a → Bool) → lookup (tabulate f) ≗ f
lookup∘tabulate f here      = refl≡
lookup∘tabulate f (left  x) = lookup∘tabulate (f ∘ left ) x
lookup∘tabulate f (right y) = lookup∘tabulate (f ∘ right) y
lookup∘tabulate f (arg a i) = lookup∘tabulate (λ z → f (arg a z)) i

swizzle : (TyIx b → TyIx a) → (⟦ a ⟧ → ⟦ b ⟧)
swizzle r a = tabulate (lookup a ∘ r)

-- tabulate≗ : ∀ {f g : TyIx a → Bool} → f ≗ g → eqᵗ a (tabulate f) (tabulate g)
tabulate≗ : ∀ {f g : TyIx a → Bool} → f ≗ g → tabulate f ≈[ a ] tabulate g
tabulate≗ {`⊤}     f≗g = refl≡
tabulate≗ {`Bool}  f≗g = f≗g here
tabulate≗ {a `× b} f≗g = tabulate≗ (λ i → f≗g (left i)) , tabulate≗ (λ j → f≗g (right j))
tabulate≗ {a `⇛ b} f≗g {x} = tabulate≗ (λ i → f≗g (arg x i))

swizzle-∘ : (g : TyIx c → TyIx b) (f : TyIx b → TyIx a)
          → ∀ {x : ⟦ a ⟧} → swizzle (f ∘ g) x ≈[ c ] (swizzle g ∘ swizzle f) x
swizzle-∘ {c = c} g f {x = x} =
  begin
    swizzle (f ∘ g) x
  ≡⟨⟩
    tabulate (lookup x ∘ f ∘ g)
  ≈˘⟨ tabulate≗ (≗∘ _ _ g (lookup∘tabulate _)) ⟩
    tabulate (lookup (tabulate (lookup x ∘ f)) ∘ g)
  ≡⟨⟩
    (swizzle g ∘ swizzle f) x
  ∎
 where open SetoidR (record { isEquivalence = isEquiv c })
       open import Function using (_∘′_)  -- temp
       -- Special case of ∘≈ˡ, but let's not import Categorical.Laws
       ≗∘ : ∀ {a}{A : Set a}{b}{B : Set b}{c}{C : Set c} (g h : B → C) (f : A → B)
          → g ≗ h → g ∘′ f ≗ h ∘′ f
       ≗∘ g h f g≗h x = g≗h (f x)

-- open ≈-Reasoning

instance

  Hₒ : Homomorphismₒ Ty Ty
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ _⇨ₜ_
  H = record { Fₘ = λ (mk r) → mk (swizzle r) }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = H-equiv H

  -- categoryH : CategoryH _⇨_ _⇨ₜ_ 0ℓ
  -- categoryH = record
  --   { F-id = λ {a} → λ x → tabulate∘lookup a
  --   ; F-∘  = λ (mk g) (mk f) → λ x → swizzle-∘ g f
  --   }

  -- productsH : ProductsH _⇨_ _⇨ₜ_ 0ℓ
  -- productsH = id-productsH

  -- monoidalH : MonoidalH _⇨_ _⇨ₜ_ 0ℓ
  -- monoidalH = record
  --               { F-unitorᵉˡ = λ {a}     _ → tabulate∘lookup a
  --               ; F-unitorⁱˡ = λ {a}     _ → tabulate∘lookup (⊤ × a)
  --               ; F-unitorᵉʳ = λ {a}     _ → tabulate∘lookup a
  --               ; F-unitorⁱʳ = λ {a}     _ → tabulate∘lookup (a × ⊤)
  --               ; F-assocˡ   = λ {a b c} _ → tabulate∘lookup ((a × b) × c)
  --               ; F-assocʳ   = λ {a b c} _ → tabulate∘lookup (a × (b × c))
  --               ; F-!        = λ         _ → tabulate∘lookup ⊤
  --               ; F-⊗        = λ f g     _ → refl≡
  --               }

  -- braidedH : BraidedH _⇨_ _⇨ₜ_ 0ℓ
  -- braidedH = record { F-swap = λ {a b} _ → tabulate∘lookup (b × a) }

  -- cartesianH : CartesianH _⇨_ _⇨ₜ_ 0ℓ
  -- cartesianH = record
  --   { F-exl = λ {a b} _ → tabulate∘lookup a
  --   ; F-exr = λ {a b} _ → tabulate∘lookup b
  --   ; F-dup = λ {a}   _ → tabulate∘lookup (a × a)
  --   }
