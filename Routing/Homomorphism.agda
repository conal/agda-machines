{-# OPTIONS --safe --without-K #-}

module Routing.Homomorphism where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)

open import Categorical.Raw
open import Categorical.Homomorphism

open import Miscellany using (Function)
open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws

open import Typed.Raw (Function {0ℓ}) renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism (Function {0ℓ}) 0ℓ
open import Typed.Laws         (Function {0ℓ}) 0ℓ

-- -- I don't know why the following alternative leads to problems
-- open import Typed (Function {0ℓ}) 0ℓ renaming (_⇨_ to _⇨ₜ_)

open import Routing.Raw

private variable a b c d : Ty

-- Extract a bit
-- ⟦_⟧ᵇ : TyIx a → a →ᵗ Bool
⟦_⟧ᵇ : TyIx a → ⟦ a ⟧ → Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

lookup : ⟦ a ⟧ → (TyIx a → Bool)
lookup a i = ⟦ i ⟧ᵇ a

tabulate : (TyIx a → Bool) → ⟦ a ⟧
tabulate {`⊤} f = tt
tabulate {`Bool} f = f here
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)

lookup∘tabulate : ∀ (f : TyIx a → Bool) → lookup (tabulate f) ≗ f
lookup∘tabulate f here      = refl≡
lookup∘tabulate f (left  x) = lookup∘tabulate (f ∘ left ) x
lookup∘tabulate f (right y) = lookup∘tabulate (f ∘ right) y

swizzle : (TyIx b → TyIx a) → (⟦ a ⟧ → ⟦ b ⟧)
swizzle r a = tabulate (lookup a ∘ r)


swizzle-tt : ∀ (f : TyIx b → TyIx ⊤) (i : TyIx b) → b ≡ ⊤
swizzle-tt f i with f i ; ... | ()
-- Is there a more straightforward formulation of this fact?

swizzle-id : ∀ a {x : ⟦ a ⟧} → swizzle {b = a} id x ≡ x
swizzle-id `⊤       = refl≡
swizzle-id `Bool    = refl≡
swizzle-id (a `× b) = cong₂ _,_ (swizzle-id a) (swizzle-id b)

tabulate≗ : ∀ {f g : TyIx a → Bool} → f ≗ g → tabulate f ≡ tabulate g
tabulate≗ {`⊤}     {f = f} {g} f≗g = refl≡
tabulate≗ {`Bool}  {f = f} {g} f≗g = f≗g here
tabulate≗ {A `× B} {f = f} {g} f≗g =
  begin
    (tabulate (f ∘ left) , tabulate (f ∘ right))
  ≡⟨ cong₂ _,_ (tabulate≗ (λ x → f≗g (left x)))
               (tabulate≗ (λ x → f≗g (right x))) ⟩
    (tabulate (g ∘ left) , tabulate (g ∘ right))
  ∎
 where open ≡-Reasoning

swizzle-∘ : (g : TyIx c → TyIx b) (f : TyIx b → TyIx a)
          → ∀ {a : ⟦ a ⟧} → swizzle (f ∘ g) a ≡ (swizzle g ∘ swizzle f) a
swizzle-∘ g f {a} =
  begin
    swizzle (f ∘ g) a
  ≡⟨⟩
    tabulate (lookup a ∘ f ∘ g)
  ≡˘⟨ tabulate≗ (≗∘ _ _ g (lookup∘tabulate _)) ⟩
    tabulate (lookup (tabulate (lookup a ∘ f)) ∘ g)
  ≡⟨⟩
    (swizzle g ∘ swizzle f) a
  ∎
 where open ≡-Reasoning
       open import Function using (_∘′_)  -- temp
       -- Special case of ∘≈ˡ, but let's not import Categorical.Laws
       ≗∘ : ∀ {a}{A : Set a}{b}{B : Set b}{c}{C : Set c} (g h : B → C) (f : A → B)
          → g ≗ h → g ∘′ f ≗ h ∘′ f
       ≗∘ g h f g≗h x = g≗h (f x)


open ≈-Reasoning

instance

  Hₒ : Homomorphismₒ Ty Ty
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ _⇨ₜ_
  H = record { Fₘ = λ (mk r) → mk (swizzle r) }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = H-equiv H

  categoryH : CategoryH _⇨_ _⇨ₜ_ 0ℓ
  categoryH = record
    { F-id = λ {a} → λ x → swizzle-id a
    ; F-∘  = λ (mk g) (mk f) → λ x → swizzle-∘ g f
    }

  productsH : ProductsH _⇨_ _⇨ₜ_ 0ℓ
  productsH = id-productsH

  monoidalH : MonoidalH _⇨_ _⇨ₜ_ 0ℓ
  monoidalH = record
                { F-unitorᵉˡ = λ {a}     _ → swizzle-id a
                ; F-unitorⁱˡ = λ {a}     _ → swizzle-id (⊤ × a)
                ; F-unitorᵉʳ = λ {a}     _ → swizzle-id a
                ; F-unitorⁱʳ = λ {a}     _ → swizzle-id (a × ⊤)
                ; F-assocˡ   = λ {a b c} _ → swizzle-id ((a × b) × c)
                ; F-assocʳ   = λ {a b c} _ → swizzle-id (a × (b × c))
                ; F-!        = λ         _ → swizzle-id ⊤
                ; F-⊗        = λ f g     _ → refl≡
                }

  braidedH : BraidedH _⇨_ _⇨ₜ_ 0ℓ
  braidedH = record { F-swap = λ {a b} _ → swizzle-id (b × a) }

  cartesianH : CartesianH _⇨_ _⇨ₜ_ 0ℓ
  cartesianH = record
    { F-exl = λ {a b} _ → swizzle-id a
    ; F-exr = λ {a b} _ → swizzle-id b
    ; F-dup = λ {a}   _ → swizzle-id (a × a)
    }
