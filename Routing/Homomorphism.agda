{-# OPTIONS --safe --without-K #-}

module Routing.Homomorphism where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)

open import Categorical.Raw
open import Categorical.Homomorphism

open import Miscellany using (Function)
open import Categorical.Instances.Function.Raw
open import Ty.Raw renaming (_⇨_ to _⇨ₜ_)
open import Ty.Homomorphism
open import Ty.Laws

open import Routing.Raw

private variable A B C D : Ty

-- Extract a bit
-- ⟦_⟧ᵇ : ∀ {A} → TyIx A → A →ᵗ Bool
⟦_⟧ᵇ : ∀ {A} → TyIx A → ⟦ A ⟧ᵗ → Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

lookup : ⟦ A ⟧ᵗ → (TyIx A → Bool)
lookup a i = ⟦ i ⟧ᵇ a

tabulate : (TyIx A → Bool) → ⟦ A ⟧ᵗ
tabulate {`⊤} f = tt
tabulate {`Bool} f = f here
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)

lookup∘tabulate : ∀ (f : TyIx A → Bool) → lookup (tabulate f) ≗ f
lookup∘tabulate f here      = refl≡
lookup∘tabulate f (left  x) = lookup∘tabulate (f ∘ left ) x
lookup∘tabulate f (right y) = lookup∘tabulate (f ∘ right) y

swizzle : (TyIx B → TyIx A) → (⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ)
swizzle r a = tabulate (lookup a ∘ r)


swizzle-tt : ∀ (f : TyIx B → TyIx ⊤) (i : TyIx B) → B ≡ ⊤
swizzle-tt f i with f i ; ... | ()
-- Is there a more straightforward formulation of this fact?

swizzle-id : ∀ {a : ⟦ A ⟧ᵗ} → swizzle id a ≡ a
swizzle-id {`⊤}     = refl≡
swizzle-id {`Bool}  = refl≡
swizzle-id {_ `× _} = cong₂ _,_ swizzle-id swizzle-id

-- swizzle-id {A = _ `× _} {a , b} =
--   begin
--     swizzle id (a , b)
--   ≡⟨⟩
--     swizzle id a , swizzle id b
--   ≡⟨ cong₂ _,_ swizzle-id swizzle-id ⟩
--     (a , b)
--   ∎
--  where open ≡-Reasoning


tabulate≗ : ∀ {f g : TyIx A → Bool} → f ≗ g → tabulate f ≡ tabulate g
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


swizzle-∘ : (g : TyIx C → TyIx B) (f : TyIx B → TyIx A)
          → ∀ {a : ⟦ A ⟧ᵗ} → swizzle (f ∘ g) a ≡ (swizzle g ∘ swizzle f) a
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
       -- Special case of ∘-resp-≈ˡ, but let's not import Categorical.Laws
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
    { F-id = λ x → swizzle-id 
    ; F-∘  = λ (mk g) (mk f) → λ x → swizzle-∘ g f
    }

  productsH : ProductsH _⇨_ _⇨ₜ_ 0ℓ
  productsH = id-productsH

  monoidalH : MonoidalH _⇨_ _⇨ₜ_ 0ℓ
  monoidalH = record
                { F-unitorᵉˡ = λ _ → swizzle-id
                ; F-unitorⁱˡ = λ _ → swizzle-id
                ; F-unitorᵉʳ = λ _ → swizzle-id
                ; F-unitorⁱʳ = λ _ → swizzle-id
                ; F-assocˡ   = λ _ → swizzle-id
                ; F-assocʳ   = λ _ → swizzle-id
                ; F-!        = λ _ → swizzle-id
                ; F-⊗        = λ f g _ → refl≡
                }

  braidedH : BraidedH _⇨_ _⇨ₜ_ 0ℓ
  braidedH = record { F-swap = λ _ → swizzle-id }

  cartesianH : CartesianH _⇨_ _⇨ₜ_ 0ℓ
  cartesianH = record
    { F-exl = λ _ → swizzle-id
    ; F-exr = λ _ → swizzle-id
    ; F-dup = λ _ → swizzle-id
    }
