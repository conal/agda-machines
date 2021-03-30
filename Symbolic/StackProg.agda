-- Akin to http://conal.net/papers/calculating-compilers-categorically/

module Symbolic.StackProg where

open import Data.Product using (∃; _,_) renaming (_×_ to _×ᵗ_)

open import Ty
import Misc as F
open import Symbolic.Extrinsic

private variable a b c d i o z zⁱ zᵒ zᵃ : Ty

-- Primitive instance p with input routing for first p
module i where

  infix 0 _⇨_
  _⇨_ : (Ty ×ᵗ Ty) → (Ty ×ᵗ Ty) → Set
  (i , zⁱ ⇨ o , zᵒ) = ∃ λ a → (a p.⇨ o) ×ᵗ (i × zⁱ r.⇨ a × zᵒ)

  ⟦_⟧ : i , zⁱ ⇨ o , zᵒ → i × zⁱ →ᵗ o × zᵒ
  ⟦ a , a⇨ₚo , i×zⁱ⇨ᵣa×zᵒ ⟧ = F.first p.⟦ a⇨ₚo ⟧ F.∘ r.⟦ i×zⁱ⇨ᵣa×zᵒ ⟧

-- Stack operations
module k where

  infix 0 _⇨_
  infixl 5 _∷ʳ_
  data _⇨_ : (Ty ×ᵗ Ty) → (Ty ×ᵗ Ty) → Set where
    [_]  : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
    _∷ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ i.⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)

  ⟦_⟧ : i , zⁱ ⇨ o , zᵒ → i × zⁱ →ᵗ o × zᵒ
  ⟦ [ r ] ⟧ = r.⟦ r ⟧
  ⟦ f ∷ʳ inst ⟧ = ⟦ f ⟧ F.∘ i.⟦_⟧ inst

  route : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
  route = [_]

  infixr 9 _∘ʳ_
  _∘ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i × zⁱ r.⇨ a × zᵃ) → (i , zⁱ ⇨ o , zᵒ)
  [ r₂ ] ∘ʳ r₁ = [ r₂ r.∘ r₁ ]
  (g ∷ʳ (d , d⇨ₚe , r₂)) ∘ʳ r₁ = g ∷ʳ (d , d⇨ₚe , r₂ r.∘ r₁)

  infixr 9 _∘_
  _∘_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ ⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)
  g ∘ [ r ] = g ∘ʳ r
  g ∘ (f ∷ʳ inst) = g ∘ f ∷ʳ inst

  -- -- Or drop _∘ʳ_, although Agda shades the last clause gray.
  -- [ r₂ ] ∘ [ r₁ ] = [ r₂ r.∘ r₁ ]
  -- (g ∷ʳ (d , d⇨ₚe , r₂)) ∘ [ r₁ ] = g ∷ʳ (d , d⇨ₚe , r₂ r.∘ r₁)
  -- g ∘ (f ∷ʳ inst) = g ∘ f ∷ʳ inst

  push : (a × b) , c ⇨ a , (b × c)
  push = route r.assocʳ

  pop : a , (b × c) ⇨ (a × b) , c
  pop = route r.assocˡ

  stacked : (a , (b × z) ⇨ c , (b × z)) → ((a × b) , z) ⇨ ((c × b) , z)
  stacked f = pop ∘ f ∘ push

  prim : i p.⇨ o → i , zⁱ ⇨ o , zⁱ
  prim {i} i⇨ₚo = [ r.id ] ∷ʳ (i , i⇨ₚo , r.id)


open k using (stacked)

-- Stack function
module sf where

  infix 0 _⇨_
  _⇨_ : Ty → Ty → Set
  i ⇨ o = ∀ {z} → i , z k.⇨ o , z

  ⟦_⟧ : a ⇨ b → a →ᵗ b
  ⟦ f ⟧ = F.unitorᵉʳ F.∘ k.⟦ f ⟧ F.∘ F.unitorⁱʳ

  prim : i p.⇨ o → i ⇨ o
  prim i⇨ₚo = k.prim i⇨ₚo

  route : i r.⇨ o → i ⇨ o
  route r = k.route (r.first r)

  id  : a ⇨ a
  dup : a ⇨ a × a
  exl : a × b ⇨ a
  exr : a × b ⇨ b
  !   : a ⇨ ⊤

  id  = route r.id
  dup = route r.dup
  exl = route r.exl
  exr = route r.exr
  !   = route λ ()

  swap : a × b ⇨ b × a
  assocˡ : a × (b × c) ⇨ (a × b) × c
  assocʳ : (a × b) × c ⇨ a × (b × c)

  swap   = route r.swap
  assocˡ = route r.assocˡ
  assocʳ = route r.assocʳ

  infixr 9 _∘_
  _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  g ∘ f = g k.∘ f
  
  first : (a ⇨ c) → (a × b ⇨ c × b)
  first f = stacked f

  second : (b ⇨ d) → (a × b ⇨ a × d)
  second f = route r.swap ∘ first f ∘ route r.swap

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a × b ⇨ c × d
  f ⊗ g = second g ∘ first f

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c × d
  f △ g = (f ⊗ g) ∘ dup

  unitorᵉˡ : ⊤ × a ⇨ a
  unitorᵉʳ : a × ⊤ ⇨ a
  unitorⁱˡ : a ⇨ ⊤ × a
  unitorⁱʳ : a ⇨ a × ⊤

  unitorᵉˡ = route r.unitorᵉˡ
  unitorᵉʳ = route r.unitorᵉʳ
  unitorⁱˡ = route r.unitorⁱˡ
  unitorⁱʳ = route r.unitorⁱʳ

open sf public

-- Functorial compilation
compile : a c.⇨ b → a ⇨ b
compile (c.route r) = route r
compile (c.prim p)  = prim p
compile (g c.∘ f)   = compile g ∘ compile f
compile (f c.⊗ g)   = compile f ⊗ compile g
