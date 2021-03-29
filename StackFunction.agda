-- Akin to http://conal.net/papers/calculating-compilers-categorically/

module StackFunction where

open import Data.Product using (∃; _×_; _,_)
open import Data.Nat using (ℕ; _+_)

open import Symbolic.ExtrinsicVec

private variable a b c d i o s sⁱ sᵒ sᵃ : ℕ

-- Primitive instance p with input routing for first p
module i where

  infix 0 _⇨_
  _⇨_ : (ℕ × ℕ) → (ℕ × ℕ) → Set
  i , sⁱ ⇨ o , sᵒ = ∃ λ a → (a p.⇨ o) × (i + sⁱ r.⇨ a + sᵒ)

  ⟦_⟧ : i , sⁱ ⇨ o , sᵒ → i + sⁱ b.⇨ o + sᵒ
  ⟦ a , a⇨ₚo , i+sⁱ⇨ᵣa+sᵒ ⟧ = b.first p.⟦ a⇨ₚo ⟧ b.∘ r.⟦ i+sⁱ⇨ᵣa+sᵒ ⟧


-- Stack operations
module k where

  infix 0 _⇨_
  infixl 5 _∷ʳ_
  data _⇨_ : (ℕ × ℕ) → (ℕ × ℕ) → Set where
    [_]  : (i + sⁱ r.⇨ o + sᵒ) → (i , sⁱ ⇨ o , sᵒ)
    _∷ʳ_ : (a , sᵃ ⇨ o , sᵒ) → (i , sⁱ i.⇨ a , sᵃ) → (i , sⁱ ⇨ o , sᵒ)

  ⟦_⟧ : i , sⁱ ⇨ o , sᵒ → i + sⁱ b.⇨ o + sᵒ
  ⟦ [ r ] ⟧ = r.⟦ r ⟧
  ⟦_⟧ {i = i}{sⁱ = sⁱ} (f ∷ʳ inst) = ⟦ f ⟧ b.∘ i.⟦_⟧ {i = i}{sⁱ = sⁱ} inst

  -- I hope to eliminate explicit implicits by moving from ℕ back to Ty.

  route : (i + sⁱ r.⇨ o + sᵒ) → (i , sⁱ ⇨ o , sᵒ)
  route = [_]

  infixr 9 _∘ʳ_
  _∘ʳ_ : (a , sᵃ ⇨ o , sᵒ) → (i + sⁱ r.⇨ a + sᵃ) → (i , sⁱ ⇨ o , sᵒ)
  [ r₂ ] ∘ʳ r₁ = [ r₂ r.∘ r₁ ]
  (g ∷ʳ (d , d⇨ₚe , r₂)) ∘ʳ r₁ = g ∷ʳ (d , d⇨ₚe , r₂ r.∘ r₁)

  infixr 9 _∘_
  _∘_ : (a , sᵃ ⇨ o , sᵒ) → (i , sⁱ ⇨ a , sᵃ) → (i , sⁱ ⇨ o , sᵒ)
  g ∘ [ r ] = g ∘ʳ r
  g ∘ (f ∷ʳ inst) = g ∘ f ∷ʳ inst

  -- -- Or drop _∘ʳ_, although Agda shades the last clause gray.
  -- [ r₂ ] ∘ [ r₁ ] = [ r₂ r.∘ r₁ ]
  -- (g ∷ʳ (d , d⇨ₚe , r₂)) ∘ [ r₁ ] = g ∷ʳ (d , d⇨ₚe , r₂ r.∘ r₁)
  -- g ∘ (f ∷ʳ inst) = g ∘ f ∷ʳ inst

  push : a + b , c ⇨ a , b + c
  push {a} = route (r.assocʳ {a})

  pop : a , b + c ⇨ a + b , c
  pop {a} = route (r.assocˡ {a})

  stacked : (a , b + s ⇨ c , b + s) → (a + b , s) ⇨ (c + b , s)
  stacked f = pop ∘ f ∘ push

  prim : i p.⇨ o → i , sⁱ ⇨ o , sⁱ
  prim {i} i⇨ₚo = [ r.id ] ∷ʳ (i , i⇨ₚo , r.id)


open k using (stacked)

-- Stack function
module sf where

  infix 0 _⇨_
  _⇨_ : ℕ → ℕ → Set
  i ⇨ o = ∀ {s} → i , s k.⇨ o , s

  ⟦_⟧ : a ⇨ b → a b.⇨ b
  ⟦ f ⟧ = b.unitorᵉʳ b.∘ k.⟦ f ⟧ b.∘ b.unitorⁱʳ

  prim : i p.⇨ o → i ⇨ o
  prim i⇨ₚo = k.prim i⇨ₚo

  route : i r.⇨ o → i ⇨ o
  route r = k.route (r.first r)

  id  : a ⇨ a
  dup : a ⇨ a + a
  exl : a + b ⇨ a
  exr : a + b ⇨ b
  !   : a ⇨ 0

  id  = route r.id
  dup = route r.dup
  exl = route r.exl
  exr = route r.exr
  !   = route λ ()

  swap : a + b ⇨ b + a
  assocˡ : a + (b + c) ⇨ (a + b) + c
  assocʳ : (a + b) + c ⇨ a + (b + c)

  swap   {a}{b}    = route (r.swap   {a}{b})
  assocˡ {a}{b}{c} = route (r.assocˡ {a}{b}{c})
  assocʳ {a}{b}{c} = route (r.assocʳ {a}{b}{c})

  infixr 9 _∘_
  _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  g ∘ f = g k.∘ f
  
  first : (a ⇨ c) → (a + b ⇨ c + b)
  first f = stacked f

  second : (b ⇨ d) → (a + b ⇨ a + d)
  second {b}{d}{a} f = route (r.swap {d}{a}) ∘ first f ∘ route (r.swap {a}{b})

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
  f ⊗ g = second g ∘ first f

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ dup

open sf public

-- Functorial compilation
compile : a c.⇨ b → a ⇨ b
compile (c.route r) = route r
compile (c.prim p)  = prim p
compile (g c.∘ f)   = compile g ∘ compile f
compile (f c.⊗ g)   = compile f ⊗ compile g
