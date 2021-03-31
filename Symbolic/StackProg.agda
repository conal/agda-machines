-- Akin to http://conal.net/papers/calculating-compilers-categorically/

module Symbolic.StackProg where

open import Function using () renaming (id to id′)
open import Data.Product using (∃; _,_) renaming (_×_ to _×ᵗ_)

open import Ty
import Misc as F
open import Symbolic.Extrinsic

private variable a b c d i o z zⁱ zᵒ zᵃ : Ty

import Category as C
open C hiding (⊤; _×_)

-- Primitive instance p with input routing for first p
module i where

  infix 0 _⇨_
  _⇨_ : (Ty ×ᵗ Ty) → (Ty ×ᵗ Ty) → Set
  (i , zⁱ ⇨ o , zᵒ) = ∃ λ a → (a p.⇨ o) ×ᵗ (i × zⁱ r.⇨ a × zᵒ)

  instance

    meaningful : Meaningful (i , zⁱ ⇨ o , zᵒ)
    meaningful {i}{zⁱ}{o}{zᵒ} = record
      { Meaning = i × zⁱ ty.⇨ o × zᵒ
      ; ⟦_⟧ = λ (a , a⇨ₚo , i×zⁱ⇨ᵣa×zᵒ) → first ⟦ a⇨ₚo ⟧ ∘ ⟦ i×zⁱ⇨ᵣa×zᵒ ⟧
      }

-- Stack operations
module k where

  infix 0 _⇨_
  infixl 5 _∷ʳ_
  data _⇨_ : (Ty ×ᵗ Ty) → (Ty ×ᵗ Ty) → Set where
    [_]  : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
    _∷ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ i.⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)


  ⟦_⟧ᵏ : (i , zⁱ ⇨ o , zᵒ) → (i × zⁱ ty.⇨ o × zᵒ)
  ⟦ [ r ] ⟧ᵏ = ⟦ r ⟧
  ⟦ f ∷ʳ inst ⟧ᵏ = ⟦ f ⟧ᵏ ∘ ⟦ inst ⟧

  route : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
  route = [_]

  instance

    meaningful : Meaningful (i , zⁱ ⇨ o , zᵒ)
    meaningful = record { ⟦_⟧ = ⟦_⟧ᵏ }

    category : Category _⇨_
    category = record { id = route id ; _∘_ = _∘′_ }
     where
       infixr 9 _∘ʳ_
       _∘ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i × zⁱ r.⇨ a × zᵃ) → (i , zⁱ ⇨ o , zᵒ)
       [ r₂ ] ∘ʳ r₁ = [ r₂ ∘ r₁ ]
       (g ∷ʳ (d , d⇨ₚe , r₂)) ∘ʳ r₁ = g ∷ʳ (d , d⇨ₚe , r₂ ∘ r₁)

       infixr 9 _∘′_
       _∘′_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ ⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)
       g ∘′ [ r ] = g ∘ʳ r
       g ∘′ (f ∷ʳ inst) = g ∘′ f ∷ʳ inst

       -- -- Or drop _∘ʳ_, although Agda shades the last clause gray.
       -- [ r₂ ] ∘′ [ r₁ ] = [ r₂ ∘ r₁ ]
       -- (g ∷ʳ (d , d⇨ₚe , r₂)) ∘′ [ r₁ ] = g ∷ʳ (d , d⇨ₚe , r₂ ∘ r₁)
       -- g ∘′ (f ∷ʳ inst) = g ∘′ f ∷ʳ inst

  push : (a × b) , c ⇨ a , (b × c)
  push = route assocʳ

  pop : a , (b × c) ⇨ (a × b) , c
  pop = route assocˡ

  stacked : (a , (b × z) ⇨ c , (b × z)) → ((a × b) , z) ⇨ ((c × b) , z)
  stacked f = pop ∘ f ∘ push

  prim : i p.⇨ o → i , zⁱ ⇨ o , zⁱ
  prim {i} i⇨ₚo = [ id ] ∷ʳ (i , i⇨ₚo , id)

open k using (stacked)

-- Stack-preserving function
module sf where

  infix 0 _⇨_
  record _⇨_ (i o : Ty) : Set where
    constructor mk
    field
      f : ∀ {z} → i , z k.⇨ o , z

  prim : i p.⇨ o → i ⇨ o
  prim i⇨ₚo = mk (k.prim i⇨ₚo)

  route : i r.⇨ o → i ⇨ o
  route r = mk (k.route (first r))

  instance

    meaningful : ∀ {a b} → Meaningful (a ⇨ b)
    meaningful {a}{b} = record
      { Meaning = a ty.⇨ b
      ; ⟦_⟧ = λ (mk f) → unitorᵉʳ ∘ ⟦ f ⟧ ∘ unitorⁱʳ
      }

    category : Category _⇨_
    category = record
      { id = route id
      ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f)
      }

    monoidal : Monoidal _⇨_
    monoidal = record
      { ⊤ = ⊤
      ; _×_ = _×_
      ; _⊗_ = λ f g → second′ g ∘ first′ f
      ; ! = route !
      ; unitorᵉˡ = route unitorᵉˡ
      ; unitorᵉʳ = route unitorᵉʳ
      ; unitorⁱˡ = route unitorⁱˡ
      ; unitorⁱʳ = route unitorⁱʳ
      ; assocʳ = route assocʳ
      ; assocˡ = route assocˡ
      }
     where
       first′ : (a ⇨ c) → (a × b ⇨ c × b)
       first′ (mk f) = mk (stacked f)

       second′ : (b ⇨ d) → (a × b ⇨ a × d)
       second′ f = route swap ∘ first′ f ∘ route swap

  -- Functorial compilation
  compile : a c.⇨ b → a ⇨ b
  compile (c.route r) = route r
  compile (c.prim p)  = prim p
  compile (g c.∘ᶜ f)  = compile g ∘ compile f
  compile (f c.⊗ᶜ g)  = compile f ⊗ compile g
