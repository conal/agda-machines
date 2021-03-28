module NetlistJ where

open import Data.Product using (∃; _×_; _,_)
open import Data.Bool using (Bool)  -- TEMP
open import Data.Nat
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality -- hiding ([_])
import Data.Vec as V

import Misc as F
open import Symbolic.ExtrinsicVec

private variable a b c d j k i o : ℕ

Q : (a b.⇨ b) → (a b.⇨ b + a)
Q f = f b.△ b.id

Inst : ℕ → ℕ → Set
Inst o b = ∃ λ a → (a p.⇨ b) × (o r.⇨ a)

⟦_⟧ⁱ : Inst o b → o b.⇨ b
⟦ a , a⇨ₚb , o⇨ᵣa ⟧ⁱ = p.⟦ a⇨ₚb ⟧ b.∘ r.⟦ o⇨ᵣa ⟧

infix 0 _⇨_
infixl 5 _∷ʳ_
data _⇨_ : ℕ → ℕ → Set where
  [_] : i r.⇨ o → i ⇨ o
  _∷ʳ_ : b + i ⇨ o → Inst i b → i ⇨ o

⟦_⟧ : i ⇨ o → i b.⇨ o
⟦ [ r ] ⟧ = r.⟦ r ⟧
⟦ f ∷ʳ inst ⟧ = ⟦ f ⟧ b.∘ Q ⟦ inst ⟧ⁱ

route : a r.⇨ b → a ⇨ b
route = [_]

infixr 9 _∘ʳ_
_∘ʳ_ : (b ⇨ c) → (a r.⇨ b) → (a ⇨ c)
[ b⇨ᵣc ] ∘ʳ a⇨ᵣb = [ b⇨ᵣc r.∘ a⇨ᵣb ]
(g ∷ʳ (d , d⇨ₚe , b⇨ᵣd)) ∘ʳ a⇨ᵣb =
  (g ∘ʳ r.second a⇨ᵣb) ∷ʳ (d , d⇨ₚe , b⇨ᵣd r.∘ a⇨ᵣb)

infixr 9 _∘_
_∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
g ∘ [ a⇨ᵣb ] = g ∘ʳ a⇨ᵣb
g ∘ (f ∷ʳ inst) = g ∘ f ∷ʳ inst



{-

Goal: b + a r.⇨ b + e
————————————————————————————————————————————————————————————
a⇨ᵣb : a r.⇨ e

r.second a⇨ᵣb : b + a r.⇨ b + e

-- b⇨ᵣd : e r.⇨ d
-- d⇨ₚe : d p.⇨ b

-- g    : b + e ⇨ c

-- b₁ = d
-}

-- infixr 9 _∘_
-- _∘_ : (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
-- [ b⇨ᵣc ] ∘ [ a⇨ʳb ] = [ b⇨ᵣc r.∘ a⇨ʳb ]

-- (g ∷ʳ (d , d⇨ₚe , b⇨ᵣd)) ∘ [ a⇨ʳb ] =
--    {!!}

-- a⇨ʳb : a r.⇨ b
-- b⇨ᵣd : b r.⇨ d
-- d⇨ₚe : d p.⇨ e
-- g    : e + b ⇨ c

-- b₁ = d


   -- {!g ∷ʳ (d , d⇨ₚe , b⇨ᵣd r.∘ a⇨ʳb)!}

-- g ∘ (f ∷ʳ inst) = {!!}

-- [ b⇨ᵣc ] ∘ [ a⇨ᵣb ] = [ b⇨ᵣc r.∘ a⇨ᵣb ]
-- [ b⇨ᵣc ] ∘ (f ∷ʳ inst) = {!!}

-- (g ∷ʳ inst) ∘ f = {!!}

-- _∘_ {b}{c}{a} (g ∷ʳ x) f = {!!}

-- [ b⇨ᵣc ] ∘ [ a⇨ᵣb ] = [ b⇨ᵣc r.∘ a⇨ᵣb ]
-- [ b+o⇨ᵣc ] ∘ P@((d , d⇨ₚb , o⇨ᵣd) ∷ a⇨o) =
--   {!!} -- {!!} ∷ a⇨o
-- (inst ∷ g) ∘ f = {!!}

