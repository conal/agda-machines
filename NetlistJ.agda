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


first : a ⇨ c → a + b ⇨ c + b
first [ a⇨ᵣc ] = [ r.first a⇨ᵣc ]
first {a}{c}{b} (f ∷ʳ (d , d⇨ₚe , a⇨ᵣd)) =
  first {b = b} f ∷ʳ ({!!} , {!!} , {!!})

{-

Goal: a + b ⇨ c + b
————————————————————————————————————————————————————————————
a⇨ᵣd : a r.⇨ d
d⇨ₚe : d p.⇨ e
d    : ℕ
f    : e + a ⇨ c

b₁ = e

first f : (e + a) + b ⇨ c + b

-}


-- first (jf , f) = jf , λ {k} (netsₖ , k⇒ᵣa+b) →
--  let nets_jf+k , jf+k⇨ᵣc = f {k} (netsₖ , r.exl r.∘ k⇒ᵣa+b) in
--    nets_jf+k , jf+k⇨ᵣc r.△ r.exr r.∘ k⇒ᵣa+b r.∘ r.exr

-- second : b ⇨ d → a + b ⇨ a + d
-- second {b}{d}{a} g = route (r.swap {d}{a}) ∘ first g ∘ route (r.swap {a}{b})

-- -- route r.swap : a + b ⇨ b + a
-- -- first g      : b + a ⇨ d + a
-- -- route r.swap : d + a ⇨ a + d

-- infixr 7 _⊗_
-- _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
-- f ⊗ g = second g ∘ first f

-- infixr 7 _△_
-- _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
-- f △ g = (f ⊗ g) ∘ dup
