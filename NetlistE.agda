-- This variation is based on a vector-like type with sized elements.
-- Replace products with vectors.

-- module Netlist where

open import Data.Product using (∃; _×_; _,_)
open import Data.Nat

open import Symbolic.ExtrinsicVec

private variable a b c d j k : ℕ

infixr 5 _∷_
data Vec′ (F : ℕ → ℕ → Set) : ℕ → Set where
  [] : Vec′ F zero
  _∷_ : F k j → Vec′ F k → Vec′ F (j + k)


F : ℕ → ℕ → Set
F k b = ∃ λ a → (a p.⇨ b) × (k r.⇨ a)

Netlist : ℕ → Set
Netlist = Vec′ F

-- A netlist with i outputs and result size a
Src : ℕ → ℕ → Set
Src k a = Netlist k × (k r.⇨ a)

-- The netlist category. The number of netlist outputs is static.
infix 0 _⇨_
_⇨_ : ℕ → ℕ → Set
a ⇨ b = ∃ λ j → ∀ {k} → Src k a → Src (j + k) b

route : a r.⇨ b → a ⇨ b
route a⇨ᵣb = zero , λ (netsₖ , k⇨ᵣa) → netsₖ , a⇨ᵣb r.∘ k⇨ᵣa

id  : a ⇨ a
dup : a ⇨ a + a
exl : a + b ⇨ a
exr : a + b ⇨ b
!   : a ⇨ 0

id  = route r.id
dup = route r.dup   -- or id △ id
exl = route r.exl
exr = route r.exr
!   = route r.!

-- assocʳ etc via route or their standard definitions via _△_ etc. TODO: prove
-- route is a cartesian functor, so all such alternatives are equivalent.

prim : a p.⇨ b → a ⇨ b
prim {a}{b} a⇨ₚb = b , λ (netsₖ , k⇨ᵣa) → (a , a⇨ₚb , k⇨ᵣa) ∷ netsₖ , r.exl

open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.Nat.Properties using (+-assoc)

infixr 9 _∘_
_∘_ : b ⇨ c → a ⇨ b → a ⇨ c
_∘_ {c = c} (jg , g) (jf , f) =
  jg + jf , λ {k} sₐ → subst (λ n → Src n c) (sym (+-assoc jg jf k)) (g (f sₐ))

first : a ⇨ c → a + b ⇨ c + b
first (jf , f) = jf , λ {k} (netsₖ , k⇒ᵣa+b) →
 let nets_jf+k , jf+k⇨ᵣc = f {k} (netsₖ , r.exl r.∘ k⇒ᵣa+b) in
   nets_jf+k , jf+k⇨ᵣc r.△ r.exr r.∘ k⇒ᵣa+b r.∘ r.exr

second : b ⇨ d → a + b ⇨ a + d
second {b}{d}{a} g = route (r.swap {d}{a}) ∘ first g ∘ route (r.swap {a}{b})

-- route r.swap : a + b ⇨ b + a
-- first g      : b + a ⇨ d + a
-- route r.swap : d + a ⇨ a + d

infixr 7 _⊗_
_⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
f ⊗ g = second g ∘ first f

infixr 7 _△_
_△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
f △ g = (f ⊗ g) ∘ dup

-- Homomorphic compilation
compile : a c.⇨ b → a ⇨ b
compile (c.route r) = route r
compile (c.prim  p) = prim p
compile (g c.∘ f)   = compile g ∘ compile f
compile (f c.⊗ g)   = compile f ⊗ compile g

-- Note that compile is a cartesian functor

-- TODO: Define evaluation ⟦_⟧. Prove functor and ⟦_⟧ ≗ c.⟦_⟧ ∘′ compile .
