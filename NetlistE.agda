-- This variation is based on a vector-like type with sized elements.
-- Replace products with vectors.

-- module Netlist where

open import Function renaming (id to id′) using (_∘′_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Nat
open import Data.Fin using (Fin; raise; inject+) renaming (splitAt to splitAtᶠ)
-- TODO: trim Data.Fin imports
-- open import Data.Fin using (Fin)
import Data.Sum as ⊎
open ⊎ using (_⊎_)

infixr 5 _∷_
data Vec′ (F : ℕ → ℕ → Set) : ℕ → Set where
  [] : Vec′ F zero
  _∷_ : ∀ {k n} → F k n → Vec′ F k → Vec′ F (n + k)


open import Symbolic.ExtrinsicVec

private variable a b c d m n k : ℕ

F : ℕ → ℕ → Set
F k n = ∃ λ m → (m p.⇨ n) × (k r.⇨ m)

Netlist : ℕ → Set
Netlist = Vec′ F

-- A netlist with i outputs and result size a
Src : ℕ → ℕ → Set
Src i a = Netlist i × (i r.⇨ a)

-- The netlist category. The number of netlist outputs is static.
infix 0 _⇨_
_⇨_ : ℕ → ℕ → Set
a ⇨ b = ∃ λ j → ∀ { i } → Src i a → Src (j + i) b

route : a r.⇨ b → a ⇨ b
route r = zero , λ {i} (netsᵢ , i⇨ᵣa) → netsᵢ , r r.∘ i⇨ᵣa

-- Now id and _∘_ are easy. What about _⊗_?

id : a ⇨ a
id = zero , id′

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

infixr 9 _∘_
_∘_ : b ⇨ c → a ⇨ b → a ⇨ c
_∘_ {c = c} (gj , g) (fj , f) =
  gj + fj , λ {i} sₐ → subst (λ n → Src n c) (sym (+-assoc gj fj i)) (g (f sₐ))

first : a ⇨ c → a + b ⇨ c + b
first (fj , f) = fj , λ {i} (netsᵢ , ir⇒a+b) →
 let nets_fj+i , fj+i⇨ᵣc = f {i} (netsᵢ , r.exl r.∘ ir⇒a+b) in
   nets_fj+i , fj+i⇨ᵣc r.△ r.exr r.∘ ir⇒a+b r.∘ r.exr

second : b ⇨ d → a + b ⇨ a + d
second {b}{d}{a} g = route (r.swap {d}{a}) ∘ first g ∘ route (r.swap {a}{b})

-- route r.swap : a + b ⇨ b + a
-- first g : b + a ⇨ d + a
-- route r.swap : d + a ⇨ a + d

infixr 7 _⊗_
_⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
f ⊗ g = second g ∘ first f

-- r.exr : fj + i r.⇨ i
-- ir⇒a+b : i r.⇨ a + b
-- r.exr : a + b r.⇨ b
-- 
-- r.exr r.∘ ir⇒a+b r.∘ r.exr : fj + i r.⇨ b
