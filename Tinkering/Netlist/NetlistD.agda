-- This variation is based on a vector-like type with sized elements.
-- Replace products with vectors.

module NetlistD where

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

-- -- A netlist with result type a
-- Nets : ℕ → ℕ → Set
-- Nets a i = Netlist i × (i r.⇨ a)

-- Source : ℕ → Set
-- Source = ∃ ∘′ Nets
-- -- Source b = ∃ (Nets b)
-- -- Source b = ∃ λ k → Nets b k
-- -- Source b = ∃ λ k → Netlist k × (k r.⇨ b)

-- -- The netlist category
-- infix 0 _⇨_
-- _⇨_ : ℕ → ℕ → Set
-- a ⇨ b = ∃ λ j → ∀ i → Nets a i → Nets b (j + i)


-- I don't know whether it's important to see relationship between the output pool.
-- Try without.

-- A netlist with result type a
Src : ℕ → Set
Src a = ∃ λ k → Netlist k × (k r.⇨ a)

-- The netlist category
infix 0 _⇨_
_⇨_ : ℕ → ℕ → Set
a ⇨ b = Src a → Src b

-- Now id and _∘_ are easy. What about _⊗_?

id : a ⇨ a
id = id′

infixr 9 _∘_
_∘_ : b ⇨ c → a ⇨ b → a ⇨ c
_∘_ = _∘′_

-- bump : (b : ℕ) → Netlist k → Netlist (k + b)
-- bump b [] = {!!}
-- bump b (x ∷ z) = {!!}

first : a ⇨ c → a + b ⇨ c + b
first {a} {c} {b} f (k , netsₖ , kr⇨a+b) =
  let k′ , netsₖ′ , k′r⇨c = f (k , netsₖ , r.exl r.∘ kr⇨a+b) in
    k′ , netsₖ′ , ⊎.[ k′r⇨c , {!!} ]′ ∘′ splitAtᶠ c

-- ? : Fin b → Fin k′

-- We have exr : Fin b → Fin (a + b), kr⇨a+b : Fin (a + b) → Fin k, so we just
-- need Fin k → Fin k′, which requires that k′ >= k. This condition is true, but
-- our simplified _⇨_ definition doesn't know it. Revert to the more specific
-- _⇨_ above with mixed existential and universal quantification.

-- k′r⇨c  : Fin c → Fin k′



                  -- λ c+b → let c⊎b = splitAtᶠ c c+b in
                  --           {!!}

-- first {b = b} f (.0 , [] , kr⇨a+b) = 0 , [] , {!kr⇨a+b!}
-- first {b = b} f (.(n + k) , _∷_ {k}{n} x nets , kr⇨a+b) = k + b , {!!} , {!!}


-- first {b = b} f (k , nets , kr⇨a+b) = k + b , {!!} , {!!}


-- infixr 7 _⊗_
-- _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
-- (f ⊗ g) (k , nets , kr⇨a+b) = {!!}

-- f : a ⇨ c
-- g : b ⇨ d



-- Nets a = ∃ λ k → Netlist k × (k r.⇨ a)
