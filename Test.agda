module Test where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Data.Bool using (true; false)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String
open import IO

import Category as C
open C hiding (⊤; _×_) ; open CartUtils
open import Ty
open import Symbolic.Extrinsic
open import Symbolic.StackProg
open import Dot

-- open CartUtils

open TyUtils

-- Combinational examples
module ce where
  open c

  t₁ : Bool ↑ 5 ⇨ Bool ↑ 5
  t₁ = id

  t₂ = prim p.∧

  t₃ = prim p.not ∘ prim p.∧

  t₄ : Bool ↑ 3 ⇨ Bool ↑ 3
  t₄ = first (prim p.not)

  t₅ = prim p.not

  -- Summands ⇨ sum , carry
  -- λ (a , b) → (a ⊕ b , a ∧ b)
  halfAdd : Bool × Bool ⇨ Bool × Bool
  halfAdd = prim p.xor △ prim p.∧

  shiftRs : ∀ {n} → Bool × Bool ↑ n ⇨ Bool ↑ n
  shiftRs = shiftR

-- Sequential examples
module se where
  open s

  -- Toggle
  t₁ : ⊤ ⇨ Bool
  t₁ = mealy true (dup ∘ c.prim p.not ∘ exr)
  -- λ { (tt , s) → (not s , not s) }

  -- Toggle
  t₁′ : ⊤ ⇨ Bool
  t₁′ = mealy true (first (c.prim p.not) ∘ dup ∘ exr)
  -- λ { (tt , s) → (s , not s) }

  -- Cumulative or
  t₂ : Bool ⇨ Bool
  t₂ = mealy false (dup ∘ c.prim p.∨)
  -- λ { (b , s) → (b ∨ s , b ∨ s) }

  t₃ = delay false

  t₄ = delay (false , true , false)

  t₅ = delay false ∘ delay true

  t₆ = t₅ ∘ t₅

  t₇ = t₆ ∘ t₆

  -- Toggle with enable
  -- mealy false (λ (i , s) → ((i xor s , i ∧ s) , i xor s))
  toggle₁ : Bool ⇨ Bool × Bool
  toggle₁ = mealy false ((id △ exl) ∘ ce.halfAdd)

  toggle₂ = toggle₁ ◂ toggle₁
  toggle₄ = toggle₂ ◂ toggle₂

  toggles = toggle₁ ↱ 5

  shift₁ : Bool ⇨ Bool × Bool
  shift₁ = dup ∘ delay false

  shifts : ∀ n → Bool ⇨ Bool ↑ n
  shifts n = exl ∘ (shift₁ ↱ n)

  -- General feedback right-shift register
  fsr : ∀ {n} → (Bool ↑ n ⇨ Bool) → Bool ↑ n ⇨ Bool ↑ n
  fsr f = shiftR ∘ (f △ id)

  -- linear : ∀ {n} → ⟦ Bool ↑ n ⟧ → Bool ↑ n ⇨ Bool
  -- linear {zero}  cs = {!!}
  -- linear {suc n} cs = {!!}

exampleˢ : ∀ {i o} → String → i s.⇨ o → IO {0ℓ} ⊤′
exampleˢ name (s.mealy {s} state₀ f) =
  do putStrLn name
     writeFile ("Figures/" ++ name ++ ".dot") (dot state₀ (sf.compile f))

exampleᶜ : ∀ {i o} → String → i c.⇨ o → IO {0ℓ} ⊤′
exampleᶜ name f = exampleˢ name (s.comb f)


main = run do

  -- exampleᶜ "id"        ce.t₁
  -- exampleᶜ "and"       ce.t₂
  -- exampleᶜ "nand"      ce.t₃
  -- exampleᶜ "first-not" ce.t₄
  -- exampleᶜ "not"       ce.t₅
  -- exampleᶜ "half-add-c"   ce.halfAdd

  -- exampleˢ "toggle"    se.t₁
  -- exampleˢ "toggleB"   se.t₁′
  -- exampleˢ "any"       se.t₂
  -- exampleˢ "delay-1"   se.t₃
  -- exampleˢ "delay-3"   se.t₄
  -- exampleˢ "delay×2"   se.t₅
  -- exampleˢ "delay×4"   se.t₆
  -- exampleˢ "delay×8"   se.t₇

  -- exampleˢ "toggle-1"   se.toggle₁
  -- exampleˢ "toggle-2"   se.toggle₂
  -- exampleˢ "toggle-4"   se.toggle₄
  -- exampleˢ "toggles"    se.toggles

  -- exampleˢ "shift-1" se.shift₁
  -- exampleˢ "shift-5" (se.shifts 5)

  exampleᶜ "shiftR-5" (ce.shiftRs {5})
