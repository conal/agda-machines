module Test where

open import Level using (0ℓ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
import Data.Bool as B  -- temporary
open import Data.Bool using (true; false; if_then_else_)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String
open import Relation.Binary.PropositionalEquality using (subst)
open import IO

import Category as C
open C ; open CartUtils
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

  t₂ : Bool × Bool ⇨ Bool
  t₂ = ∧

  t₃ : Bool × Bool ⇨ Bool
  t₃ = not ∘ ∧

  t₄ : Bool ↑ 3 ⇨ Bool ↑ 3
  t₄ = first (not)

  t₅ = not

  -- Summands ⇨ sum , carry
  -- λ (a , b) → (a ⊕ b , a ∧ b)
  halfAdd : Bool × Bool ⇨ Bool × Bool
  halfAdd = xor △ ∧

  shiftRs : ∀ {n} → Bool × Bool ↑ n ⇨ Bool ↑ n
  shiftRs = shiftR⇃

  -- General feedback right-shift register
  fsr : ∀ n → (Bool ↑ n ⇨ Bool) → (Bool ↑ n ⇨ Bool ↑ n)
  fsr _ f = shiftR⇃ ∘ (f △ id)

  linear : ∀ n → Bool ↑ suc n → Bool ↑ suc n ⇨ Bool
  linear zero (c , tt) = unitorᵉʳ
  linear (suc n) (c , cs) = (if c then xor else exr) ∘ second (linear n cs)

  lfsr : ∀ n → Bool ↑ suc n → Bool ↑ suc n ⇨ Bool ↑ suc n
  lfsr n cs = fsr (suc n) (linear n cs)

  lfsr₅ : Bool ↑ 6 ⇨ Bool ↑ 6
  lfsr₅ = lfsr 5 (true , false , false , true , false , true , tt)

-- Sequential examples
module se where
  open s

  -- Toggle
  t₁ : ⊤ ⇨ Bool
  t₁ = mealy true (dup ∘ not ∘ exr)
  -- λ { (tt , s) → (not s , not s) }

  -- Toggle
  t₁′ : ⊤ ⇨ Bool
  t₁′ = mealy true (first (not) ∘ dup ∘ exr)
  -- λ { (tt , s) → (s , not s) }

  -- Cumulative or
  t₂ : Bool ⇨ Bool
  t₂ = mealy false (dup ∘ ∨)
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

  -- Linear feedback right-shift register, given coefficients and initial value
  lfsr : ∀ n → Bool ↑ suc n → Bool ↑ suc n → ⊤ ⇨ Bool ↑ suc n
  lfsr n cs s₀ =
    mealy (subst id (Bool ⟦↑⟧ suc n) s₀) (dup ∘ ce.lfsr n cs ∘ unitorᵉˡ)

  lfsr₅ : ⊤ ⇨ Bool ↑ 6
  lfsr₅ = lfsr 5 (true , false , false , true , false , true , tt)
                 (false , true , false , true , true , false , tt)

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
  -- exampleᶜ "shiftR-5" (ce.shiftRs {5})
  -- exampleᶜ "lfsr-c5" ce.lfsr₅

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

  exampleˢ "lfsr-s5" se.lfsr₅
