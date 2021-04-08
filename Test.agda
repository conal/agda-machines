-- Miscellaneous circuit graph examples

module Test where

open import Level using (0ℓ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Bool using (if_then_else_) renaming (false to 𝕗; true to 𝕥)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (subst)
open import IO

open import Category ; open CartUtils
open import Ty
import Primitive as p
open import Stack p._⇨_ using (module sf)
import Mealy sf._⇨_ as m
open import Dot

-- open CartUtils

open TyUtils

-- Combinational examples
module ce where
  open sf

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

  shiftR-swap : ∀ {n} → Bool × Bool ↑ n ⇨ Bool × Bool ↑ n
  shiftR-swap = swap ∘ shiftR

  -- General feedback right-shift register
  fsr : ∀ n → (Bool ↑ n ⇨ Bool) → (Bool ↑ n ⇨ Bool ↑ n)
  fsr _ f = shiftR⇃ ∘ (f △ id)

  linear : ∀ n → Bool ↑ suc n → Bool ↑ suc n ⇨ Bool
  linear zero (c , tt) = unitorᵉʳ
  linear (suc n) (c , cs) = (if c then xor else exr) ∘ second (linear n cs)

  lfsr : ∀ n → Bool ↑ suc n → Bool ↑ suc n ⇨ Bool ↑ suc n
  lfsr n cs = fsr (suc n) (linear n cs)

  lfsr₅ : Bool ↑ 6 ⇨ Bool ↑ 6
  lfsr₅ = lfsr 5 (𝕥 , 𝕗 , 𝕗 , 𝕥 , 𝕗 , 𝕥 , tt)

-- Sequential examples
module se where
  open m

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

  t₄ = delay (false ⦂ true ⦂ false)

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

  -- Shift and accumulate results
  shift₁ : Bool ⇨ Bool × Bool
  shift₁ = dup ∘ delay false

  shifts : ∀ n → Bool ⇨ Bool ↑ n
  shifts n = exl ∘ (shift₁ ↱ n)

  -- Wrap swap ∘ shiftR as a sequential computation. The fine-grain dependencies
  -- (one register per bit) unravel the mealy loop into a chain.
  shiftR-swap : ∀ n → Bool ⇨ Bool
  shiftR-swap n = mealy (replicate′ n false) (ce.shiftR-swap {n})

  shiftR-swap-loop : ∀ n → ⊤ ⇨ ⊤
  shiftR-swap-loop n =
    mealy (replicate′ (suc n) false) (second (ce.shiftR-swap {n}))

  shiftR-swap-loop-xor : ∀ n → Bool ⇨ Bool
  shiftR-swap-loop-xor n =
    mealy (replicate′ (suc n) false)
          (assocʳ ∘ first dup ∘ ce.shiftR-swap {n} ∘ first xor ∘ assocˡ)

  shiftR-swap-loop-xor-out : ∀ n → Bool ⇨ Bool ↑ suc n
  shiftR-swap-loop-xor-out n =
    mealy (replicate′ (suc n) false)
          (dup ∘ ce.shiftR-swap {n} ∘ first xor ∘ assocˡ)

  -- Linear feedback right-shift register, given coefficients and initial value
  lfsr : ∀ n → Bool ↑ suc n → ⌞ Bool ↑ suc n ⌟ → ⊤ ⇨ Bool ↑ suc n
  lfsr n cs s₀ = mealy s₀ (dup ∘ ce.lfsr n cs ∘ unitorᵉˡ)

  lfsr₅ : ⊤ ⇨ Bool ↑ 6
  lfsr₅ = lfsr 5 (𝕥 , 𝕗 , 𝕗 , 𝕥 , 𝕗 , 𝕥 , tt)
                 (false ⦂ true ⦂ false ⦂ true ⦂ true ⦂ false ⦂ !)

exampleˢ : ∀ {i o} → String → i m.⇨ o → IO {0ℓ} ⊤′
exampleˢ name (m.mealy state₀ f) =
  do putStrLn name
     writeFile ("Figures/" ++ name ++ ".dot") (dot state₀ f)

exampleᶜ : ∀ {i o} → String → i sf.⇨ o → IO {0ℓ} ⊤′
exampleᶜ name f = exampleˢ name (m.comb f)


main = run do

  -- exampleᶜ "id"        ce.t₁
  -- exampleᶜ "and"       ce.t₂
  -- exampleᶜ "nand"      ce.t₃
  -- exampleᶜ "first-not" ce.t₄
  -- exampleᶜ "not"       ce.t₅
  -- exampleᶜ "half-add-c"   ce.halfAdd
  -- exampleᶜ "shiftR-swap-c5" (ce.shiftR-swap {5})
  -- exampleᶜ "lfsr-c5"  ce.lfsr₅

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

  -- exampleˢ "lfsr-s5" se.lfsr₅

  -- exampleˢ "shiftR-swap-s5" (se.shiftR-swap 5)

  -- exampleˢ "shiftR-swap-loop-xor-out" (se.shiftR-swap-loop-xor-out 6)

  exampleˢ "shiftR-swap-loop-xor" (se.shiftR-swap-loop-xor 6)
