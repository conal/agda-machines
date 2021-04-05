module Test where

open import Level using (0ℓ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
import Data.Bool as B  -- temporary
open import Data.Bool using (true; false; if_then_else_)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (subst)
open import IO

open import Category ; open CartUtils
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
  lfsr₅ = lfsr 5 (B.true , B.false , B.false , B.true , B.false , B.true , tt)

-- Sequential examples
module se where
  open s

  -- Toggle
  t₁ : ⊤ ⇨ Bool
  t₁ = mealy B.true (dup ∘ not ∘ exr)
  -- λ { (tt , s) → (not s , not s) }

  -- Toggle
  t₁′ : ⊤ ⇨ Bool
  t₁′ = mealy B.true (first (not) ∘ dup ∘ exr)
  -- λ { (tt , s) → (s , not s) }

  -- Cumulative or
  t₂ : Bool ⇨ Bool
  t₂ = mealy B.false (dup ∘ ∨)
  -- λ { (b , s) → (b ∨ s , b ∨ s) }

  t₃ = delay B.false

  t₄ = delay (B.false , B.true , B.false)

  t₅ = delay B.false ∘ delay B.true

  t₆ = t₅ ∘ t₅

  t₇ = t₆ ∘ t₆

  -- Toggle with enable
  -- mealy false (λ (i , s) → ((i xor s , i ∧ s) , i xor s))
  toggle₁ : Bool ⇨ Bool × Bool
  toggle₁ = mealy B.false ((id △ exl) ∘ ce.halfAdd)

  toggle₂ = toggle₁ ◂ toggle₁
  toggle₄ = toggle₂ ◂ toggle₂

  toggles = toggle₁ ↱ 5

  -- Shift and accumulate results
  shift₁ : Bool ⇨ Bool × Bool
  shift₁ = dup ∘ delay B.false

  shifts : ∀ n → Bool ⇨ Bool ↑ n
  shifts n = exl ∘ (shift₁ ↱ n)

  -- Wrap swap ∘ shiftR as a sequential computation. The fine-grain dependencies
  -- (one register per bit) unravel the mealy loop into a chain.
  shiftR-swap : ∀ n → Bool ⇨ Bool
  shiftR-swap n = mealy (subst id (Bool ⟦↑⟧ n) (replicate n B.false)) (ce.shiftR-swap {n})

  shiftR-swap-loop : ∀ n → ⊤ ⇨ ⊤
  shiftR-swap-loop n =
    mealy (subst id (Bool ⟦↑⟧ suc n) (replicate (suc n) B.false))
          (second (ce.shiftR-swap {n}))

  shiftR-swap-loop-xor : ∀ n → Bool ⇨ Bool
  shiftR-swap-loop-xor n =
    mealy (subst id (Bool ⟦↑⟧ suc n) (replicate (suc n) B.false))
          (assocʳ ∘ first dup ∘ ce.shiftR-swap {n} ∘ first xor ∘ assocˡ)

  shiftR-swap-loop-xor-out : ∀ n → Bool ⇨ Bool ↑ suc n
  shiftR-swap-loop-xor-out n =
    mealy (subst id (Bool ⟦↑⟧ suc n) (replicate (suc n) B.false))
          (dup ∘ ce.shiftR-swap {n} ∘ first xor ∘ assocˡ)


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

  exampleˢ "shiftR-swap-loop-xor-out" (se.shiftR-swap-loop-xor-out 6)

  exampleˢ "shiftR-swap-loop-xor" (se.shiftR-swap-loop-xor 6)
