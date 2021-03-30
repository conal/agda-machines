module Test where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Unit.Polymorphic
open import Data.Bool using (true; false)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String
open import IO

open import Symbolic.ExtrinsicVec

open import StackFunction using (compile)
open import Dot

-- Combinational examples
module ce where
  open c

  t₁ = id {10}

  t₂ = prim p.∧

  t₃ = prim p.not ∘ prim p.∧

  t₄ : 3 ⇨ 3
  t₄ = first (prim p.not)

  t₅ = prim p.not

-- Sequential examples
module se where
  open s

  -- Toggle
  t₁ : 0 ⇨ 1
  t₁ = mealy [ true ] (c.dup c.∘ c.prim p.not c.∘ c.exr {0}{1})
  -- λ { (tt , s) → (not s , not s) }

  -- Cumulative or
  t₂ : 1 ⇨ 1
  t₂ = mealy [ false ] (c.dup c.∘ c.prim p.∨)
  -- λ { (b , s) → (b ∨ s , b ∨ s) }

  t₃ = delay (false ∷ [])

  t₄ = delay (false ∷ true ∷ false ∷ [])

  t₅ = delay [ false ] ∘ delay [ true ]

exampleˢ : ∀ {i o} → String → i s.⇨ o → IO {0ℓ} ⊤
exampleˢ {i = i} name (s.mealy {s} state₀ f) =
  do putStrLn name
     writeFile ("figures/" ++ name ++ ".dot") (dot {s = s} state₀ {i = i} (compile f))

exampleᶜ : ∀ {i o} → String → i c.⇨ o → IO {0ℓ} ⊤
exampleᶜ name f = exampleˢ name (s.comb f)


main = run do

  exampleᶜ "id"        ce.t₁
  exampleᶜ "and"       ce.t₂
  exampleᶜ "nand"      ce.t₃
  exampleᶜ "first-not" ce.t₄
  exampleᶜ "not"       ce.t₅

  exampleˢ "toggle"    se.t₁
  exampleˢ "any"       se.t₂
  exampleˢ "delay-1"   se.t₃
  exampleˢ "delay-3"   se.t₄
  exampleˢ "delay×2"   se.t₅
