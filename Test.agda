module Test where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Data.Bool using (true; false)
open import Data.Vec using ([_]; []; _∷_)
open import Data.String
open import IO

open import Ty
open import Symbolic.Extrinsic
open import StackFunction using (compile)
open import Dot

-- Combinational examples
module ce where
  open c

  t₁ = id {Bool ↑ 5}

  t₂ = prim p.∧

  t₃ = prim p.not ∘ prim p.∧

  t₄ : Bool ↑ 3 ⇨ Bool ↑ 3
  t₄ = first (prim p.not)

  t₅ = prim p.not

-- Sequential examples
module se where
  open s

  -- Toggle
  t₁ : ⊤ ⇨ Bool
  t₁ = mealy true (c.dup c.∘ c.prim p.not c.∘ c.exr)
  -- λ { (tt , s) → (not s , not s) }

  -- Cumulative or
  t₂ : Bool ⇨ Bool
  t₂ = mealy false (c.dup c.∘ c.prim p.∨)
  -- λ { (b , s) → (b ∨ s , b ∨ s) }

  t₃ = delay false

  t₄ = delay (false , true , false)

  t₅ = delay false ∘ delay true

exampleˢ : ∀ {i o} → String → i s.⇨ o → IO {0ℓ} ⊤′
exampleˢ name (s.mealy {s} state₀ f) =
  do putStrLn name
     writeFile ("Figures/" ++ name ++ ".dot") (dot state₀ (compile f))

exampleᶜ : ∀ {i o} → String → i c.⇨ o → IO {0ℓ} ⊤′
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
