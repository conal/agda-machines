module Test where

open import Level
open import Data.Unit.Polymorphic
open import Data.String
open import IO

open import Symbolic.ExtrinsicVec ; open c

-- open import NetlistE using (compile)
-- open import Dot

open import StackFunction using (compile)
open import DotStack

module _ where

  t₁ : ∀ {a} → a ⇨ a
  t₁ = id

  -- t₂ : 2 ⇨ 1
  t₂ = prim p.∧

  t₃ = prim p.not ∘ prim p.∧

  t₄ : 2 ⇨ 2
  t₄ = first (prim p.not)

  t₅ = prim p.not

example : ∀ {a b} → String → a ⇨ b → IO {0ℓ} ⊤
example name f =
  do putStrLn name
     writeFile ("figures/" ++ name ++ ".dot") (dot (compile f))

open import Agda.Builtin.IO using () renaming (IO to IO′)

run-example : ∀ {a b} → String → a ⇨ b → IO′ ⊤
run-example name f = run (example name f)

main = run do
  example "id-3"      (t₁ {3})
  example "and"       t₂
  example "nand"      t₃
  example "first-not" t₄
  example "not"       t₅
