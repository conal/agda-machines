-- Expression-quoting macro

module Tinkering.Reflection.Quote where

open import Function
open import Data.Unit
open import Data.List
open import Data.Nat

open import Reflection

macro
  Q : ∀ {a}{A : Set a} → A → Term → TC ⊤
  Q x hole = quoteTC x >>= quoteTC >>= unify hole

-- Use example: "C-c C-n Q λ x → x + 3". Result:
--
--   lam visible
--   (abs "x"
--    (def (quote _+_) (vArg (var 0 []) ∷ vArg (lit (nat 3)) ∷ [])))
