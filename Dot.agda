-- Generate dot format of a netlist

module Dot where

open import Data.Product using (_,_; _×_; proj₂)
open import Data.Nat
open import Data.Nat.Show as NS
-- open import Data.Fin using (Fin; splitAt; toℕ)
open import Data.Fin hiding ()
open import Data.Fin.Show as FS
open import Data.Sum using ([_,_])
open import Data.String
open import Data.List using (List; _∷_; map; upTo)
import Data.Vec as V

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Misc as F
open import Symbolic.ExtrinsicVec
open import NetlistE

private variable a b c d j k : ℕ

labels : String → ℕ → String
labels tag n =
  braces (intersperse "|" (map (λ i → "<" ++ tag ++ NS.show i ++ ">") (upTo n)))

labelsⁱ : ℕ → String
labelsⁱ = labels "In"

labelsᵒ : ℕ → String
labelsᵒ = labels "Out"

-- Input component and port number
portⁱ : ℕ → Fin a → String
portⁱ comp# a = "c" ++ NS.show comp# ++ ":" ++ "In" ++ FS.show a

-- Output component and port number
portᵒ : ℕ → Netlist k → Fin k → String
portᵒ comp# (_∷_ {j = j} inst nl) i =
  [ (λ o → "c" ++ NS.show comp# ++ FS.show o)
  , (λ o → portᵒ (suc comp#) nl o)
  ] (splitAt j i)

_ : labelsⁱ 5 ≡ "{<In0>|<In1>|<In2>|<In3>|<In4>}"
_ = refl

dotⁱ : ℕ → Inst k b → Netlist k → String
dotⁱ {b = b} comp# (a , a⇨ₚb , k⇨ᵣa) nl = unlines (
  ("c" ++ NS.show comp# ++
   "[label=\"" ++
   braces (labelsⁱ a ++ "|" ++ p.show a⇨ₚb ++ "|" ++ labelsᵒ b) ++
   "\"];")
  ∷ map (λ i → portᵒ comp# nl (k⇨ᵣa i) ++ " -> " ++ portⁱ comp# i ++ " [];")
        (V.toList (V.allFin a)))

_ : portⁱ 4 (suc (suc (zero {3}))) ≡ "c4:In2"
_ = refl

-- {!p.show a⇨ₚb!}

--   c0 [label="{{<In0>|<In1>}|+|{<Out0>}}"];
--
--   c18:Out0 -> c31:In7 [];

dotⁿ : ℕ → Netlist k → String
dotⁿ n [] = ""
dotⁿ n (inst ∷ nl) = dotⁱ n inst nl ++ dotⁿ (suc n) nl

dot : a ⇨ b → String
dot f = dotⁿ 0 (proj₂ (sealⁿ f))

-- The performance might suffer from using lists and multiple traversals
-- (potentially quadratic). TODO: explore alternatives, such AVL trees.
