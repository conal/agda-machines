-- Generate dot format of a netlist

module Dot where

open import Data.Product using (_,_; _×_; proj₂)
open import Data.Nat
open import Data.Nat.Show as NS
open import Data.Fin using (Fin; splitAt; toℕ)
open import Data.Sum using ([_,_])
open import Data.String
open import Data.List using (List; _∷_; map; upTo)
-- open import Data.Vec using (Vec)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Misc as F
open import Symbolic.ExtrinsicVec
open import NetlistE

-- line : String → String
-- line = _++ ";\n"

private variable a b c d j k : ℕ

-- Output component and port number
portᵒ : ℕ → Netlist k → Fin k → String
portᵒ comp# (_∷_ {j = j} inst nl) i =
  [ (λ o → "c" ++ NS.show comp# ++ NS.show (toℕ o))
  , (λ o → portᵒ (suc comp#) nl o)
  ] (splitAt j i)

labels : String → ℕ → String
labels tag n =
  braces (intersperse "|" (map (λ i → "<" ++ tag ++ NS.show i ++ ">") (upTo n)))

labelsⁱ : ℕ → String
labelsⁱ = labels "In"

labelsᵒ : ℕ → String
labelsᵒ = labels "Out"

_ : labelsⁱ 5 ≡ "{<In0>|<In1>|<In2>|<In3>|<In4>}"
_ = refl

dotⁱ : ℕ → Inst k b → Netlist k → String
dotⁱ {b = b} n (a , a⇨ₚb , k⇨ᵣa) nl = unlines (
  ("c" ++ NS.show n ++
   "[label=\"" ++
     braces (
       labelsⁱ a ++
       "|" ++ p.show a⇨ₚb ++ "|" ++
       labelsᵒ b) ++
   "\"];")
  ∷ {!!})

-- {!p.show a⇨ₚb!}

--   c0 [label="{{<In0>|<In1>}|+|{<Out0>}}"];
--
--   c18:Out0 -> c31:In7 [];

dotⁿ : ℕ → Netlist k → String
dotⁿ n [] = ""
dotⁿ n (inst ∷ nl) = dotⁱ n inst nl ++ dotⁿ (suc n) nl

dot : a ⇨ b → String
dot f = dotⁿ 0 (proj₂ (sealⁿ f))


{-

data Vec′ (F : ℕ → ℕ → Set) : ℕ → Set where
  [] : Vec′ F zero
  _∷_ : F k j → Vec′ F k → Vec′ F (j + k)

Inst k b = ∃ λ a → (a p.⇨ b) × (k r.⇨ a)

Netlist = Vec′ Inst

Src k a = Netlist k × (k r.⇨ a)

a ⇨ b = ∃ λ j → ∀ {k} → Src k a → Src (j + k) b

-}
