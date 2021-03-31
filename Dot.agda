module Dot where

open import Function using (_∘′_; _∋_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Fin.Show as FS
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show as NS
open import Data.String hiding (toList; concat)
open import Data.List using (List; []; _∷_; concat; map; upTo)
  renaming (_++_ to _++ᴸ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Category as C
open import Ty renaming (map to mapᵀ)
open import Symbolic.Extrinsic
open import Symbolic.StackProg

open C hiding (⊤; _×_)

private variable a b c d i o s z zⁱ zᵒ zᵃ : Ty

prelude : List String
prelude =
  "margin=0" ∷
  "rankdir=LR" ∷
  "node [shape=Mrecord]" ∷
  "bgcolor=transparent" ∷
  "nslimit=20" ∷
  "ranksep=0.75" ∷
  []

package : List String → String
package = (_++ "\n}\n") ∘′ ("digraph {" ++_) ∘′ ("\n" ++_) ∘′
          unlines ∘′ map (λ s → "  " ++ s ++ ";") ∘′ (prelude ++ᴸ_)

-- Output port name
OPort : Set
OPort = String

labels : String → (String → String) → Ty → String
labels tag f a with size a
... | zero = ""  -- No braces or "|", to avoid port appearance
... | n@(suc _) = f (braces (
 intersperse "|" (map (λ i → "<" ++ tag ++ NS.show i ++ ">") (upTo n))))

labelsⁱ : Ty → String
labelsⁱ = labels "In" (_++ "|")

labelsᵒ : Ty → String
labelsᵒ = labels "Out" ("|" ++_)

showIx : TyIx a → String
showIx = FS.show ∘′ toFin

wire : String → TyIx a → OPort → String
wire compName i oport = oport ++ " -> " ++  compName ++ ":In" ++ showIx i

_ : wire "Foo" (TyIx (Bool ↑ 5) ∋ right (right (left here)))
       "c2:Out4" ≡ "c2:Out4 -> Foo:In2"
_ = refl

comp : String → String → TyF OPort i → Ty → List String
comp {i} compName opName ins o =
  (compName ++
   " [label=\"" ++
   braces (labelsⁱ i ++ opName ++ labelsᵒ o) ++
   "\"]")
  ∷ toList (mapᵀ (wire compName) allIx ⊛ ins)

oport : String → TyIx a → OPort
oport compName o = compName ++ ":Out" ++ showIx o

module _ {s} (state₀ : ⟦ s ⟧ᵗ) where

  reg : TyIx a → String
  reg j = "reg" ++ showIx j

  register : TyIx s → Boolᵗ → OPort → List String
  register j s₀ src =
    comp (reg j) ("cons " ++ showBit (lookup state₀ j)) [ src ] Bool

  dotᵏ : ℕ → TyF OPort (i × zⁱ) → (i , zⁱ k.⇨ (o × s) , ⊤) → List String
  dotᵏ _ ins k.[ r ] with r.⟦ unitorᵉʳ ∘ r ⟧′ ins
  ...                       | os ､ ss =
    concat (toList (mapᵀ register allIx ⊛ →TyF state₀ ⊛ ss))
    ++ᴸ comp "output" "output" os ⊤

  dotᵏ comp# ins (f k.∷ʳ (a , a⇨ₚb , i×zⁱ⇨ᵣa×zᵃ)) with r.⟦ i×zⁱ⇨ᵣa×zᵃ ⟧′ ins
  ...                                                | os ､ ss =
    let compName = "c" ++ NS.show comp# in
      comp compName (C.show a⇨ₚb) os (p.cod a⇨ₚb)
      ++ᴸ dotᵏ (suc comp#) (mapᵀ (oport compName) allIx ､ ss) f

  dot : i × s sf.⇨ o × s → String
  dot {i = i} (sf.sf f) = package (
    comp "input" "input" • i ++ᴸ
    dotᵏ 0 (( mapᵀ (oport "input") allIx ､
              mapᵀ (λ r → oport (reg r) here) allIx) ､ •) f)
