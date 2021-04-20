{-# OPTIONS --safe --without-K #-}
-- Generate GraphViz/Dot format from stack morphism

module Dot where

open import Data.Product using (_,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String hiding (toList; concat; show)
open import Data.List using (List; []; _∷_; concat; map; upTo)
  renaming (_++_ to _++ᴸ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Category
open import Ty renaming (map to mapᵀ)

import Primitive as p    -- for Show
open import Stack ; open k using (_◦_◦_; ⌞_⌟)

private variable a b c d i o s z zⁱ zᵒ zᵃ : Ty

package : List String → String
package = (_++ "\n}\n") ∘ ("digraph {" ++_) ∘ ("\n" ++_) ∘
          unlines ∘ map (λ s → "  " ++ s ++ ";") ∘ (prelude ++ᴸ_)
 where
   prelude : List String
   prelude =
     "margin=0" ∷
     "rankdir=LR" ∷
     "node [shape=Mrecord]" ∷
     "bgcolor=transparent" ∷
     "nslimit=20" ∷
     "ranksep=0.75" ∷
     []

-- Output port name
OPort : Set
OPort = String

labels : String → (String → String) → Ty → String
labels tag f a with size a
... | zero = ""   -- No braces or "|", to avoid port appearance
... | n@(suc _) = f (braces (
 intersperse "|" (map (λ i → "<" ++ tag ++ show i ++ ">") (upTo n))))

labelsⁱ : Ty → String
labelsⁱ = labels "In" (_++ "|")

labelsᵒ : Ty → String
labelsᵒ = labels "Out" ("|" ++_)

showIx : TyIx a → String
showIx = show ∘ toFin

wire : String → TyIx a → OPort → String
wire compName i oport = oport ++ " -> " ++  compName ++ ":In" ++ showIx i

-- open import Function using (_∋_)
-- _ : wire "Foo" (TyIx (Bool ↑ 5) ∋ right (right (left here)))
--        "c2:Out4" ≡ "c2:Out4 -> Foo:In2"
-- _ = refl

comp : String → String → TyF OPort i → Ty → List String
comp {i} compName opName ins o with size i | size o
... | zero | zero = []  -- drop disconnected components (input or output)
... | _    | _    =
  (compName ++
   " [label=\"" ++
   braces (labelsⁱ i ++ opName ++ labelsᵒ o) ++
   "\"]")
  ∷ toList (mapᵀ (wire compName) allIx ⊛ ins)

oport : String → TyIx a → OPort
oport compName o = compName ++ ":Out" ++ showIx o

module _ {s} (stateF₀ : ⊤ sf.⇨ s) where

  state₀ : ⟦ s ⟧
  state₀ = ⟦ ⟦ stateF₀ ⟧ ⟧ tt
  
  reg : TyIx a → String
  reg j = "reg" ++ showIx j

  register : TyIx s → Bool → OPort → List String
  register j s₀ src = comp (reg j) ("cons " ++ show s₀) [ src ] Bool

  codᵖ : (a p.⇨ b) → Ty
  codᵖ {b = b} _ = b

  dotᵏ : ℕ → TyF OPort (i × zⁱ) → (i , zⁱ k.⇨ (o × s) , ⊤) → List String
  dotᵏ _ ins ⌞ r ⌟ with r.⟦ unitorᵉʳ ∘ r ⟧′ ins ; ... | os ､ ss =
    concat (toList (mapᵀ register allIx ⊛ →TyF state₀ ⊛ ss))
    ++ᴸ comp "output" "output" os ⊤

  dotᵏ comp# ins (f ◦ p ◦ r) with r.⟦ r ⟧′ ins ; ... | os ､ ss =
    let compName = "c" ++ show comp# in
      comp compName (show p) os (codᵖ p)
      ++ᴸ dotᵏ (suc comp#) (mapᵀ (oport compName) allIx ､ ss) f

  dot : i × s sf.⇨ o × s → String
  dot {i = i} (sf.mk f) = package (
    comp "input" "input" · i ++ᴸ
    dotᵏ 0 (( mapᵀ (oport "input") allIx ､
              mapᵀ (λ r → oport (reg r) here) allIx) ､ ·) f)

  -- TODO: Consider reworking with stateF₀ as input to registers
