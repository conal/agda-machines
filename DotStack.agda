module DotStack where

open import Function using (_∘′_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Fin.Show as FS
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Nat.Show as NS
open import Data.String hiding (toList)
open import Data.Vec renaming (map to mapV; _++_ to _++ⁿ_)
open import Data.List using (List; []; _∷_; map; upTo)
  renaming (_++_ to _++ˡ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Symbolic.ExtrinsicVec
open import StackFunction

private variable a b c d i o s sⁱ sᵒ sᵃ : ℕ

-- Output port name
OPort : Set
OPort = String

labels : String → ℕ → String
labels tag n =
  braces (intersperse "|" (map (λ i → "<" ++ tag ++ NS.show i ++ ">") (upTo n)))

labelsⁱ : ℕ → String
labelsⁱ = labels "In"

labelsᵒ : ℕ → String
labelsᵒ = labels "Out"

wire : String → OPort → Fin i → String
wire compName oport i = oport ++ " -> " ++  compName ++ ":In" ++ FS.show i

_ : wire "Foo" "c2:Out4" (suc (suc (zero {5}))) ≡ "c2:Out4 -> Foo:In2"
_ = refl

-- c2:Out0 -> c1:In0 [];

-- For warm-up, just combinational

comp : String → String → Vec OPort i → ℕ → List String
comp {i} compName opName ins o =
  (compName ++
   " [label=\"" ++
   braces (labelsⁱ i ++ "|" ++ opName ++ "|" ++ labelsᵒ o) ++
   "\"]")
  ∷ toList (mapV (wire compName) ins ⊛ allFin i)

oport : String → Fin a → OPort
oport compName o = compName ++ ":Out" ++ FS.show o

dotᵏ : ℕ → Vec OPort (i + sⁱ) → (i , sⁱ k.⇨ o , sᵒ) → List String
dotᵏ comp# ins k.[ r ] =
  comp "output" "output" (r′.⟦ r ⟧ ins) comp#
dotᵏ comp# ins (f k.∷ʳ (a , a⇨ₚb , i+sⁱ⇨ᵣa+sᵃ)) =
  let ins′ = r′.⟦ i+sⁱ⇨ᵣa+sᵃ ⟧ ins
      #o = p.#outs a⇨ₚb  -- or get from an implicit
      compName = "c" ++ NS.show comp#
      oports = mapV (oport compName) (allFin #o)
      compIns , restIns , _ = splitAt a ins′
  in
    comp compName (p.show a⇨ₚb) compIns #o
    ++ˡ dotᵏ (suc comp#) (oports ++ⁿ restIns) f

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
package = (_++ "\n}\n") ∘′ ("digraph {" ++_) ∘′ ("\n" ++_) ∘′ unlines ∘′ map (λ s → "  " ++ s ++ ";") ∘′ (prelude ++ˡ_) -- ∘′ init

dot : a sf.⇨ b → String
dot {a} f = package (
  comp "input" "input" [] a ++ˡ
  dotᵏ 0 (b′.unitorⁱʳ (mapV (oport "input") (allFin a))) (f {0}))

