module DotStack where

open import Data.Product using (∃; _×_; _,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Fin.Show as FS
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Nat.Show as NS
open import Data.String hiding (toList)
open import Data.Vec hiding (_++_) renaming (map to mapV)
open import Data.List using (List; []; _∷_; map; upTo)
  renaming (_++_ to _++ˡ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Symbolic.ExtrinsicVec
open import StackFunction

-- I didn't find this function in agda-std.
map₂ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
     → (A → B → C) → Vec A n → Vec B n → Vec C n 
map₂ f as bs = mapV f as ⊛ bs

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
  ∷ toList (map₂ (wire compName) ins (allFin i))

dotˢ : ℕ → Vec OPort (i + sⁱ) → (i , sⁱ k.⇨ o , sᵒ) → List String

dotˢ comp# ins k.[ r ] = comp "output" "output" (r′.⟦ r ⟧ ins) comp#

dotˢ comp# ins (f k.∷ʳ (a , a⇨ₚb , i+sⁱ⇨ᵣa+sᵃ)) =
  comp ("c" ++ NS.show comp#) (p.show a⇨ₚb)
    {!!} (p.#outs a⇨ₚb)
  ++ˡ dotˢ (suc comp#) {!!} f

-- dot : a sf.⇨ b → String
-- dot f = dotˢ (f {0})

