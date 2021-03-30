module DotTy where

open import Function using (_∘′_)
-- open import Data.Bool
-- open import Data.Product using (∃; _×_; _,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Fin.Show as FS
-- open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Nat.Show as NS
open import Data.String hiding (toList)
open import Data.Vec renaming (map to mapⁿ; _++_ to _++ⁿ_; toList to toListⁿ)
  hiding (allFin; lookup; _⊛_) -- TODO: trim imports
open import Data.List using (List; []; _∷_; map; upTo)
  renaming (_++_ to _++ˡ_; concat to concatˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ty renaming (map to mapT)
open import Symbolic.ExtrinsicTyB
open import StackFunctionTy

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
          unlines ∘′ map (λ s → "  " ++ s ++ ";") ∘′ (prelude ++ˡ_)

-- Output port name
OPort : Set
OPort = String

labels : String → Ty → String
labels tag a =
  braces (intersperse "|" (map (λ i → "<" ++ tag ++ NS.show i ++ ">") (upTo (size a))))

labelsⁱ : Ty → String
labelsⁱ = labels "In"

labelsᵒ : Ty → String
labelsᵒ = labels "Out"

showIx : TyIx a → String
showIx = FS.show ∘′ toFin

wire : String → TyIx a → OPort → String
wire compName i oport = oport ++ " -> " ++  compName ++ ":In" ++ showIx i

-- _ : wire "Foo" (suc (suc (zero {5}))) "c2:Out4" ≡ "c2:Out4 -> Foo:In2"
-- _ = refl

comp : String → String → TyF OPort i → Ty → List String
comp {i} compName opName ins o =
  (compName ++
   " [label=\"" ++
   braces (labelsⁱ i ++ "|" ++ opName ++ "|" ++ labelsᵒ o) ++
   "\"]")
  ∷ toList (mapT (wire compName) allIx ⊛ ins)

oport : String → TyIx a → OPort
oport compName o = compName ++ ":Out" ++ showIx o

module _ {s} (state₀ : ⟦ s ⟧ᵗ) where

  reg : TyIx a → String
  reg j = "reg" ++ FS.show (toFin j)

  register : TyIx s → Boolᵗ → OPort → List String
  register j s₀ src =
    comp ("reg" ++ showIx j) ("cons " ++ showBit (lookup state₀ j)) (bit src) Bool

  dotᵏ : Ty → TyF OPort (i × zⁱ) → (i , zⁱ k.⇨ (o × s) , ⊤) → List String

  dotᵏ comp# ins k.[ r ] with r.⟦ r.unitorᵉʳ r.∘ r ⟧′ ins
  ...                       | pair os ss =
    concatˡ (toList (mapT register allIx ⊛ →TyF state₀ ⊛ ss))
    ++ˡ comp "output" "output" os comp#

  dotᵏ comp# ins (f k.∷ʳ x) = {!!}

  -- dotᵏ {o = o} comp# ins k.[ r ] =
  --   let os , q , _ = splitAt o (r′.⟦ r′.assocʳ {A = OPort}{a = o}{s} r.∘ r ⟧ ins)
  --       ss , _ , _ = splitAt s q in
  --   concatˡ (toList (mapⁿ register (allFin s) ⊛ state₀ ⊛ ss))
  --   ++ˡ comp "output" "output" os comp#
  --   -- TODO: I think zᵒ must be zero here (empty stack). Can I enforce with types?
  -- dotᵏ {o = o} comp# ins (f k.∷ʳ (a , a⇨ₚb , i×zⁱ⇨ᵣa×zᵃ)) =
  --   let ins′ = r′.⟦ i×zⁱ⇨ᵣa×zᵃ ⟧ ins
  --       #o = p.#outs a⇨ₚb  -- or get from an implicit
  --       compName = "c" ++ NS.show comp#
  --       oports = mapⁿ (oport compName) (allFin #o)
  --       compIns , restIns , _ = splitAt a ins′
  --   in
  --     comp compName (p.show a⇨ₚb) compIns #o
  --     ++ˡ dotᵏ {o = o} (suc comp#) (oports ++ⁿ restIns) f

--   dot : i + s sf.⇨ o + s → String
--   dot {i = i} f = package (
--     comp "input" "input" [] i ++ˡ
--     dotᵏ 0 (b′.unitorⁱʳ (mapⁿ (oport "input") (allFin i) ++ⁿ
--                          mapⁿ (λ r → oport ("reg" ++ FS.show r) (zero {1})) (allFin s)))
--            (f {0}))
