{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

-- To insert before Dot.

module SSA where

open import Level using (Level; 0ℓ)
open import Data.Product using (_,_; curry)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.String hiding (toList; show)
open import Data.List using (List; []; _∷_; upTo; zip; zipWith)
             renaming (map to mapᴸ; length to lengthᴸ)

-- open import Categorical.Raw
-- open import Categorical.Instances.Function.Raw
-- open import Categorical.Instances.Function.Laws

open import Function using (_∘_)
open import Data.Product using (_×_)
open import Data.Nat.Show using (show)

open import Linearize.Simple

private variable a b : Ty

-- Identifier as component/instance number and output index
Id : Set
Id = ℕ × ℕ

showId : Id → String
showId (comp# , out#) = "x" ++ show comp# ++ "_" ++ show out#

Ref : Ty → Set
Ref = TyF Id

record Statement : Set where
  constructor mk
  field
    #outs : ℕ
    prim  : String
    ins   : List Id

show-stmt : ℕ → Statement → String
show-stmt comp#  (mk #outs prim ins) =
     intersperse " , " (mapᴸ (curry showId comp#) (upTo #outs))
  ++ " = "
  ++ prim ++ parens (intersperse " , " (mapᴸ showId ins))

SSA : Set
SSA = List Statement

refs : ℕ → Ref b
refs comp# = mapᵀ (λ i → (comp# , toℕ i)) allFin

#outs : (a ⇨ₚ b) → ℕ
#outs {b = b} _ = size b

ssaᵏ : ℕ → Ref a → (a ⇨ₖ b) → SSA
ssaᵏ _ ins ⌞ r ⌟ = mk 0 "output" (toList (⟦ r ⟧′ ins)) ∷ []
ssaᵏ i ins (f ∘·first p ∘ r) with ⟦ r ⟧′ ins ; ... | x ､ y =
  mk (#outs p) (show p) (toList x) ∷ ssaᵏ (suc i) (refs i ､ y) f

ssa : (a ⇨ₖ b) → SSA
ssa {a} f = mk (size a) "input" [] ∷ ssaᵏ 1 (refs 0) f

tagℕ : {ℓ : Level} {A : Set ℓ} → List (ℕ × A)
tagℕ as = zip (upTo (lengthᴸ as)) as

show-SSA : SSA → String
show-SSA ssa = concat (zipWith show-stmt (upTo (lengthᴸ ssa)) ssa)

-- TODO: sort out what to make private.
