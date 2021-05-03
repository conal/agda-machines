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

open import Miscellany using (Function)

open import Categorical.Raw
open import Categorical.Instances.Function.Raw

open import Typed.Raw (Function {0ℓ}) renaming (_⇨_ to _⇨ₜ_)
open import Primitive.Type renaming (_⇨_ to _⇨ₚ_)
open import Routing.Type renaming (_⇨_ to _⇨ᵣ_)
open import Routing.Functor renaming (map to mapᵀ)

open import Linearize.Type _⇨ₜ_ _⇨ₚ_ _⇨ᵣ_ renaming (_⇨_ to _⇨ₖ_)

private variable a b : Ty

-- open primitive-instances

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
  mk (#outs p) (showₚ p) (toList x) ∷ ssaᵏ (suc i) (refs i ､ y) f

ssa : (a ⇨ₖ b) → SSA
ssa {a} f = mk (size a) "input" [] ∷ ssaᵏ 1 (refs 0) f

mapℕ : {A B : Set} → (ℕ → A → B) → List A → List B
mapℕ f as = zipWith f (upTo (lengthᴸ as)) as

show-SSA : SSA → String
show-SSA = concat ∘ mapℕ show-stmt

-- TODO: sort out what to make private.
