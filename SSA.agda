{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

-- To insert before Dot.

module SSA where

open import Level using (Level; 0ℓ)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.String hiding (toList; show)
open import Data.List using (List; []; _∷_)

open import Categorical.Raw
open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws

open import Linearize.Simple

private variable a b : Ty

Id : Set
Id = String

Ref : Ty → Set
Ref = TyF Id

record Statement : Set where
  constructor _:=_·_
  field
    outs  : List Id
    prim  : String
    ins   : List Id

instance
  show-Statement : Show Statement
  show-Statement = record { show = λ (outs := prim · ins) →
     intersperse " , " outs ++ " = " ++ prim ++ parens (intersperse " , " outs)
   }

SSA : Set
SSA = List Statement

-- Construct an assignment and bump the free variable counter.
mkRefs : ℕ → Ref b × ℕ
mkRefs {b = b} i = mapᵀ (λ j → "x" ++ show (i + toℕ j)) allFin , i + size b

ssaᵏ : ℕ → Ref a → (a ⇨ₖ b) → SSA
ssaᵏ _ ins ⌞ r ⌟ = [] := "Out" · toList (⟦ r ⟧′ ins) ∷ []
ssaᵏ i ins (f ∘·first p ∘ r) with ⟦ r ⟧′ ins ; ... | x ､ y =
  let os , i′ = mkRefs i in toList os := show p · toList x ∷ ssaᵏ i′ (os ､ y) f

ssa : (a ⇨ₖ b) → SSA
ssa f = let ins , i = mkRefs 0 in ssaᵏ i ins f
