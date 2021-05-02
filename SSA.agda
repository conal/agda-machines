{-# OPTIONS --safe --without-K #-}

-- Generate static single assignment form from linearized morphism.

-- To insert before Dot.

module SSA where

open import Level using (Level; 0ℓ)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; toℕ; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.String hiding (toList; concat; show)
open import Data.List using (List; []; _∷_; concat; map; upTo)
  renaming (_++_ to _++ᴸ_)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws
open import Categorical.Homomorphism

private

  _↠_ : Set → Set → Set
  _↠_ = Function {0ℓ}

  q : Level
  q = 0ℓ

open import Typed.Raw _↠_ as t using (Ty) renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism _↠_ q
open import Typed.Laws _↠_ q

open import Primitive _↠_ q as p using () renaming (_⇨_ to _⇨ₚ_)

import Routing.Raw as r ; open r using (TyIx) renaming (_⇨_ to _⇨ᵣ_)
import Routing.Homomorphism
open import Routing.Functor renaming (map to mapᵀ)

open import Linearize.Raw _⇨ₜ_ _⇨ₚ_ _⇨ᵣ_ 0ℓ as k
  using (_∘·first_∘_; ⌞_⌟) renaming (_⇨_ to _⇨ₖ_)
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

Prog : Set
Prog = List Statement

-- Construct an assignment and bump the free variable counter.
mkRefs : ℕ → Ref b × ℕ
mkRefs {b = b} i = mapᵀ (λ j → "x" ++ show (i + toℕ j)) allFin , i + size b

ssaᵏ : ℕ → Ref a → (a ⇨ₖ b) → Prog
ssaᵏ _ ins ⌞ r ⌟ = [] := "Out" · toList (⟦ r ⟧′ ins) ∷ []
ssaᵏ i ins (f ∘·first p ∘ r) with ⟦ r ⟧′ ins ; ... | x ､ y =
  let os , i′ = mkRefs i in toList os := show p · toList x ∷ ssaᵏ i′ (os ､ y) f

ssa : (a ⇨ₖ b) → Prog
ssa f = let ins , i = mkRefs 0 in ssaᵏ i ins f

instance
  show-Statement : Show Statement
  show-Statement = record { show = λ (outs := prim · ins) →
     intersperse " , " outs ++ " = " ++ prim ++ parens (intersperse " , " outs)
   }
