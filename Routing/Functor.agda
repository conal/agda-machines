{-# OPTIONS --safe --without-K #-}

module Routing.Functor where

open import Data.Product using (_,_)

open import Categorical.Raw
open import Categorical.Instances.Function.Raw

open import Ty.Raw hiding (_⇨_)
open import Routing.Raw

private
  variable
    A B C D : Ty
    X Y Z : Set

infixr 4 _､_

-- Ty-indexed representable functor
data TyF (X : Set) : Ty → Set where
  ·   : TyF X ⊤
  [_] : X → TyF X Bool
  _､_ : TyF X A → TyF X B → TyF X (A × B)

tabulate′ : (TyIx A → X) → TyF X A
tabulate′ {`⊤} f = ·
tabulate′ {`Bool} f = [ f here ]
tabulate′ {_ `× _} f = tabulate′ (f ∘ left) ､ tabulate′ (f ∘ right)

lookup′ : TyF X A → (TyIx A → X)
lookup′ [ x ] here = x
lookup′ (l ､ r) (left  a) = lookup′ l a
lookup′ (l ､ r) (right b) = lookup′ r b

swizzle′ : (TyIx B → TyIx A) → ∀ {X} → TyF X A → TyF X B
swizzle′ r a = tabulate′ (lookup′ a ∘ r)


⟦_⟧′ : A ⇨ B → ∀ {X} → TyF X A → TyF X B
⟦ mk f ⟧′ = swizzle′ f


→TyF : ⟦ A ⟧ᵗ → TyF Bool A
→TyF {`⊤} tt = ·
→TyF {`Bool} b = [ b ]
→TyF {_ `× _} (x , y) = →TyF x ､ →TyF y

TyF→ : TyF Bool A → ⟦ A ⟧ᵗ
TyF→ · = tt
TyF→ [ b ] = b
TyF→ (x ､ y) = TyF→ x , TyF→ y

-- TODO: Finish ⟦ A ⟧ ↔ TyF Bool A . Proofs should be much easier than with vectors.

-- Agsy synthesized all of the TyF operations above. (Tidying needed for most,
-- -c for all but swizzle′, and tabulate′ and lookup′ hints for swizzle′.)

-- Relate Ty values to vectors

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec using (Vec; []; _∷_)
  renaming (_++_ to _++ⁿ_; toList to toListⁿ)

size : Ty → ℕ
size `⊤       = 0
size `Bool    = 1
size (A `× B) = size A + size B

toFin : TyIx A → Fin (size A)
toFin here      = zero
toFin (left  i) = inject+ _ (toFin i)
toFin (right j) = raise   _ (toFin j)

toVec : TyF X A → Vec X (size A)
toVec · = []
toVec [ x ] = x ∷ []
toVec (u ､ v) = toVec u ++ⁿ toVec v

open import Data.List using (List)

toList : TyF X A → List X
toList = toListⁿ ∘ toVec

map : (X → Y) → TyF X A → TyF Y A
map f · = ·
map f [ x ] = [ f x ]
map f (u ､ v) = map f u ､ map f v

allFin : TyF (Fin (size A)) A
allFin {`⊤} = ·
allFin {`Bool} = [ zero ]
allFin {_ `× _} = map (inject+ _) allFin ､ map (raise _) allFin

allIx : TyF (TyIx A) A
allIx {`⊤} = ·
allIx {`Bool} = [ here ]
allIx {_ `× _} = map left allIx ､ map right allIx

infixl 4 _⊛_
_⊛_ : TyF (X → Y) A → TyF X A → TyF Y A
· ⊛ · = ·
[ f ] ⊛ [ x ] = [ f x ]
(fs ､ gs) ⊛ (xs ､ ys) = (fs ⊛ xs) ､ (gs ⊛ ys)

map₂ : (X → Y → Z) → TyF X A → TyF Y A → TyF Z A
map₂ f u v = map f u ⊛ v
