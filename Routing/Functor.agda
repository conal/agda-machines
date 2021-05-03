{-# OPTIONS --safe --without-K #-}

module Routing.Functor where

open import Level using (0ℓ)
open import Data.Product using (_,_)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws

-- open import Ty.Raw hiding (_⇨_)
-- open import Routing.Raw

open import Typed.Raw (Function {0ℓ}) renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism (Function {0ℓ}) 0ℓ
open import Typed.Laws         (Function {0ℓ}) 0ℓ

-- -- I don't know why the following alternative leads to problems
-- open import Typed (Function {0ℓ}) 0ℓ renaming (_⇨_ to _⇨ₜ_)

open import Routing.Raw

private
  variable
    a b c d : Ty
    X Y Z : Set

infixr 4 _､_

-- Ty-indexed representable functor
data TyF (X : Set) : Ty → Set where
  ·   : TyF X ⊤
  [_] : X → TyF X Bool
  _､_ : TyF X a → TyF X b → TyF X (a × b)

tabulate′ : (TyIx a → X) → TyF X a
tabulate′ {`⊤} f = ·
tabulate′ {`Bool} f = [ f here ]
tabulate′ {_ `× _} f = tabulate′ (f ∘ left) ､ tabulate′ (f ∘ right)

lookup′ : TyF X a → (TyIx a → X)
lookup′ [ x ] here = x
lookup′ (l ､ r) (left  a) = lookup′ l a
lookup′ (l ､ r) (right b) = lookup′ r b

swizzle′ : (TyIx b → TyIx a) → ∀ {X} → TyF X a → TyF X b
swizzle′ r a = tabulate′ (lookup′ a ∘ r)


⟦_⟧′ : a ⇨ b → ∀ {X} → TyF X a → TyF X b
⟦ mk f ⟧′ = swizzle′ f


→TyF : ⟦ a ⟧ → TyF Bool a
→TyF {`⊤} tt = ·
→TyF {`Bool} b = [ b ]
→TyF {_ `× _} (x , y) = →TyF x ､ →TyF y

TyF→ : TyF Bool a → ⟦ a ⟧
TyF→ · = tt
TyF→ [ b ] = b
TyF→ (x ､ y) = TyF→ x , TyF→ y

-- TODO: Finish ⟦ a ⟧ ↔ TyF Bool a . Proofs should be much easier than with vectors.

-- Agsy synthesized all of the TyF operations above. (Tidying needed for most,
-- -c for all but swizzle′, and tabulate′ and lookup′ hints for swizzle′.)

-- Relate Ty values to vectors

open import Data.Fin hiding (_+_)
open import Data.Vec using (Vec; []; _∷_)
  renaming (_++_ to _++ⁿ_; toList to toListⁿ)

toFin : TyIx a → Fin (size a)
toFin here      = zero
toFin (left  i) = inject+ _ (toFin i)
toFin (right j) = raise   _ (toFin j)

toVec : TyF X a → Vec X (size a)
toVec · = []
toVec [ x ] = x ∷ []
toVec (u ､ v) = toVec u ++ⁿ toVec v

open import Data.List using (List)

toList : TyF X a → List X
toList = toListⁿ ∘ toVec

map : (X → Y) → TyF X a → TyF Y a
map f · = ·
map f [ x ] = [ f x ]
map f (u ､ v) = map f u ､ map f v

allFin : TyF (Fin (size a)) a
allFin {`⊤} = ·
allFin {`Bool} = [ zero ]
allFin {_ `× _} = map (inject+ _) allFin ､ map (raise _) allFin

allIx : TyF (TyIx a) a
allIx {`⊤} = ·
allIx {`Bool} = [ here ]
allIx {_ `× _} = map left allIx ､ map right allIx

infixl 4 _⊛_
_⊛_ : TyF (X → Y) a → TyF X a → TyF Y a
· ⊛ · = ·
[ f ] ⊛ [ x ] = [ f x ]
(fs ､ gs) ⊛ (xs ､ ys) = (fs ⊛ xs) ､ (gs ⊛ ys)

map₂ : (X → Y → Z) → TyF X a → TyF Y a → TyF Z a
map₂ f u v = map f u ⊛ v
