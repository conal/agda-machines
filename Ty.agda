{-# OPTIONS --safe --without-K #-}

module Ty where

open import Data.Unit renaming (⊤ to ⊤ᵗ) public
open import Data.Bool using () renaming (Bool to Boolᵗ) public
open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Show as BS
open import Data.Product using (_,_; uncurry) renaming (_×_ to _×ᵗ_) public
open import Data.Nat
open import Data.String hiding (toVec; toList)

import Misc as F

infixr 2 _×_
data Ty : Set where
  ⊤    : Ty
  Bool : Ty
  _×_  : Ty → Ty → Ty

private variable A B C D : Ty

infixl 8 _↑_
_↑_ : Ty → ℕ → Ty
A ↑ zero  = ⊤
A ↑ suc zero = A
A ↑ suc (suc n) = A × A ↑ suc n

⟦_⟧ᵗ : Ty → Set
⟦ ⊤ ⟧ᵗ     = ⊤ᵗ
⟦ σ × τ ⟧ᵗ = ⟦ σ ⟧ᵗ ×ᵗ ⟦ τ ⟧ᵗ
⟦ Bool ⟧ᵗ  = Boolᵗ

showTy : ⟦ A ⟧ᵗ → String
showTy = go true
 where
   -- flag says we're in the left part of a pair
   go : Boolᵗ → ⟦ A ⟧ᵗ → String
   go {⊤} _ tt = "tt"
   go {Bool} _ b = BS.show b
   go {_ × _} p (x , y) = (if p then parens else F.id)
                          (go true x ++ "," ++ go false y)

infix 0 _→ᵗ_
_→ᵗ_ : Ty → Ty → Set
A →ᵗ B = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

-- Index of a bit in a type
data TyIx : Ty → Set where
  here : TyIx Bool
  left  : TyIx A → TyIx (A × B)
  right : TyIx B → TyIx (A × B)

-- Extract a bit
⟦_⟧ᵇ : ∀ {A} → TyIx A → A →ᵗ Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

tabulate : (TyIx A → Boolᵗ) → ⟦ A ⟧ᵗ
tabulate {⊤} f = tt
tabulate {Bool} f = f here
tabulate {_ × _} f = tabulate (f F.∘ left) , tabulate (f F.∘ right)

lookup : ⟦ A ⟧ᵗ → (TyIx A → Boolᵗ)
lookup a i = ⟦ i ⟧ᵇ a

swizzle : (TyIx B → TyIx A) → (⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ)
swizzle r a = tabulate (lookup a F.∘ r)

private variable X Y Z : Set

infixr 4 _､_

-- Ty-indexed representable functor
data TyF (X : Set) : Ty → Set where
  •   : TyF X ⊤
  [_] : X → TyF X Bool
  _､_ : TyF X A → TyF X B → TyF X (A × B)

tabulate′ : (TyIx A → X) → TyF X A
tabulate′ {⊤} f = •
tabulate′ {Bool} f = [ f here ]
tabulate′ {_ × _} f = tabulate′ (f F.∘ left) ､ tabulate′ (f F.∘ right)

lookup′ : TyF X A → (TyIx A → X)
lookup′ [ x ] here = x
lookup′ (l ､ r) (left  a) = lookup′ l a
lookup′ (l ､ r) (right b) = lookup′ r b

swizzle′ : (TyIx B → TyIx A) → ∀ {X} → TyF X A → TyF X B
swizzle′ r a = tabulate′ (lookup′ a F.∘ r)

→TyF : ⟦ A ⟧ᵗ → TyF Boolᵗ A
→TyF {⊤} tt = •
→TyF {Bool} b = [ b ]
→TyF {_ × _} (x , y) = →TyF x ､ →TyF y

TyF→ : TyF Boolᵗ A → ⟦ A ⟧ᵗ
TyF→ • = tt
TyF→ [ b ] = b
TyF→ (x ､ y) = TyF→ x , TyF→ y

-- TODO: Finish ⟦ A ⟧ᵗ ↔ TyF Boolᵗ A . Proofs should be much easier than with vectors.

-- Agsy synthesized all of the TyF operations above. (Tidying needed for most,
-- -c for all but swizzle′, and tabulate′ and lookup′ hints for swizzle′.)

-- Relate Ty values to vectors

open import Data.Vec using (Vec; []; _∷_)
  renaming (_++_ to _++ⁿ_; toList to toListⁿ)

size : Ty → ℕ
size ⊤       = 0
size Bool    = 1
size (A × B) = size A + size B

open import Data.Fin

toFin : TyIx A → Fin (size A)
toFin here      = zero
toFin (left  i) = inject+ _ (toFin i)
toFin (right j) = raise   _ (toFin j)

toVec : TyF X A → Vec X (size A)
toVec • = []
toVec [ x ] = x ∷ []
toVec (u ､ v) = toVec u ++ⁿ toVec v

open import Data.List using (List)

toList : TyF X A → List X
toList = toListⁿ F.∘ toVec

map : (X → Y) → TyF X A → TyF Y A
map f • = •
map f [ x ] = [ f x ]
map f (u ､ v) = map f u ､ map f v

allFin : TyF (Fin (size A)) A
allFin {⊤} = •
allFin {Bool} = [ zero ]
allFin {_ × _} = map (inject+ _) allFin ､ map (raise _) allFin

allIx : TyF (TyIx A) A
allIx {⊤} = •
allIx {Bool} = [ here ]
allIx {_ × _} = map left allIx ､ map right allIx

infixl 4 _⊛_
_⊛_ : TyF (X → Y) A → TyF X A → TyF Y A
• ⊛ • = •
[ f ] ⊛ [ x ] = [ f x ]
(fs ､ gs) ⊛ (xs ､ ys) = (fs ⊛ xs) ､ (gs ⊛ ys)

map₂ : (X → Y → Z) → TyF X A → TyF Y A → TyF Z A
map₂ f u v = map f u ⊛ v
