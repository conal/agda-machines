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


{-

open import Data.Nat
open import Data.Vec renaming (_++_ to _++ⁿ_)
open import Data.Vec.Properties using (++-injective)
open import Function using (_↔_; mk↔′)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

size : Ty → ℕ
size ⊤       = 0
size Bool    = 1
size (A × B) = size A + size B

→Vec : ⟦ A ⟧ᵗ → Vec Boolᵗ (size A)
→Vec {⊤} tt = []
→Vec {Bool} b = b ∷ []
→Vec {_ × _} (x , y) = →Vec x ++ⁿ →Vec y

Vec→ : Vec Boolᵗ (size A) → ⟦ A ⟧ᵗ
Vec→ {⊤} [] = tt
Vec→ {Bool} (b ∷ []) = b
Vec→ {A × B} bs = let u , v , _ = splitAt (size A) bs in Vec→ u , Vec→ v

→Vec∘Vec→ : ∀ (bs : Vec Boolᵗ (size A)) → →Vec (Vec→ {A} bs) ≡ bs
→Vec∘Vec→ {⊤} [] = refl
→Vec∘Vec→ {Bool} (b ∷ []) = refl
→Vec∘Vec→ {A × B} uv with splitAt (size A) uv
... | u , v , refl = cong₂ _++ⁿ_ (→Vec∘Vec→ {A} u) (→Vec∘Vec→ {B} v)

-- In progress
Vec→∘→Vec : ∀ (x : ⟦ A ⟧ᵗ) → Vec→ (→Vec x) ≡ x
Vec→∘→Vec {⊤} tt = refl
Vec→∘→Vec {Bool} b = refl
Vec→∘→Vec {A × B} (x , y) =
  let u , v , eq = splitAt (size A) (→Vec x ++ →Vec y)
      →Vec_x≡u , →Vec_y≡v = ++-injective (→Vec x) u eq in
    begin
      Vec→ (→Vec (x , y))
    ≡⟨⟩
      Vec→ (→Vec x ++ →Vec y)
    ≡⟨ cong₂ (λ u v → Vec→ (u ++ v)) →Vec_x≡u →Vec_y≡v ⟩
      Vec→ (u ++ v)
    ≡⟨ {!!} ⟩
      Vec→ (→Vec x) , Vec→ (→Vec y)
    ≡⟨ cong₂ _,_ (Vec→∘→Vec {A} x) (Vec→∘→Vec {B} y) ⟩
      x , y
    ∎

↔Vec : ⟦ A ⟧ᵗ ↔ Vec Boolᵗ (size A)
↔Vec {A} = mk↔′ →Vec Vec→ (→Vec∘Vec→ {A}) (Vec→∘→Vec {A})
-}

-- TODO: rework ↔Vec as a equational style proof.


-- TODO: Maybe phase out TyIx and ⟦_⟧ᵇ. More likely, drop its
-- generalization below.

-- Index of a subvalue in a type
infix 1 _∈ᵗ_
data _∈ᵗ_ : Ty → Ty → Set where
  here  : A ∈ᵗ A
  left  : A ∈ᵗ B → A ∈ᵗ B × C
  right : A ∈ᵗ C → A ∈ᵗ B × C

-- Extract a subvalue
⟦_∈ᵗ⟧ : ∀ {A} → B ∈ᵗ A → A →ᵗ B
⟦ here    ∈ᵗ⟧ = F.id
⟦ left  i ∈ᵗ⟧ = ⟦ i ∈ᵗ⟧ F.∘ F.exl
⟦ right i ∈ᵗ⟧ = ⟦ i ∈ᵗ⟧ F.∘ F.exr

-- ⟦ here    ∈ᵗ⟧ x = x
-- ⟦ left  i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ x
-- ⟦ right i ∈ᵗ⟧ (x , y) = ⟦ i ∈ᵗ⟧ y

infixr 9 _∘∈ᵗ_
_∘∈ᵗ_ : B ∈ᵗ C → A ∈ᵗ B → A ∈ᵗ C
here    ∘∈ᵗ f = f
left  i ∘∈ᵗ f = left  (i ∘∈ᵗ f)
right i ∘∈ᵗ f = right (i ∘∈ᵗ f)
-- Fully synthesized from {! -c !}

-- TODO: Prove that ⟦_∈ᵗ⟧  is a functor. Probably easy.
