{-# OPTIONS --safe --without-K #-}

module Ty where

open import Data.Unit using (tt)
open import Data.Bool using (if_then_else_)
  renaming (false to false′; true to true′)
open import Data.Bool.Show as BS
open import Data.Product using (_,_; uncurry)
open import Data.Nat
open import Data.String hiding (toVec; toList; replicate)

import Category as C
open C

infixr 2 _`×_
data Ty : Set where
  `⊤    : Ty
  `Bool : Ty
  _`×_  : Ty → Ty → Ty

private variable A B C D : Ty

module tyv where
  instance

    meaningful : Meaningful Ty
    meaningful = record { ⟦_⟧ = ⟦_⟧′ }
     where
       ⟦_⟧′ : Ty → Set
       ⟦ `⊤ ⟧′     = ⊤
       ⟦ σ `× τ ⟧′ = ⟦ σ ⟧′ × ⟦ τ ⟧′
       ⟦ `Bool ⟧′  = Bool

    products : Products Ty
    products = record { ⊤ = `⊤ ; _×_ = _`×_ }

    boolean : Boolean Ty
    boolean = record { Bool = `Bool }

showTy : ⟦ A ⟧ → String
showTy = go true′
 where
   -- flag says we're in the left part of a pair
   go : Bool → ⟦ A ⟧ → String
   go {`⊤} _ tt = "tt"
   go {`Bool} _ b = BS.show b
   go {_ `× _} p (x , y) = (if p then parens else id)
                           (go true′ x ++ "," ++ go false′ y)

-- infix 0 _→ᵗ_
-- _→ᵗ_ : Ty → Ty → Set
-- A →ᵗ B = ⟦ A ⟧ → ⟦ B ⟧

-- Index of a bit in a type
data TyIx : Ty → Set where
  here : TyIx Bool
  left  : TyIx A → TyIx (A × B)
  right : TyIx B → TyIx (A × B)

-- Extract a bit
-- ⟦_⟧ᵇ : ∀ {A} → TyIx A → A →ᵗ Bool
⟦_⟧ᵇ : ∀ {A} → TyIx A → ⟦ A ⟧ → Bool
⟦ here    ⟧ᵇ x = x
⟦ left  i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ x
⟦ right i ⟧ᵇ (x , y) = ⟦ i ⟧ᵇ y

instance

  TyIx-Meaningful : ∀ {A} → Meaningful (TyIx A)
  TyIx-Meaningful = record { ⟦_⟧ = ⟦_⟧ᵇ }

tabulate : (TyIx A → Bool) → ⟦ A ⟧
tabulate {`⊤} f = tt
tabulate {`Bool} f = f here
tabulate {_ `× _} f = tabulate (f ∘ left) , tabulate (f ∘ right)

lookup : ⟦ A ⟧ → (TyIx A → Bool)
lookup a i = ⟦ i ⟧ᵇ a

swizzle : (TyIx B → TyIx A) → (⟦ A ⟧ → ⟦ B ⟧)
swizzle r a = tabulate (lookup a ∘ r)

private variable X Y Z : Set

infixr 4 _､_

-- Ty-indexed representable functor
data TyF (X : Set) : Ty → Set where
  •   : TyF X ⊤
  [_] : X → TyF X Bool
  _､_ : TyF X A → TyF X B → TyF X (A × B)

tabulate′ : (TyIx A → X) → TyF X A
tabulate′ {`⊤} f = •
tabulate′ {`Bool} f = [ f here ]
tabulate′ {_ `× _} f = tabulate′ (f ∘ left) ､ tabulate′ (f ∘ right)

lookup′ : TyF X A → (TyIx A → X)
lookup′ [ x ] here = x
lookup′ (l ､ r) (left  a) = lookup′ l a
lookup′ (l ､ r) (right b) = lookup′ r b

swizzle′ : (TyIx B → TyIx A) → ∀ {X} → TyF X A → TyF X B
swizzle′ r a = tabulate′ (lookup′ a ∘ r)

→TyF : ⟦ A ⟧ → TyF Bool A
→TyF {`⊤} tt = •
→TyF {`Bool} b = [ b ]
→TyF {_ `× _} (x , y) = →TyF x ､ →TyF y

TyF→ : TyF Bool A → ⟦ A ⟧
TyF→ • = tt
TyF→ [ b ] = b
TyF→ (x ､ y) = TyF→ x , TyF→ y

-- TODO: Finish ⟦ A ⟧ ↔ TyF Bool A . Proofs should be much easier than with vectors.

-- Agsy synthesized all of the TyF operations above. (Tidying needed for most,
-- -c for all but swizzle′, and tabulate′ and lookup′ hints for swizzle′.)

-- Relate Ty values to vectors

open import Data.Vec using (Vec; []; _∷_)
  renaming (_++_ to _++ⁿ_; toList to toListⁿ)

size : Ty → ℕ
size `⊤       = 0
size `Bool    = 1
size (A `× B) = size A + size B

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
toList = toListⁿ ∘ toVec

map : (X → Y) → TyF X A → TyF Y A
map f • = •
map f [ x ] = [ f x ]
map f (u ､ v) = map f u ､ map f v

allFin : TyF (Fin (size A)) A
allFin {`⊤} = •
allFin {`Bool} = [ zero ]
allFin {_ `× _} = map (inject+ _) allFin ､ map (raise _) allFin

allIx : TyF (TyIx A) A
allIx {`⊤} = •
allIx {`Bool} = [ here ]
allIx {_ `× _} = map left allIx ､ map right allIx

infixl 4 _⊛_
_⊛_ : TyF (X → Y) A → TyF X A → TyF Y A
• ⊛ • = •
[ f ] ⊛ [ x ] = [ f x ]
(fs ､ gs) ⊛ (xs ､ ys) = (fs ⊛ xs) ､ (gs ⊛ ys)

map₂ : (X → Y → Z) → TyF X A → TyF Y A → TyF Z A
map₂ f u v = map f u ⊛ v

module ty where

  infix 0 _⇨_
  record _⇨_ (A B : Ty) : Set where
    constructor mk
    field
      f : ⟦ A ⟧ → ⟦ B ⟧

  instance
    meaningful : Meaningful (A ⇨ B)
    meaningful = record { ⟦_⟧ = _⇨_.f }

    category : Category _⇨_
    category = record
      { id    = mk id
      ; _∘_   = λ { (mk g) (mk f) → mk (g ∘ f) }
      -- ; _≈_   = ?
      -- ; id-l  = refl
      -- ; id-r  = refl
      -- ; assoc = refl
      }

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_ = λ (mk f) (mk g) → mk λ (x , y) → f x , g y
      ; ! = mk λ _ → tt
      ; unitorᵉˡ = mk unitorᵉˡ
      ; unitorᵉʳ = mk unitorᵉʳ
      ; unitorⁱˡ = mk unitorⁱˡ
      ; unitorⁱʳ = mk unitorⁱʳ
      ; assocʳ = mk assocʳ
      ; assocˡ = mk assocˡ
      }

    braided : Braided _⇨_
    braided = record { swap = mk swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = mk exl ; exr = mk exr ; dup = mk dup }

open import Relation.Binary.PropositionalEquality

_⟦↑⟧_ : ∀ (A : Ty) n → ⟦ A ⟧ ↑ n ≡ ⟦ A ↑ n ⟧
A ⟦↑⟧ zero = refl
A ⟦↑⟧ suc n rewrite A ⟦↑⟧ n = refl

replicate : ∀ n → ⟦ A ⟧ → ⟦ A ⟧ ↑ n
replicate zero a = tt
replicate (suc n) a = a , replicate n a


-- Miscellaneous utilities, perhaps to move elsewhere
module TyUtils {ℓ} {_⇨_ : Ty → Ty → Set ℓ} (let infix 0 _⇨_; _⇨_ = _⇨_) where

  module _ ⦃ _ : Braided ⦃ tyv.products ⦄ _⇨_ ⦄ where

    -- Todo: rename
    replicate′ : ∀ n → (⊤ ⇨ A) → (⊤ ⇨ A ↑ n)
    replicate′ zero    a = !
    replicate′ (suc n) a = a ⦂ replicate′ n a

    shiftR : Bool × A ⇨ A × Bool
    shiftR {`⊤}     = swap
    shiftR {`Bool}  = id
    shiftR {_ `× _} = assocˡ ∘ second shiftR ∘ assocʳ ∘ first shiftR ∘ assocˡ

    -- i , (u , v)
    -- (i , u) , v
    -- (u′ , m) , v
    -- u′ , (m , v)
    -- u′ , (v′ , o)
    -- (u′ , v′) , o

    shiftL : A × Bool ⇨ Bool × A
    shiftL {`⊤}     = swap
    shiftL {`Bool}  = id
    shiftL {_ `× _} = assocʳ ∘ first shiftL ∘ assocˡ ∘ second shiftL ∘ assocʳ

    -- (u , v) , i
    -- u , (v , i)
    -- u , (m , v′)
    -- (u , m) , v′
    -- (o , u′) , v′
    -- o , (u′ , v′)

  module _ ⦃ _ : Cartesian ⦃ tyv.products ⦄ _⇨_ ⦄ where

    shiftR⇃ : Bool × A ⇨ A
    shiftR⇃ = exl ∘ shiftR

    shiftL⇃ : A × Bool ⇨ A
    shiftL⇃ = exr ∘ shiftL


module r where

  infix 1 _⇨_
  record _⇨_ (A B : Ty) : Set where
    constructor mk
    field
      f : TyIx B → TyIx A

  ⟦_⟧′ : A ⇨ B → ∀ {X} → TyF X A → TyF X B
  ⟦ mk f ⟧′ = swizzle′ f

  instance

    meaningful : ∀ {a b} → Meaningful {μ = a ty.⇨ b} (a ⇨ b)
    meaningful {a}{b} = record { ⟦_⟧ = λ (mk r) → ty.mk (swizzle r) }

    category : Category _⇨_
    category = record
      { id = mk id
      ; _∘_ = λ (mk f) (mk g) → mk (g ∘ f)
      }

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_ = λ (mk f) (mk g) → mk λ { (left x) → left (f x) ; (right x) → right (g x) }
      ; unitorᵉˡ = mk right
      ; unitorᵉʳ = mk left
      ; unitorⁱˡ = mk λ { (right x) → x }
      ; unitorⁱʳ = mk λ { (left  x) → x }
      ; assocʳ = mk λ { (left x) → left (left x)
                      ; (right (left x)) → left (right x)
                      ; (right (right x)) → right x
                      }
      ; assocˡ = mk λ { (left (left x)) → left x
                      ; (left (right x)) → right (left x)
                      ; (right x) → right (right x)
                      }
      ; ! = mk λ ()
      }

    braided : Braided _⇨_
    braided = record { swap = mk λ { (left x) → right x ; (right x) → left x } }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = mk left ; exr = mk right ; dup = mk λ { (left x) → x ; (right x) → x } }
