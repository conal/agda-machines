-- Symbolic representation or Mealy machines, suitable for analysis and code
-- generation (e.g., Verilog).

module Symbolic.ExtrinsicVec where

open import Data.Nat
open import Data.Fin using (Fin; raise; inject+) renaming (splitAt to splitAtᶠ)
open import Data.Vec hiding (transpose)
import Data.Bool as Bool
open Bool using (Bool; if_then_else_)
open import Data.Product using (_×_ ; _,_; uncurry) renaming (map to map×)
import Data.Sum as ⊎
open ⊎ using (_⊎_; inj₁; inj₂)
open import Data.String using (String) renaming (concat to concatˢ)
import Data.List as L

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

import Misc as F

private variable a b c d s t : ℕ

Bits : ℕ → Set
Bits = Vec Bool

showBit : Bool → String
showBit Bool.false = "0"
showBit Bool.true  = "1"

showBits : Bits a → String
showBits bs = concatˢ (L.map showBit (toList bs))

-- Is this function defined somewhere?
mergeᶠ : Fin a ⊎ Fin b → Fin (a + b)
mergeᶠ {a}{b} = ⊎.[ inject+ b , raise a ]

split′ : ∀ {ℓ}{X : Set ℓ} → Vec X (a + b) → Vec X a × Vec X b
split′ {a = a} xs = let (u , v , _) = splitAt a xs in u , v

module b′ {A : Set} where

  infix 0 _⇨_
  _⇨_ : ℕ → ℕ → Set
  m ⇨ n = Vec A m → Vec A n

  id : a ⇨ a
  id = F.id

  infixr 9 _∘_
  _∘_ : b ⇨ c → a ⇨ b → a ⇨ c
  _∘_ = F._∘_

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
  f ⊗ g = uncurry _++_ F.∘ map× f g F.∘ split′

  first : a ⇨ c → a + b ⇨ c + b
  first f = f ⊗ id

  second : b ⇨ d → a + b ⇨ a + d
  second g = id ⊗ g

  exl : a + b ⇨ a
  exl = F.exl F.∘ split′

  exr : a + b ⇨ b
  exr = F.exr F.∘ split′

  dup : a ⇨ a + a
  dup = uncurry _++_ F.∘ F.dup

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ dup

  swap : a + b ⇨ b + a
  swap {a} = exr △ exl {a}

  ! : a ⇨ 0
  ! = F.const []

  assocˡ : a + (b + c) ⇨ (a + b) + c
  assocʳ : (a + b) + c ⇨ a + (b + c)

  assocˡ {a}{b}{c} = subst (_⇨ (a + b) + c) (+-assoc a b c) id
  assocʳ {a}{b}{c} = subst ((a + b) + c ⇨_) (+-assoc a b c) id

  -- -- Or standard definitions:
  -- assocˡ {a}{b}{c} = second (exl {b}) △ exr {b}{c} ∘ exr {a}
  -- assocʳ {a}{b}{c} = exl {a} ∘ exl △ first (exr {a})

  -- Elimination half of unitor isomorphisms
  unitorᵉˡ : 0 + a ⇨ a
  unitorᵉˡ = id
  -- unitorᵉˡ {a} = subst (0 + a ⇨_) (+-identityˡ a) id

  unitorᵉʳ : a + 0 ⇨ a
  unitorᵉʳ {a} = subst (a + 0 ⇨_) (+-identityʳ a) id

  -- Introduction half of unitor isomorphisms
  unitorⁱˡ : a ⇨ 0 + a
  unitorⁱˡ = id
  -- unitorⁱˡ {a} = subst (_⇨ 0 + a) (+-identityˡ a) id

  unitorⁱʳ : a ⇨ a + 0
  unitorⁱʳ {a} = subst (_⇨ a + 0) (+-identityʳ a) id

module b where
  open b′ {Bool} public
  

-- Routing.  TODO: consider generalizing from Bool.
module r′ {A : Set} where

  infix 1 _⇨_
  _⇨_ : ℕ → ℕ → Set
  a ⇨ b = Fin b → Fin a

  ⟦_⟧ : (a ⇨ b) → b′._⇨_ {A} a b
  ⟦ f ⟧ a = tabulate (lookup a F.∘ f)

  -- TODO: consider removing the A module parameter and universally quantifying
  -- over A in the ⟦_⟧ signature.

  id : a ⇨ a
  id = F.id

  infixr 9 _∘_
  _∘_ : b ⇨ c → a ⇨ b → a ⇨ c
  g ∘ f = f F.∘ g

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
  _⊗_ {c = c} f g = mergeᶠ F.∘ ⊎.map f g F.∘ splitAtᶠ c

  first : a ⇨ c → a + b ⇨ c + b
  first f = f ⊗ id

  second : b ⇨ d → a + b ⇨ a + d
  second g = id ⊗ g

  exl : a + b ⇨ a
  exl {a}{b} = inject+ b

  exr : a + b ⇨ b
  exr {a}{b} = raise a

  dup : a ⇨ a + a
  dup {a} = F.jam F.∘ splitAtᶠ a

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ dup

  swap : a + b ⇨ b + a
  swap {a} = exr △ exl {a}
  -- We must not use the subst/id trick for swap!

  assocˡ : a + (b + c) ⇨ (a + b) + c
  assocʳ : (a + b) + c ⇨ a + (b + c)

  assocˡ {a}{b}{c} = subst (_⇨ (a + b) + c) (+-assoc a b c) id
  assocʳ {a}{b}{c} = subst ((a + b) + c ⇨_) (+-assoc a b c) id

  -- Elimination half of unitor isomorphisms
  unitorᵉˡ : 0 + a ⇨ a
  unitorᵉˡ = id
  -- unitorᵉˡ {a} = subst (0 + a ⇨_) (+-identityˡ a) id

  unitorᵉʳ : a + 0 ⇨ a
  unitorᵉʳ {a} = subst (a + 0 ⇨_) (+-identityʳ a) id

  -- Introduction half of unitor isomorphisms
  unitorⁱˡ : a ⇨ 0 + a
  unitorⁱˡ = id
  -- unitorⁱˡ {a} = subst (_⇨ 0 + a) (+-identityˡ a) id

  unitorⁱʳ : a ⇨ a + 0
  unitorⁱʳ {a} = subst (_⇨ a + 0) (+-identityʳ a) id

  ! : a ⇨ 0
  ! ()

module r where
  open r′ {Bool} public

-- Combinational primitives
module p where

  1→1 : (Bool → Bool) → 1 b.⇨ 1
  1→1 f (x ∷ []) = f x ∷ []

  2→1 : (Bool → Bool → Bool) → 2 b.⇨ 1
  2→1 _∙_ (x ∷ y ∷ []) = x ∙ y ∷ []

  infix 1 _⇨_
  data _⇨_ : ℕ → ℕ → Set where
    ∧ ∨ xor : 2 ⇨ 1
    not : 1 ⇨ 1
    const : Bits a → 0 ⇨ a
    -- The next two are introduced by graph generation
    input  : 0 ⇨ a
    output : b ⇨ 0

  ⟦_⟧ : a ⇨ b → a b.⇨ b
  ⟦ ∧ ⟧       = 2→1 Bool._∧_
  ⟦ ∨ ⟧       = 2→1 Bool._∨_
  ⟦ xor ⟧     = 2→1 Bool._xor_
  ⟦ not ⟧     = 1→1 Bool.not
  ⟦ const a ⟧ = F.const a
  ⟦ input ⟧   = F.const (replicate Bool.false)
  ⟦ output ⟧  = F.const []

  show : a ⇨ b → String
  show ∧         = "∧"
  show ∨         = "∨"
  show xor       = "xor"
  show not       = "not"
  show (const x) = showBits x
  show input     = "input"
  show output    = "output"

  #outs : (a ⇨ b) → ℕ
  #outs {b = b} _ = b

-- Combinational circuits
module c where

  infix  0 _⇨_
  infixr 7 _⊗_
  infixr 9 _∘_

  data _⇨_ : ℕ → ℕ → Set where
    route : a r.⇨ b → a ⇨ b
    prim : a p.⇨ b → a ⇨ b
    _∘_ : b ⇨ c → a ⇨ b → a ⇨ c
    _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d

  ⟦_⟧ : a ⇨ b → a b.⇨ b
  ⟦ route r ⟧ xs = tabulate (lookup xs F.∘ r)
  ⟦ prim  p ⟧ = p.⟦ p ⟧
  ⟦ g ∘ f ⟧ = ⟦ g ⟧ b.∘ ⟦ f ⟧
  ⟦ f ⊗ g ⟧ = ⟦ f ⟧ b.⊗ ⟦ g ⟧

  -- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
  -- parametrized by denotation.

  id  : a ⇨ a
  dup : a ⇨ a + a
  exl : a + b ⇨ a
  exr : a + b ⇨ b
  !   : a ⇨ 0

  id         = route r.id
  dup {a}    = route (r.dup {a})
  exl {a}{b} = route (r.exl {a}{b})
  exr {a}{b} = route (r.exr {a}{b})
  !          = route λ ()

  -- ∧ ∨ xor : 2 ⇨ 1
  -- not : 1 ⇨ 1
  -- ∧   = prim p.∧
  -- ∨   = prim p.∨
  -- xor = prim p.xor
  -- not = prim p.not

  -- Cartesian-categorical operations with standard definitions:

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ dup

  first : a ⇨ c → a + b ⇨ c + b
  first f = f ⊗ id

  second : b ⇨ d → a + b ⇨ a + d
  second f = id ⊗ f

  -- Some useful composite combinational circuits

  assocˡ : a + (b + c) ⇨ (a + b) + c
  assocʳ : (a + b) + c ⇨ a + (b + c)

  assocˡ {a}{b}{c} = subst (_⇨ (a + b) + c) (+-assoc a b c) id
  assocʳ {a}{b}{c} = subst ((a + b) + c ⇨_) (+-assoc a b c) id

  -- assocˡ {a}{b}{c} = second (exl {b}) △ exr {b} ∘ exr {a}
  -- assocʳ {a}{b}{c} = exl {a} ∘ exl △ first (exr {a})

  -- assocˡ = second exl △ exr ∘ exr
  -- assocʳ = exl ∘ exl △ first exr

  swap : a + b ⇨ b + a
  swap {a}{b} = exr △ exl {a}

  transpose : (a + b) + (c + d) ⇨ (a + c) + (b + d)
  transpose {a}{b}{c}{d} = (exl {a} ⊗ exl {c}) △ (exr {a} ⊗ exr {c})

  -- TODO: redo transpose via subst and Data.Nat.Properties

  -- If I parametrize by Ty instead of ℕ, I expect all of the implicit arguments
  -- to be inferred, since Ty _×_ is injective, unlike ℕ _+_.

-- Synchronous state machine.
module s where

  -- For composability, the state type is not visible in the type.
  infix  0 _⇨_
  record _⇨_ (a b : ℕ) : Set where
    constructor mealy
    field
      { σ } : ℕ
      start : Bits σ
      transition : a + σ c.⇨ b + σ

--   import Mealy as m

--   ⟦_⟧ : a ⇨ b → ⟦ a ⟧ᵗ m.⇨ ⟦ b ⟧ᵗ
--   ⟦ mealy s₀ f ⟧ = m.mealy s₀ c.⟦ f ⟧

  comb : a c.⇨ b → a ⇨ b
  comb f = mealy [] (c.first f)

  id  : a ⇨ a
  dup : a ⇨ a + a
  exl : a + b ⇨ a
  exr : a + b ⇨ b
  !   : a ⇨ 0

  id  = comb c.id
  dup = comb c.dup
  exl = comb c.exl
  exr = comb c.exr
  !   = comb c.!

  prim : a p.⇨ b → a ⇨ b
  prim p = comb (c.prim p)

  ∧ ∨ xor : 2 ⇨ 1
  not : 1 ⇨ 1
  ∧   = prim p.∧
  ∨   = prim p.∨
  xor = prim p.xor
  not = prim p.not

  delay : Bits a → a ⇨ a
  delay {a} a₀ = mealy a₀ (c.swap {a})

  infixr 9 _∘_
  _∘_ : b ⇨ c → a ⇨ b → a ⇨ c
  _∘_ {b}{c}{a} (mealy {t} t₀ g) (mealy {s} s₀ f) = mealy (s₀ ++ t₀)
    (swiz₂ c.∘ c.second {b = b + t}{a = s} g c.∘ swiz₁
     c.∘ c.first f c.∘ c.assocˡ {a}{s}{t})
   where
     swiz₁ : (b + s) + t c.⇨ s + (b + t)
     swiz₁ = c.exr {b} c.∘ c.exl {b + s} c.△ c.first (c.exl {b})
     swiz₂ : s + (c + t) c.⇨ c + (s + t)
     swiz₂ = c.exl {c} c.∘ c.exr {s} c.△ c.second (c.exr {c}{t})

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
  _⊗_ {a}{c}{b}{d} (mealy {s} s₀ f) (mealy {t} t₀ g) =
    mealy (s₀ ++ t₀)
     (c.transpose {c}{s}{d}{t} c.∘ (f c.⊗ g) c.∘ c.transpose {a}{b}{s}{t})

  -- Cartesian-categorical operations with standard definitions:

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ comb c.dup

  first : a ⇨ c → a + b ⇨ c + b
  first f = f ⊗ id

  second : b ⇨ d → a + b ⇨ a + d
  second f = id ⊗ f

  assocˡ : a + (b + c) ⇨ (a + b) + c
  assocʳ : (a + b) + c ⇨ a + (b + c)

  assocˡ {a}{b}{c} = subst (_⇨ (a + b) + c) (+-assoc a b c) id
  assocʳ {a}{b}{c} = subst ((a + b) + c ⇨_) (+-assoc a b c) id

  -- assocˡ {a}{b}{c} = second (exl {b}) △ exr {b} ∘ exr {a}
  -- assocʳ {a}{b}{c} = exl {a} ∘ exl △ first (exr {a})

  -- assocˡ = second exl △ exr ∘ exr
  -- assocʳ = exl ∘ exl △ first exr

  swap : a + b ⇨ b + a
  swap {a}{b} = exr △ exl {a}

  transpose : (a + b) + (c + d) ⇨ (a + c) + (b + d)
  transpose {a}{b}{c}{d} = (exl {a} ⊗ exl {c}) △ (exr {a} ⊗ exr {c})

  -- TODO: redo transpose via subst and Data.Nat.Properties



-- TODO: consider making categorical operations (most of the functionality in
-- this module) be methods of a common typeclass, so that (a) we can state and
-- prove laws conveniently, and (b) we needn't use clumsy names.

-- TODO: Rebuild this module in terms of semantic Mealy machines.

-- TODO: Prove the cartesian category laws for _⇨_. Probably easier if
-- parametrized by denotation.

-- TODO: Cocartesian.

-- TODO: replicate compiling-to-categories using Agda reflection, and use to
-- make definitions like `_∘_` and `_⊗_` above read like their counterparts in
-- the Mealy module.
