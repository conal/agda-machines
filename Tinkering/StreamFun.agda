-- Synchronous stream functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K --copatterns --guardedness #-}

module Tinkering.StreamFun where

open import Function using (_∘′_; case_of_) renaming (id to id→)
open import Data.Product hiding (zip) renaming (map to map×; map₁ to map×₁; swap to swap×)
open import Data.Unit
open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

private
  variable
    A B C D : Set

record Stream (A : Set) : Set where
  coinductive
  constructor delay
  field
    hd : A
    tl : Stream A
-- {-# ETA Stream #-}

open Stream public

infix 4 _≈_
record _≈_ (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  -- constructor ∷≈
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_ public

infix 8 _!_
_!_ : Stream A → ℕ → A
as ! zero  = hd as
as ! suc i = tl as ! i

-- Mapping a function (combinational logic)
map : (A → B) → Stream A → Stream B
hd (map f as) = f (hd as)
tl (map f as) = map f (tl as)

zip : Stream A × Stream B → Stream (A × B)
hd (zip uv) = map× hd hd uv
tl (zip uv) = zip (map× tl tl uv)

-- hd (zip (as , bs)) = hd as , hd bs
-- tl (zip (as , bs)) = zip (tl as , tl bs)

-- Seems a shame to make two passes, but I couldn't figure out how to satisfy
-- the termination checker in a single-pass definition.
unzip : Stream (A × B) → Stream A × Stream B
unzip = < map proj₁ , map proj₂ >
-- unzip zs = map proj₁ zs , map proj₂ zs

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

-- Truncate to a vector
take : ∀ n → Stream A → Vec A n
take zero    as = []
take (suc n) as = hd as ∷ take n (tl as)

infix 4 _≈_upto_
_≈_upto_ : Stream A → Stream A → ℕ → Set
u ≈ v upto n = take n u ≡ take n v

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = Stream A → Stream B

infix 4 _≗_
_≗_ : Rel (A ↠ B) _
f ≗ g = ∀ as → f as ≈ g as

causal : ℕ → (A ↠ B) → Set
causal d f = ∀ n u v → u ≈ v upto n → f u ≈ f v upto (d + n)

-- TODO: Define a category of causal stream functions. Then map Mealy to them.

-- Mapping a function (combinational logic)
arr : (A → B) → (A ↠ B)
arr = map

const : A → Stream A
hd (const a) = a
tl (const a) = const a

id : A ↠ A
id = id→

infixr 9 _∘_
_∘_ : (B ↠ C) → (A ↠ B) → (A ↠ C)
_∘_ = _∘′_

-- Parallel composition
infixr 10 _⊗_
_⊗_ : (A ↠ C) → (B ↠ D) → (A × B ↠ C × D)
f ⊗ g = zip ∘′ map× f g ∘′ unzip
-- (f ⊗ g) ps = let as , bs = unzip ps in zip (f as) (g bs)

-- -- -- Conditional/choice composition
-- -- infixr 6 _⊕_
-- -- _⊕_ : (A ↠ C) → (B ↠ D) → ((A ⊎ B) ↠ (C ⊎ D))

-- -- Cons (memory/register)
-- delay : A → (A ↠ A)
-- hd (delay a as) = a
-- tl (delay a as) = as

scanl : (B → A → B) → B → A ↠ B
hd (scanl f e as) = e
tl (scanl f e as) = scanl f (f e (hd as)) (tl as)

mealy : ∀ {σ : Set} → σ → (A × σ → B × σ) → A ↠ B
hd (mealy s f as) = let b , _  = f (hd as , s) in b
tl (mealy s f as) = let _ , s′ = f (hd as , s) in mealy s′ f (tl as)

-- -- Can mealy be defined without redundant computation?
-- -- The following alternative doesn't pass termination checking:
-- mealy s f as = let b , s′ = f (hd as , s) in delay b (mealy s′ f (tl as))

-- TODO: relate scanl and mealy. Are they inter-definable?

-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality.Properties

-- open import Relation.Binary.Structures ()

-- open IsEquivalence isEquivalence renaming (refl to refl≡; sym to sym≡; trans to trans≡)

-- open ≡-Reasoning

≈-refl : ∀ {as : Stream A} → as ≈ as
hd-≈ ≈-refl = refl     -- hd as ≡ hd as
tl-≈ ≈-refl = ≈-refl   -- tl as ≈ tl as

≈-sym : ∀ {u v : Stream A} → u ≈ v → v ≈ u
hd-≈ (≈-sym u≈v) =   sym (hd-≈ u≈v)
tl-≈ (≈-sym u≈v) = ≈-sym (tl-≈ u≈v)

≈-trans : ∀ {u v w : Stream A} → u ≈ v → v ≈ w → u ≈ w
hd-≈ (≈-trans u≈v v≈w) =   trans (hd-≈ u≈v) (hd-≈ v≈w)
tl-≈ (≈-trans u≈v v≈w) = ≈-trans (tl-≈ u≈v) (tl-≈ v≈w)

open import Relation.Binary

isEq : IsEquivalence {A = Stream A} _≈_
isEq = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

≈-setoid : Set → Setoid _ _
≈-setoid A = record { isEquivalence = isEq {A} }
-- ≈-setoid A = record { Carrier = Stream A ; _≈_ = _≈_ ; isEquivalence = isEq }

module R {A : Set} where
  open import Relation.Binary.Reasoning.Setoid (≈-setoid A) public

delay-hd-tl : ∀ {as : Stream A} → delay (hd as) (tl as) ≈ as
hd-≈ (delay-hd-tl {as = as}) = refl   -- : hd as ≡ hd as
tl-≈ (delay-hd-tl {as = as}) = ≈-refl -- : tl as ≈ tl as

-- open R

zip∘unzip : ∀ {ps : Stream (A × B)} → zip (unzip ps) ≈ ps
hd-≈ zip∘unzip = refl
tl-≈ zip∘unzip = zip∘unzip  -- on tl ps

zip∘unzip′ : zip ∘′ unzip ≗ id {A × B}
hd-≈ (zip∘unzip′ _) = refl
tl-≈ (zip∘unzip′ ps) = zip∘unzip′ (tl ps)  -- on tl ps

-- delay⊗ : ∀ {a₀ : A} {b₀ : B} ps → (delay a₀ ⊗ delay b₀) ps ≈ delay (a₀ , b₀) ps
delay⊗ : ∀ {a₀ : A} {b₀ : B} → delay a₀ ⊗ delay b₀ ≗ delay (a₀ , b₀)
hd-≈ (delay⊗ ps) = refl
tl-≈ (delay⊗ ps) = zip∘unzip

-- tl-≈ (delay⊗ {a₀ = a₀}{b₀} ps) =
--   begin
--     tl ((delay a₀ ⊗ delay b₀) ps)
--   ≡⟨⟩
--     tl (zip (map× (delay a₀) (delay b₀) (unzip ps)))
--   ≡⟨⟩
--     tl (zip (map× (delay a₀) (delay b₀) (map proj₁ ps , map proj₂ ps)))
--   ≡⟨⟩
--     tl (zip (delay a₀ (map proj₁ ps) , delay b₀ (map proj₂ ps)))
--   ≡⟨⟩
--     zip (tl (delay a₀ (map proj₁ ps)) , tl (delay b₀ (map proj₂ ps)))
--   ≡⟨⟩
--     zip (map proj₁ ps , map proj₂ ps)
--   ≡⟨⟩
--     zip (unzip ps)
--   ≈⟨ zip∘unzip ⟩
--     ps
--   ≡⟨⟩
--     tl (delay (a₀ , b₀) ps)
--   ∎
--  where open R

module AsMealy where
  open R

  arrᴹ : ∀ (f : A → B) → arr f ≗ mealy tt (map×₁ f)
  hd-≈ (arrᴹ f as) = refl
  tl-≈ (arrᴹ f as) = arrᴹ f (tl as)              -- passes termination check
  -- tl-≈ (arrᴹ f as) = ≈-trans ≈-refl (arrᴹ f (tl as))  -- fails termination check

  -- delayᴹ : (a₀ : A) → mealy a₀ swap× ≗ delay a₀
  -- hd-≈ (delayᴹ a₀ as) = refl
  -- -- tl-≈ (delayᴹ a₀ as) = ≈-trans (delayᴹ (hd as) (tl as)) delay-hd-tl
  -- tl-≈ (delayᴹ a₀ as) = delayᴹ (hd as) (tl as)

  -- delayᴹ : (a₀ : A) → mealy a₀ swap× ≗ delay a₀
  -- hd-≈ (delayᴹ a₀ as) = refl
  -- tl-≈ (delayᴹ a₀ as) = ≈-trans (delayᴹ (hd as) (tl as)) delay-hd-tl

  -- ⟦delay⟧ : (a₀ : A) → ⟦ delay a₀ ⟧ ≗ ◇.delay a₀
  -- hd-≈ (⟦delay⟧ a₀ as) = refl
  -- tl-≈ (⟦delay⟧ a₀ as) = ◇.≈-trans (⟦delay⟧ (hd as) (tl as)) ◇.delay-hd-tl


  -- infixr 9 _∘ᴹ_
  -- _∘ᴹ_ : ∀ (g : B ⇨ C) (f : A ⇨ B) → mealy t g ∘ mealy s f ≗ ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
  -- (_ ∘ᴹ _) [] = refl
  -- (mealy t g ∘ᴹ mealy s f) (a ∷ as)
  --   rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
  --             (mealy t′ g ∘ᴹ mealy s′ f) as) = refl
  


  -- infixr 9 _⟦∘⟧_
  -- _⟦∘⟧_ : ∀ (g : B ⇨ C) (f : A ⇨ B) → ⟦ g ∘ f ⟧ ≗ ⟦ g ⟧ ◇.∘ ⟦ f ⟧
  -- (_ ⟦∘⟧ _) [] = refl
  -- (mealy t g ⟦∘⟧ mealy s f) (a ∷ as)
  --   rewrite (let b , s′ = f (a , s) ; c , t′ = g (b , t) in 
  --             (mealy t′ g ⟦∘⟧ mealy s′ f) as) = refl
