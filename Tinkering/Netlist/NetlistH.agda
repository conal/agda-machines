-- This variation is based on a vector-like type with sized elements.
-- Replace products with vectors.

module NetlistH where

open import Data.Product using (∃; _×_; _,_)
open import Data.Bool using (Bool)  -- TEMP
open import Data.Nat
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality -- using (_≡_; sym; subst)
import Data.Vec as V

import Misc as F
open import Symbolic.ExtrinsicVec

private variable a b c d j k : ℕ

-- Primitive instance: primitive and matching input routing
Inst : ℕ → ℕ → Set
Inst k b = ∃ λ a → (a p.⇨ b) × (k r.⇨ a)

⟦_⟧ⁱ : Inst k b → k b.⇨ b
⟦ _ , p , r ⟧ⁱ = p.⟦ p ⟧ F.∘ r.⟦ r ⟧

module _ (i : ℕ) where

  infixr 5 _∷_
  data Vec′ (F : ℕ → ℕ → Set) : ℕ → Set where
    [] : Vec′ F i
    _∷_ : F k j → Vec′ F k → Vec′ F (j + k)

  -- TODO: Define fold on Vec′

  Netlist : ℕ → Set
  Netlist = Vec′ Inst

  -- TODO: generalize ⟦_⟧ⁿ from Netlist to Vec′, probably as a fold

  -- A netlist with k outputs and result size a
  Src : ℕ → ℕ → Set
  Src k a = Netlist k × (k + i r.⇨ a)


Q : (a b.⇨ b) → (a b.⇨ b + a)
Q f = f b.△ b.id

⟦_⟧ⁿ : Netlist a k → a b.⇨ k + a
⟦ [] ⟧ⁿ = b.dup
⟦ inst ∷ nl ⟧ⁿ = b.first (Q ⟦ inst ⟧ⁱ) b.∘ ⟦ nl ⟧ⁿ

⟦_⟧ˢ : Src a k b → a b.⇨ b
⟦ nl , r ⟧ˢ = r.⟦ r ⟧ b.∘ ⟦ nl ⟧ⁿ

infix 0 _⇨_
_⇨_ : ℕ → ℕ → Set
i ⇨ o = ∃ λ k → Src i k o

-- Netlist semantics/interpreter
⟦_⟧ : a ⇨ b → a b.⇨ b
⟦ k , n , k⇨ᵣb ⟧ = r.⟦ k⇨ᵣb ⟧ b.∘ ⟦ n ⟧ⁿ

route : a r.⇨ b → a ⇨ b
route {a} a⇨ᵣb = {!!} , {!!} , {!!}

-- route {a} a⇨ᵣb = a , [] , a⇨ᵣb

-- infixr 9 _∘_
-- _∘_ : b ⇨ c → a ⇨ b → a ⇨ c

-- (kg , [] , kg⇨ᵣc) ∘ (kf , nf , kf⇨ᵣkg) = kf , nf , kg⇨ᵣc r.∘ kf⇨ᵣkg

-- (.(_ + _) , (d , d⇨ₚj , k⇨ᵣd) ∷ ng , kg⇨ᵣc) ∘ f =
--   let h@(e , nh , e⇨ᵣd) = (_ , ng , k⇨ᵣd) ∘ f in
--     {!!} , (_ , d⇨ₚj , e⇨ᵣd) ∷ nh , {!!}


-- Goal: j + e r.⇨ c

-- kg⇨ᵣc : j + k r.⇨ c
-- e⇨ᵣd  : e r.⇨ d
-- k⇨ᵣd  : k r.⇨ d

-- (.(_ + _) , inst ∷ ng , kg⇨ᵣc) ∘ f = {!!}

-- ∘_ {c = c} (jg , g) (jf , f) =
--   jg + jf , λ {k} sₐ → subst (λ n → Src n c) (sym (+-assoc jg jf k)) (g (f sₐ))


  -- valIn : Bits a → Src a a
  -- valIn x = subst Netlist (+-identityʳ _) ((zero , p.const x , r.!) ∷ []) , r.id

  -- input : Src a a
  -- input = subst Netlist (+-identityʳ _) ((zero , p.input , r.!) ∷ []) , r.id

  -- output : ℕ → Src k k
  -- output a = {!!} , r.id

{-

  -- The netlist category. The number of netlist outputs is static.
  infix 0 _⇨_
  _⇨_ : ℕ → ℕ → Set
  a ⇨ b = ∃ λ j → ∀ {k} → Src k a → Src (j + k) b

  route : a r.⇨ b → a ⇨ b
  route a⇨ᵣb = zero , λ (netsₖ , k⇨ᵣa) → netsₖ , a⇨ᵣb r.∘ k⇨ᵣa

  id  : a ⇨ a
  dup : a ⇨ a + a
  exl : a + b ⇨ a
  exr : a + b ⇨ b
  !   : a ⇨ 0

  id  = route r.id
  dup = route r.dup   -- or id △ id
  exl = route r.exl
  exr = route r.exr
  !   = route r.!

  -- assocʳ etc via route or their standard definitions via _△_ etc. TODO: prove
  -- route is a cartesian functor, so all such alternatives are equivalent.

  prim : a p.⇨ b → a ⇨ b
  prim {a}{b} a⇨ₚb = b , λ (netsₖ , k⇨ᵣa) → (a , a⇨ₚb , k⇨ᵣa) ∷ netsₖ , r.exl

  const : Bits b → 0 ⇨ b
  const x = prim (p.const x)

  -- The next two are for plugging the input and output before

  infixr 9 _∘_
  _∘_ : b ⇨ c → a ⇨ b → a ⇨ c
  _∘_ {c = c} (jg , g) (jf , f) =
    jg + jf , λ {k} sₐ → subst (λ n → Src n c) (sym (+-assoc jg jf k)) (g (f sₐ))

  first : a ⇨ c → a + b ⇨ c + b
  first (jf , f) = jf , λ {k} (netsₖ , k⇒ᵣa+b) →
   let nets_jf+k , jf+k⇨ᵣc = f {k} (netsₖ , r.exl r.∘ k⇒ᵣa+b) in
     nets_jf+k , jf+k⇨ᵣc r.△ r.exr r.∘ k⇒ᵣa+b r.∘ r.exr

  second : b ⇨ d → a + b ⇨ a + d
  second {b}{d}{a} g = route (r.swap {d}{a}) ∘ first g ∘ route (r.swap {a}{b})

  -- route r.swap : a + b ⇨ b + a
  -- first g      : b + a ⇨ d + a
  -- route r.swap : d + a ⇨ a + d

  infixr 7 _⊗_
  _⊗_ : a ⇨ c → b ⇨ d → a + b ⇨ c + d
  f ⊗ g = second g ∘ first f

  infixr 7 _△_
  _△_ : a ⇨ c → a ⇨ d → a ⇨ c + d
  f △ g = (f ⊗ g) ∘ dup

  -- Functorial compilation
  compile : a c.⇨ b → a ⇨ b
  compile (c.route r) = route r
  compile (c.prim p)  = prim p
  compile (g c.∘ f)   = compile g ∘ compile f
  compile (f c.⊗ g)   = compile f ⊗ compile g

  -- TODO: Prove that ⟦_⟧ is a functor and c.⟦_⟧ ≗ ⟦_⟧ F.∘ compile .



  -- TODO: Render a ⇨ b to dot format to make pictures. What about input? If I
  -- plug the input hole with const, it will render that way. I suppose I could
  -- add a special "input" primitive with a silly evaluator (e.g., zero).
  -- Alternatively, change Vec′ to denote a function, with [] denoting input. Then
  -- drop the Cayley trick, and define Src append instead. Might be a nicer
  -- design.

  -- seal : a ⇨ b → 0 ⇨ 0
  -- seal f = prim p.output ∘ f ∘ prim p.input

  -- nuthinˢ : Src 0 0
  -- nuthinˢ = [] , r.!  -- equivalently, r.id

  -- -- Seal and extract netlist
  -- sealⁿ : a ⇨ b → ∃ Netlist
  -- sealⁿ f = let k , h = seal f
  --               nl , r = h nuthinˢ
  --           in k , subst Netlist (+-identityʳ k) nl


  -- -- Experimental variations for stateful computation

  -- sealˢ : ∀ {s} → a + s ⇨ b + s → s ⇨ s
  -- sealˢ f = first (prim p.output) ∘ f ∘ first (prim p.input)


⟦_⟧ⁿ : Netlist a k → a b.⇨ k
⟦ [] ⟧ⁿ = b.id
⟦ inst ∷ nl ⟧ⁿ = (⟦ inst ⟧ⁱ b.△ b.id) b.∘ ⟦ nl ⟧ⁿ

⟦_⟧ˢ : Src a k b → a b.⇨ b
⟦ nl , r ⟧ˢ = r.⟦ r ⟧ b.∘ ⟦ nl ⟧ⁿ



-- -- Netlist semantics/interpreter
-- ⟦_⟧ : a ⇨ b → a b.⇨ b
-- ⟦ _ , f ⟧ x = ⟦ f (valIn x) ⟧ˢ

-}
