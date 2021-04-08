-- Steps toward compiling-to-categories in Agda

module Tinkering.Reflection.CtoC where

open import Level using ()
open import Function
open import Data.Unit
open import Data.Product hiding (_<*>_)
open import Data.List
open import Data.Nat hiding (_⊔_)
import Data.Maybe as M
open M using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Reflection
open import Reflection.Name
open import Reflection.Term
open import Reflection.Argument
open import Reflection.DeBruijn
open import Reflection.TypeChecking.Monad.Syntax

open import Tinkering.Reflection.Quote  -- to experiment

pattern vlam x b = lam visible (abs x b)
pattern hlam x b = lam hidden  (abs x b)

pattern hcons¹ x = _ ⟅∷⟆ x
pattern hcons² x = hcons¹ (hcons¹ x)
pattern hcons³ x = hcons¹ (hcons² x)
pattern hcons⁴ x = hcons¹ (hcons³ x)
pattern hcons⁵ x = hcons¹ (hcons⁴ x)

apply : ∀ {a}{b}{A : Set a}{B : Set b} → (A → B) × A → B
apply = uncurry _$_
-- apply (f , x) = f x

infixl 4 _<*>ᴹ_
_<*>ᴹ_ = M.ap

open import Data.Bool
open import Relation.Nullary using (does)

primDefs primCons : List Name
primDefs = quote _∧_ ∷ quote _∨_ ∷ quote _xor_ ∷ quote not ∷ quote _+_ ∷ []
primCons = quote true ∷ quote false ∷ quote suc ∷  []

_∈ⁿ_ : Name → Names → Bool
nm ∈ⁿ names = any (does ∘ (_≈? nm)) names

transform : Term → Term
transform e₀@(vlam x body) with strengthen body
... | just body′ = def (quote const) (4 ⋯⟅∷⟆ body′ ⟨∷⟩ [])
... | nothing = case body of λ
      { (var zero []) → def (quote id) (2 ⋯⟅∷⟆ [])
      ; (con (quote _,_) (hcons⁴ (u ⟨∷⟩ v ⟨∷⟩ []))) →
          def (quote <_,_>) (6 ⋯⟅∷⟆ transform (vlam x u) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
      ; (con c args) → comp (con c) args
                       -- if c ∈ⁿ primCons then comp (con c) args else e₀
      ; (def f args) → comp (def f) args
                       -- if f ∈ⁿ primDefs then comp (def f) args else e₀
      -- ; (var zero args) → app args
      ; _ → e₀
      }
 where
   strengthenArg : Arg Term → Maybe (Arg Term)
   strengthenArg (arg info t) = M.map (arg info) (strengthen t)

   comp : (List (Arg Term) → Term) → List (Arg Term) → Term
   comp f (h ⟅∷⟆ args) with strengthen h
   ... | just h′ = comp (f ∘ (h′ ⟅∷⟆_)) args    -- accumulate invisible arguments
   ... | nothing = e₀                            -- invisible and uses x: fail
   -- For now, handle just one or two visible arguments. TODO: generalize.
   -- (λ x → f U) ↦ f ∘ (λ x → U)
   comp f (v ⟨∷⟩ []) = def (quote _∘′_) (6 ⋯⟅∷⟆ (f []) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
   -- (λ x → f U V) ↦ uncurry f ∘ (λ x → U , V)
   comp f (u ⟨∷⟩ v ⟨∷⟩ []) =
     def (quote _∘′_)
       (6 ⋯⟅∷⟆ def (quote uncurry′) (3 ⋯⟅∷⟆ f [] ⟨∷⟩ [])
        ⟨∷⟩ transform (vlam x (con (quote _,_) (4 ⋯⟅∷⟆ u ⟨∷⟩ v ⟨∷⟩ [])))
        ⟨∷⟩ [])
   comp f args = e₀

transform e₀ = e₀

-- I get the same results without "n ⋯⟅∷⟆". Is it really unnecessary?

-- Wrap in `A ∋`
asTy : ∀ {a} → Set a → Term → TC Term
asTy A t = (λ qA → def (quote _∋_) (vArg qA ∷ vArg t ∷ [])) <$> quoteTC A

-- asTy A t = do
--   qA ← quoteTC A
--   return (def (quote _∋_) (vArg qA ∷ vArg t ∷ []))

macro
  cat : ∀ {a}{A : Set a} {b}{B : Set b} → (A → B) → Term → TC ⊤
  cat {A = A}{B = B} f hole =
    transform <$> quoteTC f
    >>= asTy (A → B)
    >>= unify hole

_ : (λ (x : ℕ) → x) ≡ id
_ = {!!}

-- (λ x → x) ≡ id

_ : cat (λ (x : ℕ) → x) ≡ id
_ = {!!}

-- ((ℕ → ℕ) ∋ id) ≡ id

_ : cat (λ ((a , b) : ℕ × ℕ) → b , a) ≡ swap
_ = {!!}

-- ((ℕ × ℕ → Σ ℕ (λ v → ℕ)) ∋ < proj₂ , proj₁ >) ≡ swap

_ : cat (λ (x : ℕ) → 3) ≡ const 3
_ = {!!}

-- ((ℕ → ℕ) ∋ const 3) ≡ const 3

_ : ∀ {z : ℕ} → cat (λ (x : ℕ) → z + 1) ≡ const (z + 1)
_ = {!!}

-- ((ℕ → ℕ) ∋ const (z + 1)) ≡ const (z + 1)

_ : cat (λ n → suc n) ≡ suc
_ = {!!}

-- ((ℕ → ℕ) ∋ suc ∘′ id) ≡ suc

_ : cat (λ n → n + n) ≡ (λ n → n + n)
_ = {!!}

-- ((ℕ → ℕ) ∋ uncurry′ _+_ ∘′ < id , id >) ≡ (λ n → n + n)

_ : cat (λ n → n + 1) ≡ (λ n → n + 1)
_ = {!!}

-- ((ℕ → ℕ) ∋ uncurry′ _+_ ∘′ < id , const 1 >) ≡ (λ n → n + 1)
