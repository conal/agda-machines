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
open import Reflection.Term
open import Reflection.Argument
open import Reflection.DeBruijn
open import Reflection.TypeChecking.Monad.Syntax

open import Tinkering.Reflection.Quote  -- to experiment


pattern vlam x b = lam visible (abs x b)
pattern hlam x b = lam hidden  (abs x b)

pattern cons¹ x = _ ∷ x
pattern cons² x = cons¹ (cons¹ x)
pattern cons³ x = cons¹ (cons² x)
pattern cons⁴ x = cons¹ (cons³ x)
pattern cons⁵ x = cons¹ (cons⁴ x)


apply : ∀ {a}{b}{A : Set a}{B : Set b} → (A → B) × A → B
apply = uncurry _$_
-- apply (f , x) = f x

infixl 4 _<*>ᴹ_
_<*>ᴹ_ = M.ap

transform : Term → Term
transform e@(vlam x body) with strengthen body
... | just body′ = def (quote const) (4 ⋯⟅∷⟆ body′ ⟨∷⟩ [])
... | nothing = case body of λ
      { (var zero []) → def (quote id) (2 ⋯⟅∷⟆ [])
      ; (con (quote _,_) (cons⁴ (vArg u ∷ vArg v ∷ []))) →
          def (quote <_,_>) (6 ⋯⟅∷⟆ transform (vlam x u) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
      ; (con c args) → comp₀ (con c) args
      ; (def f args) → comp₀ (def f) args
      -- ; (var zero args) → app args
      ; _ → e
      }
 where
   strengthenArg : Arg Term → Maybe (Arg Term)
   strengthenArg (arg info t) = M.map (arg info) (strengthen t)

   -- strengthenArgs : List (Arg Term) → Maybe (List (Arg Term))
   -- strengthenArgs [] = just []
   -- strengthenArgs (a ∷ as) = just _∷_ <*>ᴹ strengthenArg a <*>ᴹ strengthenArgs as

   -- I have to strengthen each argument as it comes.
   -- If successful, fold into f; if not, recursively transform.
   -- How to combine?

   comp₁ : (List (Arg Term) → Term) → List (Arg Term) → Term
   -- comp₁ f (h ⟅∷⟆ args) with strengthen h
   -- ... | just h′ = comp₁ (f ∘ (h′ ⟅∷⟆_)) args
   -- ... | 
   comp₁ f (v ⟨∷⟩ []) = def (quote _∘′_) (6 ⋯⟅∷⟆ (f []) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
   -- TODO: handle more arguments
   comp₁ f args = e
   -- app : List (Arg Term) → Term
   -- app args = ?  -- use of apply

   -- comp₀ : (List (Arg Term) → Term) → List (Arg Term) → Term
   -- comp₀ f args with strengthenArgs args
   -- ... | nothing = e
   -- ... | just args′ = comp₁ f args′

transform e = e

-- I get the same results without "n ⋯⟅∷⟆".

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
