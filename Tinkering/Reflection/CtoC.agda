-- Steps toward compiling-to-categories in Agda

module Tinkering.Reflection.CtoC where

open import Level using ()
open import Function
open import Data.Unit
open import Data.Product hiding (_<*>_)
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Maybe using (Maybe; nothing; just)
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

-- N-ary curried function types
infix 0 _⇉_
_⇉_ : ∀ {a} → List (Set a) → Set a → Set a
[]       ⇉ B = B
(A ∷ As) ⇉ B = A → As ⇉ B
-- To allow diverse levels, maybe define a special inductive type.

-- A view of the body of a lambda expression
data λCases : Set where
  Id : λCases
  Weaken : (body′ : Term) → λCases
  Pair : (u v : Term) → λCases
  Comp : (f : List (Arg Term) → Term) → (u : Term) → λCases
  Other : λCases

cases : Term → λCases
cases body with strengthen body
... | just body′ = Weaken body′
... | nothing = case body of λ
      { (var zero []) → Id
      ; (con (quote _,_) (cons⁴ (vArg u ∷ vArg v ∷ []))) → Pair u v
      ; (con c (u ⟨∷⟩ [])) → Comp (con c) u
      ; (def f (u ⟨∷⟩ [])) → Comp (def f) u
      ; _ → Other
      }

transform : Term → Term
transform e@(vlam x body) with cases body
... | Id = def (quote id) (2 ⋯⟅∷⟆ [])
... | Weaken body′ = def (quote const) (4 ⋯⟅∷⟆ body′ ⟨∷⟩ [])
... | Pair u v = def (quote <_,_>) (6 ⋯⟅∷⟆ vlam x u ⟨∷⟩ vlam x v ⟨∷⟩ [])
... | Comp f u = def (quote _∘′_) (6 ⋯⟅∷⟆ (f []) ⟨∷⟩ vlam x u ⟨∷⟩ [])
... | Other = e
transform f = f


-- Wrap in `A ∋_`
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
