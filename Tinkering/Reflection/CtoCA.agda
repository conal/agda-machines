-- Steps toward compiling-to-categories in Agda

module Tinkering.Reflection.CtoCA where

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

open import Data.Bool
open import Relation.Nullary using (does)

infixr 5 _⋯⟅∷⟆′_
_⋯⟅∷⟆′_ : ℕ → Args Term → Args Term
_⋯⟅∷⟆′_ n = id
-- _⋯⟅∷⟆′_ = _⋯⟅∷⟆_

transform : Term → Term
transform e₀@(vlam x body) with strengthen body
... | just body′ = def (quote const) (4 ⋯⟅∷⟆′ body′ ⟨∷⟩ [])
... | nothing = case body of λ
      { -- (λ x → x) ↦ id
        (var zero []) → def (quote id) (2 ⋯⟅∷⟆′ [])
      ; -- (λ x → U , V) → < λ x → U , λ x → V >
        (con (quote _,_) (hcons⁴ (u ⟨∷⟩ v ⟨∷⟩ []))) →
          def (quote <_,_>)
            (6 ⋯⟅∷⟆′ transform (vlam x u) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
      ; (con c args) → comp (con c) args
      ; (def f args) → comp (def f) args
      ; _ → e₀
      }
 where
   comp : (List (Arg Term) → Term) → List (Arg Term) → Term
   comp f (h ⟅∷⟆ args) with strengthen h
   ... | just h′ = comp (f ∘ (h′ ⟅∷⟆_)) args    -- accumulate invisible arguments
   ... | nothing = e₀                           -- invisible and uses x: fail
   -- For now, handle just one or two visible arguments. TODO: generalize.
   -- (λ x → f U) ↦ f ∘ (λ x → U)
   comp f (v ⟨∷⟩ []) = def (quote _∘′_) (6 ⋯⟅∷⟆′ (f []) ⟨∷⟩ transform (vlam x v) ⟨∷⟩ [])
   -- (λ x → f U V) ↦ uncurry f ∘ (λ x → U , V)
   comp f (u ⟨∷⟩ v ⟨∷⟩ []) =
     def (quote _∘′_)
       (6 ⋯⟅∷⟆′ def (quote uncurry′) (3 ⋯⟅∷⟆′ f [] ⟨∷⟩ [])
        ⟨∷⟩ transform (vlam x (con (quote _,_) (4 ⋯⟅∷⟆ u ⟨∷⟩ v ⟨∷⟩ [])))
        ⟨∷⟩ [])
   comp f args = e₀

transform e₀ = e₀

-- I get the same results without "n ⋯⟅∷⟆", except that removing the last one
-- seems to put the compiler into an ift loop.

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

-- To test, replace each refl with a hole, load, and read the hole types.

_ : id ≡ cat (λ (x : ℕ) → x)
_ = refl

-- id ≡ ((ℕ → ℕ) ∋ id)

_ : (λ ((a , b) : ℕ × ℕ) → b , a) ≡ cat (λ ((a , b) : ℕ × ℕ) → b , a)
_ = refl

-- (λ .patternInTele0 →
--        proj₂ .patternInTele0 , proj₁ .patternInTele0)
--     ≡ ((ℕ × ℕ → Σ ℕ (λ v → ℕ)) ∋ < proj₂ ∘′ id , proj₁ ∘′ id >)

_ : (λ (x : ℕ) → 3) ≡ cat (λ (x : ℕ) → 3)
_ = refl

-- (λ x → 3) ≡ ((ℕ → ℕ) ∋ const 3)

_ : ∀ {z : ℕ} → (λ (x : ℕ) → z + 1) ≡ cat (λ (x : ℕ) → z + 1)
_ = refl

-- (λ x → z + 1) ≡ ((ℕ → ℕ) ∋ const (z + 1))

_ : (λ n → suc n) ≡ cat (λ n → suc n)
_ = refl

-- (λ n → suc n) ≡ ((ℕ → ℕ) ∋ suc ∘′ id)

_ : (λ n → n + n) ≡ cat (λ n → n + n)
_ = refl

-- (λ n → n + n) ≡ ((ℕ → ℕ) ∋ uncurry′ _+_ ∘′ < id , id >)

_ : (λ n → n + 1) ≡ cat (λ n → n + 1)
_ = refl

-- (λ n → n + 1) ≡ ((ℕ → ℕ) ∋ uncurry′ _+_ ∘′ < id , const 1 >)
