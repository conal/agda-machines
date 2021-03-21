module Netlist where

open import Data.Product using (_,_) renaming (_×_ to _×ᵗ_)
open import Data.Nat
open import Data.List

import Misc as F
open import Symbolic.ExtrinsicTy

private
  variable
    A B C D X : Ty

infixr 4 _∙_
data Source : Ty → Set₁ where
  tt : Source ⊤
  port : ℕ → Source Bool
  _∙_ : ∀ {σ τ} → Source σ → Source τ → Source (σ × τ)

-- Generate a source, and advance the port counter
mkSource : ℕ → Source A ×ᵗ ℕ
mkSource {⊤} n = tt , n
mkSource {Bool} n = port n , suc n
mkSource {A × B} n = let A′ , m = mkSource n
                         B′ , o = mkSource m in 
                     (A′ ∙ B′) , o
                        
record Instance : Set₁ where
  constructor inst
  field
    {σ τ} : Ty
    i : Source σ
    p : σ p.⇨ τ
    o : Source τ

Netlist : Set₁
Netlist = List Instance

-- State
St : Set₁
St = Netlist ×ᵗ ℕ

infixr 0 _→ᴹ_
_→ᴹ_ : Ty → Ty → Set₁
A →ᴹ B = Source A ×ᵗ St → Source B ×ᵗ St

route : (A r.⇨ B) → Source A → Source B
route r.id  x       = x
route r.dup x       = x ∙ x
route r.exl (x ∙ y) = x
route r.exr (x ∙ y) = y

flatten : (A c.⇨ B) → A →ᴹ B
flatten (c.route r) = F.first (route r)
flatten (c.prim p) (a , nets , m) =
  let b , n = mkSource m in b , inst a p b ∷ nets , n
flatten (g c.∘ f) = flatten g F.∘ flatten f
flatten (f c.⊗ g) ((a ∙ b) , nets , m) =
  let c , nets′ , n = flatten f (a , nets  , m)
      d , nets″ , o = flatten g (b , nets′ , n)
   in (c ∙ d) , nets″ , o

-- TODO: Use a standard state monad and "do" notation

-- TODO: Define an interpreter for _→ᴹ_, and prove that flatten preserves
-- meaning. I expect it to be difficult or impossible.

-- TODO: Redesign the representation and interpreter to simplify the interpreter
-- and its proof.

