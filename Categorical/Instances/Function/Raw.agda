{-# OPTIONS --safe --without-K #-}

open import Level

module Categorical.Instances.Function.Raw (o : Level) where

open import Function using (_∘′_; const) renaming (id to id′)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

open import Miscellany using (Function)
open import Categorical.Raw

import Data.Bool as B

pattern 𝕗 = lift B.false
pattern 𝕥 = lift B.true

private

  lift→ : ∀ {a b} {A B : Set} → (A → B) → (Lift a A → Lift b B)
  lift→ f (lift x) = lift (f x)

  lift→₂ : ∀ {a b c} {A B C : Set} → (A → B → C) → (Lift a A → Lift b B → Lift c C)
  lift→₂ f (lift x) (lift y) = lift (f x y)

module →RawInstances where

  instance

    category : Category (Function {o})
    category = record { id = id′ ; _∘_ = _∘′_ }

    products : Products (Set o)
    products = record { ⊤ = ⊤′ ; _×_ = _×′_ }

    monoidal : Monoidal (Function {o})
    monoidal = record
                  { _⊗_ = λ f g (x , y) → (f x , g y)
                  ; unitorᵉˡ = λ (tt , y) → y
                  ; unitorᵉʳ = λ (x , tt) → x
                  ; unitorⁱˡ = tt ,_
                  ; unitorⁱʳ = _, tt
                  ; assocʳ   = λ ((x , y) , z) → x , (y , z)
                  ; assocˡ   = λ (x , (y , z)) → (x , y) , z
                  }

    braided : Braided (Function {o})
    braided = record { swap = λ (a , b) → b , a }

    cartesian : Cartesian (Function {o})
    cartesian = record { exl = proj₁ ; exr = proj₂ ; dup = λ z → z , z }

    exponentials : Exponentials (Set o)
    exponentials = record { _⇛_ = Function }

    closed : Closed (Function {o})
    closed = record { _⟴_ = λ f h g → h ∘ g ∘ f }

    boolean : Boolean (Set o)
    boolean = record { Bool = Lift o B.Bool }

    logic : Logic (Function {o})
    logic = record
              { ∧     = uncurry (lift→₂ B._∧_)
              ; ∨     = uncurry (lift→₂ B._∨_)
              ; xor   = uncurry (lift→₂ B._xor_)
              ; not   = lift→ B.not
              ; true  = const 𝕥
              ; false = const 𝕗
              ; cond  = λ (lift c , (a , b)) → B.if c then b else a
              }

