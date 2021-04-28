{-# OPTIONS --safe --without-K #-}

module Categorical.Instances.Function.Raw where

open import Level using (Level)
open import Function using (_∘′_; const) renaming (id to id′)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)

open import Miscellany using (Function)
open import Categorical.Raw

private variable o : Level

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

    import Data.Bool as B

    boolean : Boolean Set
    boolean = record { Bool  = B.Bool }
    -- Can I make level-polymorphic? Probably with Lift.

    logic : Logic Function
    logic = record
              { ∧     = uncurry B._∧_
              ; ∨     = uncurry B._∨_
              ; xor   = uncurry B._xor_
              ; not   = B.not
              ; true  = const B.true
              ; false = const B.false
              ; cond  = λ (c , (a , b)) → B.if c then b else a
              }
