{-# OPTIONS --safe --without-K #-}

open import Level
open import Categorical.Raw

module Primitive.Homomorphism
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Categorical.Homomorphism
open import Categorical.Laws

open import Typed _↠_ q renaming (_⇨_ to _⇨ₜ_)
open import Primitive.Raw _↠_

module primitive-homomomorphism-instances where

  instance

    open import Relation.Binary.PropositionalEquality

    open import Level using (0ℓ)

    productsH : ⦃ _ : Category _↠_ ⦄
                ⦃ lcat : LawfulCategory _↠_ q ⦄
              → ProductsH _⇨_ _⇨ₜ_ q
    productsH = id-productsH

    booleanH : ⦃ _ : Category _↠_ ⦄
             → BooleanH _⇨_ _⇨ₜ_
    booleanH = id-booleanH

    -- Help type inference along
    open Equiv {q = q}{_⇨_ = _↠_} using () renaming (sym to sym↠; trans to trans↠)

    logicH : ⦃ _ : Monoidal _↠_ ⦄ ⦃ lmon : LawfulMonoidal _↠_ q ⦄
           → LogicH _⇨_ _⇨ₜ_ q
    logicH ⦃ lmon = lmon ⦄ =
      let -- Help type inference along
          open LawfulCategory (LawfulMonoidal.lawful-cat lmon) using ()
                 renaming (identityˡ to identityˡ↠; identityʳ to identityʳ↠) in
        record
          { F-false = trans↠ identityʳ↠ (sym↠ identityˡ↠)
          ; F-true  = trans↠ identityʳ↠ (sym↠ identityˡ↠)
          ; F-not   = trans↠ identityʳ↠ (sym↠ identityˡ↠)
          ; F-∧     = trans↠ ∘id⊗       (sym↠ identityˡ↠)
          ; F-∨     = trans↠ ∘id⊗       (sym↠ identityˡ↠)
          ; F-xor   = trans↠ ∘id⊗       (sym↠ identityˡ↠)
          }

    -- TODO: Generalize to id-LogicH. See start in Categorical.Homomorphism
