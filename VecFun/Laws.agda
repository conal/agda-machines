{-# OPTIONS --safe --without-K #-}

module VecFun.Laws where

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as ≡

open import Miscellany using (Function)

open import Categorical.Raw
open import Categorical.Laws
open import Categorical.Instances.Function

open import VecFun.Raw

module VecFunLawfulInstances where
  instance

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = record
      { identityˡ = λ {a b}{f}{n} as → ≡.refl
      ; identityʳ = λ {a b}{f}{n} as → ≡.refl
      ; assoc     = λ {c d b a}{f g h}{n} as → ≡.refl
      ; ∘-resp-≈  = λ {a b c}{(mk f) (mk g)}{(mk h) (mk k)} h≈k f≈g {n} →
         let open ≈-Reasoning {_⇨_ = Function} in
          begin
            ⟦ mk h ∘ mk f ⟧ₛ {n}
          ≡⟨⟩
            ⟦ mk (h ∘ f) ⟧ₛ {n}
          ≡⟨⟩
            h {n} ∘ f {n}
          ≈⟨ ∘-resp-≈ (h≈k {n}) (f≈g {n}) ⟩
            k {n} ∘ g {n}
          ≡⟨⟩
            ⟦ mk (k ∘ g) ⟧ₛ {n}
          ≡⟨⟩
            ⟦ mk k ∘ mk g ⟧ₛ {n}
          ∎
      }
