{-# OPTIONS --safe --without-K #-}

module VecFun.Laws where

open import Level using (0ℓ)
open import Data.Vec
import Relation.Binary.PropositionalEquality as ≡

open import Miscellany using (Function)

open import Categorical.Raw
open import Categorical.Laws
open import Categorical.Instances.Function

open import VecFun.Raw

module VecFunLawfulInstances where
  instance

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = record
      { _≈_ = λ (mk f) (mk g) → ∀ {n} → f {n} ≈ g
                                -- ∀ {n} (as : Vec _ n) → f as ≡ g as
      ; equiv = record
        { refl  = refl -- = λ as → ≡.refl
        ; sym   = λ f∼g as → ≡.sym (f∼g as)
        ; trans = λ f∼g g∼h as → ≡.trans (f∼g as) (g∼h as)
        }
      }

    lawful-category : LawfulCategory _⇨_ 0ℓ
    lawful-category = record
      { identityˡ = refl
      ; identityʳ = refl
      ; assoc     = refl
      ; ∘≈ = λ {a b c}{(mk f) (mk g)}{(mk h) (mk k)} h≈k f≈g {n} →
         let open ≈-Reasoning {_⇨_ = Function} in
          begin
            ⟦ mk h ∘ mk f ⟧ₛ {n}
          ≡⟨⟩
            ⟦ mk (h ∘ f) ⟧ₛ {n}
          ≡⟨⟩
            h {n} ∘ f {n}
          ≈⟨ ∘≈ (h≈k {n}) (f≈g {n}) ⟩
            k {n} ∘ g {n}
          ≡⟨⟩
            ⟦ mk (k ∘ g) ⟧ₛ {n}
          ≡⟨⟩
            ⟦ mk k ∘ mk g ⟧ₛ {n}
          ∎
      }
