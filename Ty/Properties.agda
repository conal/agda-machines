module Ty.Properties where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat
open import Data.Nat.Properties

open import Ty

card≡2^size : ∀ a → card a ≡ 2 ^ size a
card≡2^size `⊤ = refl
card≡2^size `Bool = refl
card≡2^size (a `× b) = begin
                         card (a `× b)
                       ≡⟨⟩
                         card a * card b
                       ≡⟨ cong₂ _*_ (card≡2^size a) (card≡2^size b) ⟩
                         2 ^ size a * 2 ^ size b
                       ≡˘⟨ ^-distribˡ-+-* 2 (size a) (size b) ⟩
                         2 ^ (size a + size b)
                       ≡⟨⟩
                         2 ^ size (a `× b)
                       ∎
card≡2^size (a `⇛ b) = begin
                         card b ^ card a
                       ≡⟨ cong (_^ card a) (card≡2^size b) ⟩
                         (2 ^ size b) ^ card a
                       ≡⟨ ^-*-assoc 2 (size b) (card a) ⟩
                         2 ^ (size b * card a)
                       ∎
