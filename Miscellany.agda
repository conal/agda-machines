{-# OPTIONS --safe --without-K #-}

module Miscellany where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality

private
  variable
    o : Level
    A B : Set o

_≡,≡_ : {a a′ : A}{b b′ : B} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
refl ≡,≡ refl = refl

-- TODO: Consider using setoid functions instead
Function : Set o → Set o → Set o
Function a b = a → b


import Data.String as S
open S using (String)

-- Not really about categories, so maybe move elsewhere
record Show (A : Set o) : Set (suc o) where
  field
    show : A → String

open Show ⦃ … ⦄ public

instance

  open import Data.Nat

  import Data.Bool as B
  import Data.Bool.Show as BS
  import Data.Nat.Show as NS
  open import Data.Fin using (Fin)
  import Data.Fin.Show as FS

  Bool-Show : Show B.Bool
  Bool-Show = record { show = BS.show }

  ℕ-Show : Show ℕ
  ℕ-Show = record { show = NS.show }

  Fin-Show : ∀ {n} → Show (Fin n)
  Fin-Show = record { show = FS.show }

  import Data.String as S
  String-Show : Show S.String
  String-Show = record { show = S.show }

  -- etc
