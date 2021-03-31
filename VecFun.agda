-- Length-preserving vector functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecFun where

open import Function using (_∘′_; case_of_; const) renaming (id to id′)
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (zip)
  renaming (map to map×; map₁ to map×₁; map₂ to map×₂)
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open ≡-Reasoning

import Category as C
open C hiding (⊤; _×_)

private
  variable
    A B C D : Set
    n : ℕ

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = ∀ {n} → Vec A n → Vec B n

infix 4 _≗_
_≗_ : (f g : A ↠ B) → Set _
f ≗ g = ∀ {n} (as : Vec _ n) → f as ≡ g as

-- Mapping a function (combinational logic)
arr : (A → B) → (A ↠ B)
arr f = map f

module VecFunInstances where

  instance

    category : Category _↠_
    category = record { id = id′ ; _∘_ = λ g f → g ∘′ f }

    monoidal : Monoidal _↠_
    monoidal = record
                 { ⊤ = ⊤
                 ; _×_ = _×_
                 ; _⊗_ = λ f g →  uncurry zip ∘′ map× f g ∘′ unzip
                 ; ! = λ _ → replicate tt
                 ; unitorᵉˡ = arr unitorᵉˡ
                 ; unitorᵉʳ = arr unitorᵉʳ
                 ; unitorⁱˡ = arr unitorⁱˡ
                 ; unitorⁱʳ = arr unitorⁱʳ
                 ; assocʳ = arr C.assocʳ
                 ; assocˡ = arr C.assocˡ
                 }

    braided : Braided _↠_
    braided = record { swap = arr C.swap }

-- Cons (memory/register)
delay : A → (A ↠ A)
delay a as = init (a ∷ as)

scanl : (B → A → B) → B → A ↠ B
scanl _∙_ b []       = []
scanl _∙_ b (a ∷ as) = b ∷ scanl _∙_ (b ∙ a) as

scanl′ : (B → A → B) → B → ∀ {n} → Vec A n → Vec B (suc n)
scanl′ _∙_ b []       = b ∷ []
scanl′ _∙_ b (a ∷ as) = b ∷ scanl′ _∙_ (b ∙ a) as

scanl× : (B → A → B) → B → ∀ {n} → Vec A n → Vec B n × B
scanl× _∙_ b []       = [] , b
scanl× _∙_ b (a ∷ as) = map×₁ (b ∷_) (scanl× _∙_ (b ∙ a) as)

mealy′ : ∀ {State : Set} → (A × State → B × State)
       → Vec A n × State → Vec B n × State
mealy′ f ([] , s) = [] , s
mealy′ f (a ∷ as , s) = let b , s′ = f (a , s) in
  map×₁ (b ∷_) (mealy′ f (as , s′))

scanl-via-mealy : (B → A → B) → B → Vec A n → Vec B n × B
scanl-via-mealy _∙_ b as = mealy′ (λ (a , b) → b , b ∙ a) (as , b)

scanl≡mealy : (_∙_ : B → A → B) → (e : B) → (as : Vec A n)
            → scanl× _∙_ e as ≡ scanl-via-mealy _∙_ e as
scanl≡mealy _∙_ e [] = refl
scanl≡mealy _∙_ e (a ∷ as) rewrite scanl≡mealy _∙_ (e ∙ a) as = refl


-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

init∷ : ∀ {a : A} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
init∷ as with initLast as
... | _ , _ , refl = refl

-- TODO: Package init∷ into an agda-stdlib PR.

delay∷ : ∀ {a₀ a : A} {as : Vec A n} → delay a₀ (a ∷ as) ≡ a₀ ∷ delay a as
delay∷ {a = a}{as = as} = init∷ (a ∷ as)

init∘scanl′ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
            → init (scanl′ f e as) ≡ scanl f e as
init∘scanl′ [] = refl
init∘scanl′ {f = f}{e} (a ∷ as) =
  begin
    init (e ∷ scanl′ f (f e a) as)
  ≡⟨ init∷ _ ⟩
    e ∷ init (scanl′ f (f e a) as)
  ≡⟨ cong (e ∷_) (init∘scanl′ as) ⟩
    e ∷ scanl f (f e a) as
  ∎

scanl∷ʳ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
         → scanl′ f e as ≡ scanl f e as ∷ʳ foldl _ f e as
scanl∷ʳ [] = refl
scanl∷ʳ {f = f}{e} (a ∷ as) =
  begin
    scanl′ f e (a ∷ as)
  ≡⟨⟩
    e ∷ scanl′ f (f e a) as
  ≡⟨ cong (e ∷_) (scanl∷ʳ as) ⟩
    e ∷ (scanl f (f e a) as ∷ʳ foldl _ f e (a ∷ as))
  ≡⟨⟩
    (e ∷ scanl f (f e a) as) ∷ʳ foldl _ f e (a ∷ as)
  ≡⟨⟩
    scanl f e (a ∷ as) ∷ʳ foldl _ f e (a ∷ as)
  ∎

init∷ʳ : ∀ (as : Vec A n) {x} → init (as ∷ʳ x) ≡ as
init∷ʳ [] = refl
init∷ʳ (a ∷ as) {x = x} =
  begin
    init ((a ∷ as) ∷ʳ x)
  ≡⟨⟩
    init (a ∷ (as ∷ʳ x))
  ≡⟨ init∷ _ ⟩
    a ∷ init (as ∷ʳ x)
  ≡⟨ cong (a ∷_) (init∷ʳ as) ⟩
    a ∷ as
  ∎


{-

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

open import Data.Bool

bval : Bool → ℕ
bval false = 0
bval true  = 1

⟦_⟧ : Vec Bool n → ℕ
⟦_⟧ = foldl _ (λ n b → bval b + 2 * n) 0

ex₁ : ⟦ true ∷ false ∷ true ∷ [] ⟧ ≡ 5
ex₁ = refl


Carry : Set
Carry = Bool

halfAdd : Bool → Bool → Bool × Carry
halfAdd a b = a xor b , a ∧ b

fullAdd : Carry → Bool → Bool → Bool × Carry
fullAdd cin a b =
  let a+b , cout₁ = halfAdd a b
      p , cout₂ = halfAdd cin a+b
  in
    p , cout₁ ∨ cout₂

addⱽ : Carry → Vec Bool n → Vec Bool n → Vec Bool n × Carry
addⱽ cin [] [] = [] , cin
addⱽ cin (a ∷ as) (b ∷ bs) =
  let sum₁ , cout₁ = fullAdd cin a b
      sums , cout  = addⱽ cout₁ as bs
  in
    sum₁ ∷ sums , cout

⟦_⟧ᵒ : Vec Bool n × Carry → ℕ
⟦_⟧ᵒ {n} (bs , cout) = ⟦ bs ⟧ + 2 ^ n * bval cout
-- ⟦ bs , cout ⟧ᵒ = ⟦ bs ∷ʳ cout ⟧

open import Data.Nat.Properties

{-

⟦addⱽ⟧ : ∀ cin (as bs : Vec Bool n) → ⟦ addⱽ cin as bs ⟧ᵒ ≡ bval cin + ⟦ as ⟧ + ⟦ bs ⟧

⟦addⱽ⟧ {zero} cin [] [] =
  begin
    ⟦ addⱽ cin [] [] ⟧ᵒ
  ≡⟨⟩
    bval cin + zero
  ≡˘⟨ +-identityʳ _ ⟩
    bval cin + zero + zero
  ≡⟨⟩
    bval cin + ⟦ [] ⟧ + ⟦ [] ⟧
  ∎

⟦addⱽ⟧ {suc n} cin (a ∷ as) (b ∷ bs) =
  begin
    ⟦ addⱽ cin (a ∷ as) (b ∷ bs) ⟧ᵒ
  ≡⟨⟩
      ⟦ (let sum₁ , cout₁ = fullAdd cin a b ; sums , cout  = addⱽ cout₁ as bs in sum₁ ∷ sums , cout) ⟧ᵒ
  ≡⟨ {!!} ⟩
    {!!}
  ≡⟨⟩
    bval cin + ⟦ a ∷ as ⟧ + ⟦ b ∷ bs ⟧
  ∎

-}

-}

{-

-- Equivalence relation for easier reasoning.

refl≗ : ∀ {f : A ↠ B} → f ≗ f
refl≗ as = refl

sym≗ : ∀ {f g : A ↠ B} → f ≗ g → g ≗ f
sym≗ f≗g as = sym (f≗g as)

trans≗ : ∀ {f g h : A ↠ B} → f ≗ g → g ≗ h → f ≗ h
trans≗ f≗g g≗h as = trans (f≗g as) (g≗h as)

open import Relation.Binary

isEq : IsEquivalence {A = A ↠ B} _≗_
isEq = record { refl = λ {f} → refl≗ {f = f} ; sym = sym≗ ; trans = trans≗ }

≗-setoid : Set → Set → Setoid _ _
≗-setoid A B = record { isEquivalence = isEq {A}{B} }

-- Is cong≗ provable without assuming extensionality?

-- cong≗ : ∀ (P : (A ↠ B) → (C ↠ D)) {f g : A ↠ B} → f ≗ g → P f ≗ P g
-- cong≗ P {f} {g} f≗g as =
--   begin
--      P f as
--   ≡⟨⟩
--      P (λ s → f s) as
--   ≡⟨ ? ⟩
--      P (λ s → g s) as
--   ≡⟨ {!!} ⟩
--     P g as
--   ∎

-}
