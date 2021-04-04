-- Length-preserving vector functions, used as semantics for Mealy machines

{-# OPTIONS --safe --without-K #-}

module VecFun where

open import Data.Product using (_,_; uncurry; <_,_>)
open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open ≡-Reasoning

open import Category

private
  variable
    A B C D : Set
    n : ℕ

infix 0 _↠_
_↠_ : Set → Set → Set
A ↠ B = ∀ {n} → Vec A n → Vec B n

infix 0 _⇨_
record _⇨_ (A B : Set) : Set where
  constructor mk
  field
    f : A ↠ B

infix 4 _≗_
_≗_ : (f g : A ⇨ B) → Set _
mk f ≗ mk g = ∀ {n} (as : Vec _ n) → f as ≡ g as

causal : A ⇨ B → Set
causal (mk f) = ∀ m {n} (as : Vec _ (m + n)) → f (take m as) ≡ take m (f as)

-- -- I'd rather write the following, but it doesn't type
-- causal f = ∀ m n → take m {n} ∘ f ≗ f ∘ take m {n}

-- Mapping a function (combinational logic)
arr : (A → B) → (A ⇨ B)
arr f = mk (map f)

zip′ : Vec A n × Vec B n → Vec (A × B) n
zip′ = uncurry zip

module VecFunInstances where

  instance

    meaningful : ∀ {A}{B} → Meaningful {μ = A ↠ B} (A ⇨ B)
    meaningful = record { ⟦_⟧ = λ { (mk f) → f } }

    category : Category _⇨_
    category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_ = λ (mk f) (mk g) →  mk (zip′ ∘ (f ⊗ g) ∘ unzip)
      ; ! = arr !
      ; unitorᵉˡ = arr unitorᵉˡ
      ; unitorᵉʳ = arr unitorᵉʳ
      ; unitorⁱˡ = arr unitorⁱˡ
      ; unitorⁱʳ = arr unitorⁱʳ
      ; assocʳ = arr assocʳ
      ; assocˡ = arr assocˡ
      }

    braided : Braided _⇨_
    braided = record { swap = arr swap }

    constants : Constant _⇨_
    constants = record { const = arr ∘ const }

    import Data.Bool as B
    logic : Logic _⇨_
    logic = record
              { ∧   = arr (uncurry B._∧_)
              ; ∨   = arr (uncurry B._∨_)
              ; xor = arr (uncurry B._xor_)
              ; not = arr B.not
              }

-- Cons (memory/register)
delay : A → (A ⇨ A)
delay a = mk (λ as → init (a ∷ as))

scanl : (B → A → B) → B → A ⇨ B
scanl {B}{A} _∙_ b₀ = mk (go b₀)
 where
   go : B → ∀ {m} → Vec A m → Vec B m
   go b []       = []
   go b (a ∷ as) = b ∷ go (b ∙ a) as

scanl′ : (B → A → B) → B → ∀ {n} → Vec A n → Vec B (suc n)
scanl′ _∙_ b []       = b ∷ []
scanl′ _∙_ b (a ∷ as) = b ∷ scanl′ _∙_ (b ∙ a) as

scanl× : (B → A → B) → B → ∀ {n} → Vec A n → Vec B n × B
scanl× _∙_ b []       = [] , b
scanl× _∙_ b (a ∷ as) = first (b ∷_) (scanl× _∙_ (b ∙ a) as)

mealy′ : ∀ {State : Set} → (A × State → B × State)
       → Vec A n × State → Vec B n × State
mealy′ f ([] , s) = [] , s
mealy′ f (a ∷ as , s) = let b , s′ = f (a , s) in
  first (b ∷_) (mealy′ f (as , s′))

scanl-via-mealy : (B → A → B) → B → Vec A n → Vec B n × B
scanl-via-mealy _∙_ b as = mealy′ (λ (a , b) → b , b ∙ a) (as , b)

scanl≡mealy : (_∙_ : B → A → B) → (e : B) → (as : Vec A n)
            → scanl× _∙_ e as ≡ scanl-via-mealy _∙_ e as
scanl≡mealy _∙_ e [] = refl
scanl≡mealy _∙_ e (a ∷ as) rewrite scanl≡mealy _∙_ (e ∙ a) as = refl


-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

-- Causality

causal-id : causal {A} id
causal-id = λ m as → refl

take-zero : ∀ {a}{A : Set a}{n} (as : Vec A n) → take zero as ≡ []
take-zero as = refl

⇨[] : ∀ ((mk f) : A ⇨ B) → f [] ≡ []
⇨[] (mk f) with f [] ; ... | [] = refl

causal-arr : ∀ (f : A → B) → causal (arr f)
causal-arr f zero as = refl
causal-arr f (suc m) (a ∷ as) =
  begin
    map f (take (suc m) (a ∷ as))
  ≡⟨ cong (map f) (unfold-take m a as) ⟩
    map f (a ∷ take m as)
  ≡⟨⟩
    f a ∷ map f (take m as)
  ≡⟨ cong (f a ∷_) (causal-arr f m as) ⟩
    f a ∷ take m (map f as)
  ≡˘⟨ unfold-take m (f a) (map f as) ⟩
    take (suc m) (f a ∷ map f as)
  ≡⟨⟩
    take (suc m) (map f (a ∷ as))
  ∎

causal-∘ : ∀ {f : A ⇨ B}{g : B ⇨ C} → causal g → causal f → causal (g ∘ f)
causal-∘ {f = mk f}{mk g} cg cf m as =
  begin
    g (f (take m as))
  ≡⟨ cong g (cf m as) ⟩
    g (take m (f as))
  ≡⟨ cg m (f as) ⟩
    take m (g (f as))
  ∎

unzip∘take : ∀ m {n} (as : Vec A (m + n)) (bs : Vec B (m + n))
           → unzip (take m (zip as bs)) ≡ (take m as , take m bs)
unzip∘take m {n} as bs =
  begin
    unzip (take m (zip as bs))
  ≡⟨ cong unzip (take-distr-zipWith _,_ as bs) ⟩
    unzip (zip (take m as) (take m bs))
  ≡⟨ unzip∘zip (take m as) (take m bs) ⟩
    (take m as , take m bs)
  ∎

≡zip : ∀ (ps : Vec (A × B) n) → ps ≡ zip (map exl ps) (map exr ps)
≡zip ps =
  begin
    ps
  ≡⟨ sym (map-id ps) ⟩
    map id ps
  ≡⟨⟩
    map (exl △ exr) ps
  ≡⟨ map-<,>-zip exl exr ps ⟩
    zip (map exl ps) (map exr ps)
  ∎
 
causal-⊗ : ∀ {f : A ⇨ C}{g : B ⇨ D} → causal f → causal g → causal (f ⊗ g)
causal-⊗ {f = mk f} {mk g} cf cg m ps =
  begin
    (zip′ ∘ (f ⊗ g) ∘ unzip) (take m ps)
  ≡⟨ cong (zip′ ∘ (f ⊗ g) ∘ unzip ∘ take m) (≡zip ps) ⟩
    (zip′ ∘ (f ⊗ g) ∘ unzip) (take m (zip (map exl ps) (map exr ps)))
  ≡⟨ cong (zip′ ∘ (f ⊗ g) ∘ unzip) (take-distr-zipWith _,_ (map exl ps) (map exr ps)) ⟩
    (zip′ ∘ (f ⊗ g) ∘ unzip) (zip (take m (map exl ps)) (take m (map exr ps)))
  ≡⟨ cong (zip′ ∘ (f ⊗ g) ∘ unzip) (cong₂ zip (take-distr-map exl m ps) (take-distr-map exr m ps)) ⟩
    (zip′ ∘ (f ⊗ g) ∘ unzip) (zip (map exl (take m ps)) (map exr (take m ps)))
  ≡⟨ cong (zip′ ∘ (f ⊗ g)) (unzip∘zip (map exl (take m ps)) (map exr (take m ps))) ⟩
    (zip′ ∘ (f ⊗ g)) (map exl (take m ps) , map exr (take m ps))
  ≡⟨⟩
    zip (f (map exl (take m ps))) (g (map exr (take m ps)))
  ≡˘⟨ cong₂ (λ as bs → zip (f as) (g bs)) (take-distr-map exl m ps) (take-distr-map exr m ps) ⟩
    zip (f (take m (map exl ps))) (g (take m (map exr ps)))
  ≡⟨ cong₂ zip (cf m (map exl ps)) (cg m (map exr ps)) ⟩
    zip (take m (f (map exl ps))) (take m (g (map exr ps)))
  ≡˘⟨ take-distr-zipWith _,_ (f (map exl ps)) (g (map exr ps)) ⟩
    take m (zip (f (map exl ps)) (g (map exr ps)))
  ≡⟨⟩
    take m (zip′ ((f ⊗ g) (map exl ps , map exr ps)))
  ≡˘⟨ cong (take m ∘ zip′ ∘ (f ⊗ g)) (unzip∘zip (map exl ps) (map exr ps)) ⟩
    take m (zip′ ((f ⊗ g) (unzip (zip (map exl ps) (map exr ps)))))
  ≡˘⟨ cong (take m ∘ zip′ ∘ (f ⊗ g) ∘ unzip) (≡zip ps) ⟩
    take m (zip′ ((f ⊗ g) (unzip ps)))
  ∎

init∷ : ∀ {a : A} (as : Vec A (suc n)) → init (a ∷ as) ≡ a ∷ init as
init∷ as with initLast as
... | _ , _ , refl = refl

-- TODO: Package init∷ into an agda-stdlib PR.

delay∷ : ∀ {a₀ a : A} {as : Vec A n} → ⟦ delay a₀ ⟧ (a ∷ as) ≡ a₀ ∷ ⟦ delay a ⟧ as
delay∷ {a = a}{as = as} = init∷ (a ∷ as)

init∘scanl′ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
            → init (scanl′ f e as) ≡ ⟦ scanl f e ⟧ as
init∘scanl′ [] = refl
init∘scanl′ {f = f}{e} (a ∷ as) =
  begin
    init (e ∷ scanl′ f (f e a) as)
  ≡⟨ init∷ _ ⟩
    e ∷ init (scanl′ f (f e a) as)
  ≡⟨ cong (e ∷_) (init∘scanl′ as) ⟩
    e ∷ ⟦ scanl f (f e a) ⟧ as
  ∎

scanl∷ʳ : ∀ {f : B → A → B} {e : B} (as : Vec A n)
         → scanl′ f e as ≡ ⟦ scanl f e ⟧ as ∷ʳ foldl _ f e as
scanl∷ʳ [] = refl
scanl∷ʳ {f = f}{e} (a ∷ as) =
  begin
    scanl′ f e (a ∷ as)
  ≡⟨⟩
    e ∷ scanl′ f (f e a) as
  ≡⟨ cong (e ∷_) (scanl∷ʳ as) ⟩
    e ∷ (⟦ scanl f (f e a) ⟧ as ∷ʳ foldl _ f e (a ∷ as))
  ≡⟨⟩
    (e ∷ ⟦ scanl f (f e a) ⟧ as) ∷ʳ foldl _ f e (a ∷ as)
  ≡⟨⟩
    ⟦ scanl f e ⟧ (a ∷ as) ∷ʳ foldl _ f e (a ∷ as)
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

refl≗ : ∀ {f : A ⇨ B} → f ≗ f
refl≗ as = refl

sym≗ : ∀ {f g : A ⇨ B} → f ≗ g → g ≗ f
sym≗ f≗g as = sym (f≗g as)

trans≗ : ∀ {f g h : A ⇨ B} → f ≗ g → g ≗ h → f ≗ h
trans≗ f≗g g≗h as = trans (f≗g as) (g≗h as)

open import Relation.Binary

isEq : IsEquivalence {A = A ⇨ B} _≗_
isEq = record { refl = λ {f} → refl≗ {f = f} ; sym = sym≗ ; trans = trans≗ }

≗-setoid : Set → Set → Setoid _ _
≗-setoid A B = record { isEquivalence = isEq {A}{B} }

-- Is cong≗ provable without assuming extensionality?

-- cong≗ : ∀ (P : (A ⇨ B) → (C ⇨ D)) {f g : A ⇨ B} → f ≗ g → P f ≗ P g
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
