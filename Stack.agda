{-# OPTIONS --safe --without-K #-}

-- A linearizing category, parametrized by primitives. This category embodies a
-- normal form for categorical formulas as a strictly linear composition of the
-- following form:
--
--     unitorᵉʳ ∘ rₙ ∘ first pₙ₋₁ ∘ rₙ₋₁ ⋯ ∘ first p₀ ∘ r₀ ∘ unitorⁱʳ
--  
-- where the `pᵢ` are primitive operations and the `rᵢ` are pure routings. This
-- category was designed to capture the simple essence of stack machines and
-- compiling to them homomorphically. It appears also to capture SSA and
-- hardware netlists nicely. Primitives always operate on the first part of a
-- pair ("the accumulator") while preserving the second ("the stack"). The first
-- and final unitor steps introduce and eliminate empty stacks, respectively.
-- See http://conal.net/papers/calculating-compilers-categorically .

open import Level using (0ℓ)

module Stack where

open import Data.Product using (∃; _,_)

open import Ty
open import Category
import Primitive as p

private variable a b c d i o z zⁱ zᵒ zᵃ zᵇ zᶜ zᵈ : Ty

-- TODO: replace superscripts by subscripts in z names.

-- Stack operations
module k where

  infix 0 _⇨_
  infixr 9 _◦first_◦_  -- (note ◦ vs ∘)
  data _⇨_ : Ty × Ty → Ty × Ty → Set where
    ⌞_⌟ : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
    _◦first_◦_ : (b , z ⇨ o , zᵒ) → (a p.⇨ b) → (i × zⁱ r.⇨ a × z)
                → (i , zⁱ ⇨ o , zᵒ)
    
  route : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
  route = ⌞_⌟

  ⟦_⟧′ : (i , zⁱ ⇨ o , zᵒ) → (i × zⁱ ty.⇨ o × zᵒ)
  ⟦ ⌞ r ⌟ ⟧′ = ⟦ r ⟧
  ⟦ f ◦first p ◦ r ⟧′ = ⟦ f ⟧′ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧

  infixr 9 _∘′_
  _∘′_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ ⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)
  g ∘′ (f ◦first p ◦ r) = (g ∘′ f) ◦first p ◦ r
  (g ◦first p ◦ r₂) ∘′ ⌞ r₁ ⌟ = g ◦first p ◦ (r₂ ∘ r₁)
  ⌞ r₂ ⌟ ∘′ ⌞ r₁ ⌟ = ⌞ r₂ ∘ r₁ ⌟

  instance

    meaningful : Meaningful (i , zⁱ ⇨ o , zᵒ)
    meaningful = record { ⟦_⟧ = ⟦_⟧′ }

    category : Category _⇨_
    category = record { id = route id ; _∘_ = _∘′_ }

  open ≈-Reasoning

  infixr 9 _⟦∘⟧_
  _⟦∘⟧_ : ∀ (g : b , zᵇ ⇨ c , zᶜ) (f : a , zᵃ ⇨ b , zᵇ)
        → ⟦ g ∘ f ⟧ ≈ ⟦ g ⟧ ∘ ⟦ f ⟧

  g ⟦∘⟧ (f ◦first p ◦ r) = let open CategoryH r.⟦⟧-categoryH in
    begin
      ⟦ g ∘ (f ◦first p ◦ r) ⟧
    ≡⟨⟩
      ⟦ (g ∘ f) ◦first p ◦ r ⟧
    ≡⟨⟩
      ⟦ g ∘ f ⟧ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧
    ≈⟨ ∘-resp-≈ˡ {h = ⟦ g ∘ f ⟧} (g ⟦∘⟧ f) ⟩
      (⟦ g ⟧ ∘ ⟦ f ⟧) ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧
    ≈⟨ assoc {g = ⟦ f ⟧}{h = ⟦ g ⟧} ⟩
      ⟦ g ⟧ ∘ (⟦ f ⟧ ∘ first ⟦ p ⟧ ∘ ⟦ r ⟧)
    ≡⟨⟩
      ⟦ g ⟧ ∘ ⟦ f ◦first p ◦ r ⟧
    ∎

  (g ◦first p ◦ r₂) ⟦∘⟧ ⌞ r₁ ⌟ = let open CategoryH r.⟦⟧-categoryH in
    begin
      ⟦ (g ◦first p ◦ r₂) ∘ ⌞ r₁ ⌟ ⟧
    ≡⟨⟩
      ⟦ g ◦first p ◦ (r₂ ∘ r₁) ⟧
    ≡⟨⟩
      ⟦ g ⟧ ∘ first ⟦ p ⟧  ∘ ⟦ r₂ ∘ r₁ ⟧
    ≈⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (∘-resp-≈ʳ {h = first ⟦ p ⟧} (F-∘ r₂ r₁)) ⟩
      ⟦ g ⟧ ∘ (first ⟦ p ⟧ ∘ (⟦ r₂ ⟧ ∘ ⟦ r₁ ⟧))
    ≈˘⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (assoc {f = ⟦ r₁ ⟧}{g = ⟦ r₂ ⟧}{h = first ⟦ p ⟧}) ⟩
      ⟦ g ⟧ ∘ ((first ⟦ p ⟧ ∘ ⟦ r₂ ⟧) ∘ ⟦ r₁ ⟧)
    ≈˘⟨ assoc {g = first ⟦ p ⟧ ∘ ⟦ r₂ ⟧}{h = ⟦ g ⟧}⟩
      (⟦ g ⟧ ∘ (first ⟦ p ⟧ ∘ ⟦ r₂ ⟧)) ∘ ⟦ r₁ ⟧
    ≡⟨⟩
      ⟦ g ◦first p ◦ r₂ ⟧ ∘ ⟦ ⌞ r₁ ⌟ ⟧
    ∎

  ⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘ r₂ r₁   where open CategoryH r.⟦⟧-categoryH

  ⟦⟧-Hₒ : Homomorphismₒ (Ty × Ty) Ty
  ⟦⟧-Hₒ = record { Fₒ = λ (i , zⁱ) → i × zⁱ }

  ⟦⟧-H : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-H = record { Hₒ = ⟦⟧-Hₒ ; Fₘ = ⟦_⟧ }
  -- ⟦⟧-H = record { Fₘ = ⟦_⟧ }

  -- Without the explicit homomorphismₒ, I get an error:
  --
  --   No instance of type Homomorphismₒ (Data.Product.Σ Ty (λ x → Ty)) Ty
  --   was found in scope.
  --   when checking that ⟦_⟧ is a valid argument to a function of type
  --   ⦃ homomorphismₒ
  --     : Homomorphismₒ ((→Instances.products Products.× Ty) Ty) Ty ⦄ →
  --   ({a b : (→Instances.products Products.× Ty) Ty} →
  --    a ⇨ b →
  --    Homomorphismₒ.Fₒ homomorphismₒ a ty.⇨
  --    Homomorphismₒ.Fₒ homomorphismₒ b) →
  --   "dummyType: src/full/Agda/TypeChecking/Rules/Application.hs:722"
  --
  -- What's going on here? Similar problems below.

  ⟦⟧-categoryH : CategoryH _⇨_ ty._⇨_ 0ℓ ⦃ H = ⟦⟧-H ⦄
  ⟦⟧-categoryH = record { F-id = λ _ → swizzle-id ; F-∘ = _⟦∘⟧_ }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = H-equiv ⟦⟧-H

  lawful-category : LawfulCategory 0ℓ _⇨_ ⦃ equiv = equivalent ⦄
  lawful-category = LawfulCategoryᶠ ⦃ H = ⟦⟧-H ⦄ ⟦⟧-categoryH

  push : (a × b) , c ⇨ a , (b × c)
  push = route assocʳ

  pop : a , (b × c) ⇨ (a × b) , c
  pop = route assocˡ

  stacking : (a , (b × z) ⇨ c , (b × z)) → ((a × b) , z) ⇨ ((c × b) , z)
  stacking f = pop ∘ f ∘ push

  prim : (i p.⇨ o) → (i , zⁱ ⇨ o , zⁱ)
  prim p = ⌞ id ⌟ ◦first p ◦ id

open k using (stacking)

-- Stack-preserving function
module sf where

  infix 0 _⇨_
  record _⇨_ (i o : Ty) : Set where
    constructor mk
    field
      f : ∀ {z} → i , z k.⇨ o , z

  prim : i p.⇨ o → i ⇨ o
  prim p = mk (k.prim p)

  route : i r.⇨ o → i ⇨ o
  route r = mk (k.route (first r))

  ⟦_⟧′ : (a ⇨ b) → (a ty.⇨ b)
  ⟦ mk f ⟧′ = unitorᵉʳ ∘ ⟦ f ⟧ ∘ unitorⁱʳ

  instance

    meaningful : ∀ {a b} → Meaningful {μ = a ty.⇨ b} (a ⇨ b)
    meaningful = record { ⟦_⟧ = ⟦_⟧′ }
    -- meaningful = record { ⟦_⟧ = λ (mk f) → unitorᵉʳ ∘ ⟦ f ⟧ ∘ unitorⁱʳ }

    category : Category _⇨_
    category = record { id = route id  ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

    ⟦⟧-Hₒ : Homomorphismₒ Ty Ty
    ⟦⟧-Hₒ = record { Fₒ = λ a → a }

    ⟦⟧-H : Homomorphism _⇨_ ty._⇨_
    ⟦⟧-H = record { Fₘ = ⟦_⟧ }

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = H-equiv ⟦⟧-H

    open import Relation.Binary.PropositionalEquality

    ⟦⟧-categoryH : CategoryH _⇨_ ty._⇨_ 0ℓ
    ⟦⟧-categoryH = record
      { F-id = λ x → swizzle-id
      ; F-∘  = λ g@(mk g′) f@(mk f′) →
          begin
            ⟦ g ∘ f ⟧
          ≡⟨⟩
            ⟦ mk g′ ∘ mk f′ ⟧
          ≡⟨⟩
            ⟦ mk (g′ ∘ f′) ⟧
          ≡⟨⟩
            unitorᵉʳ ∘ ⟦ g′ ∘ f′ ⟧ ∘ unitorⁱʳ
          ≡⟨⟩
            unitorᵉʳ ∘ k.⟦ g′ ∘ f′ ⟧′ ∘ unitorⁱʳ
          ≈⟨ ∘-resp-≈ʳ {_⇨′_ = ty._⇨_} {h = unitorᵉʳ}
                (∘-resp-≈ˡ {_⇨′_ = ty._⇨_} (F-∘ g′ f′)) ⟩
            unitorᵉʳ ∘ (k.⟦ g′ ⟧′ ∘ k.⟦ f′ ⟧′) ∘ unitorⁱʳ
          ≈⟨ (λ x → refl) ⟩
            (unitorᵉʳ ∘ k.⟦ g′ ⟧′ ∘ unitorⁱʳ) ∘ (unitorᵉʳ ∘ k.⟦ f′ ⟧′ ∘ unitorⁱʳ)
          ≡⟨⟩
            ⟦ g ⟧′ ∘ ⟦ f ⟧′
          ∎
      }
     where open ≈-Reasoning
           open CategoryH ⦃ H = k.⟦⟧-H ⦄ k.⟦⟧-categoryH

    lawful-category : LawfulCategory 0ℓ _⇨_
    lawful-category = LawfulCategoryᶠ ⟦⟧-categoryH

    monoidal : Monoidal _⇨_
    monoidal = record
      { _⊗_ = λ f g → second′ g ∘ first′ f
      ; !        = route !
      ; unitorᵉˡ = route unitorᵉˡ
      ; unitorᵉʳ = route unitorᵉʳ
      ; unitorⁱˡ = route unitorⁱˡ
      ; unitorⁱʳ = route unitorⁱʳ
      ; assocʳ   = route assocʳ
      ; assocˡ   = route assocˡ
      }
     where
       first′ : (a ⇨ c) → (a × b ⇨ c × b)
       first′ (mk f) = mk (stacking f)

       second′ : (b ⇨ d) → (a × b ⇨ a × d)
       second′ f = route swap ∘ first′ f ∘ route swap

    braided : Braided _⇨_
    braided = record { swap = route swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = route exl ; exr = route exr ; dup = route dup }

    logic : Logic _⇨_
    logic = record { ∧ = prim ∧ ; ∨ = prim ∨ ; xor = prim xor ; not = prim not
                   ; false = prim false ; true = prim true ; cond = prim cond }

  import Symbolic as s
  -- Homomorphic compilation. Pretty and unnecessary. TODO: move this function
  -- to Symbolic, and generalize the target category.
  compile : a s.⇨ b → a ⇨ b
  compile (s.`route r) = route r
  compile (s.`prim  p) = prim p
  compile ( g s.`∘ f ) = compile g ∘ compile f
  compile ( f s.`⊗ g ) = compile f ⊗ compile g
