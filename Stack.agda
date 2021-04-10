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

open import Ty
open import Category

module Stack (_↠′_ : Ty → Ty → Set) (let private infix 0 _↠_; _↠_ = _↠′_)
             ⦃ _ : ∀ {A B} → Meaningful {μ = A ty.⇨ B} (A ↠ B) ⦄ where

open import Data.Product using (∃; _,_)

private variable a b c d i o z zⁱ zᵒ zᵃ zᵇ zᶜ zᵈ : Ty

-- TODO: replace superscripts by subscripts in z names?

-- Primitive instance: primitive `p` with input routing for `first p`.
module i where

  infix 0 _⇨_
  _⇨_ : (Ty × Ty) → (Ty × Ty) → Set
  (i , zⁱ ⇨ o , zᵒ) = ∃ λ a → (a ↠ o) × (i × zⁱ r.⇨ a × zᵒ)

  instance

    meaningful : Meaningful {μ = i × zⁱ ty.⇨ o × zᵒ} (i , zⁱ ⇨ o , zᵒ)
    meaningful {i}{zⁱ}{o}{zᵒ} = record
      { ⟦_⟧ = λ (a , a↠o , i×zⁱ⇨ᵣa×zᵒ) → first ⟦ a↠o ⟧ ∘ ⟦ i×zⁱ⇨ᵣa×zᵒ ⟧ }


-- Stack operations
module k where

  infix 0 _⇨_
  infixl 5 _∷ʳ_
  data _⇨_ : Ty × Ty → Ty × Ty → Set where
    [_]  : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
    _∷ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ i.⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)

  route : (i × zⁱ r.⇨ o × zᵒ) → (i , zⁱ ⇨ o , zᵒ)
  route = [_]

  instance

    meaningful : Meaningful (i , zⁱ ⇨ o , zᵒ)
    meaningful = record { ⟦_⟧ = ⟦_⟧′ }
     where
       ⟦_⟧′ : (i , zⁱ ⇨ o , zᵒ) → (i × zⁱ ty.⇨ o × zᵒ)
       ⟦ [ r ] ⟧′ = ⟦ r ⟧
       ⟦ f ∷ʳ inst ⟧′ = ⟦ f ⟧′ ∘ ⟦ inst ⟧

    category : Category _⇨_
    category = record { id = route id ; _∘_ = _∘′_ }
     where
       infixr 9 _∘ʳ_
       _∘ʳ_ : (a , zᵃ ⇨ o , zᵒ) → (i × zⁱ r.⇨ a × zᵃ) → (i , zⁱ ⇨ o , zᵒ)
       [ r₂ ] ∘ʳ r₁ = [ r₂ ∘ r₁ ]
       (g ∷ʳ (d , d↠e , r₂)) ∘ʳ r₁ = g ∷ʳ (d , d↠e , r₂ ∘ r₁)

       infixr 9 _∘′_
       _∘′_ : (a , zᵃ ⇨ o , zᵒ) → (i , zⁱ ⇨ a , zᵃ) → (i , zⁱ ⇨ o , zᵒ)
       g ∘′ [ r ] = g ∘ʳ r
       g ∘′ (f ∷ʳ inst) = g ∘′ f ∷ʳ inst

       -- -- Or drop _∘ʳ_, although Agda shades the last clause gray.
       -- [ r₂ ] ∘′ [ r₁ ] = [ r₂ ∘ r₁ ]
       -- (g ∷ʳ (d , d↠e , r₂)) ∘′ [ r₁ ] = g ∷ʳ (d , d↠e , r₂ ∘ r₁)
       -- g ∘′ (f ∷ʳ inst) = g ∘′ f ∷ʳ inst

  open ≈-Reasoning

  infixr 9 _⟦∘⟧_
  _⟦∘⟧_ : ∀ (g : b , zᵇ ⇨ c , zᶜ) (f : a , zᵃ ⇨ b , zᵇ)
        → ⟦ g ∘ f ⟧ ≈ ⟦ g ⟧ ∘ ⟦ f ⟧

  [ r₂ ] ⟦∘⟧ [ r₁ ] = F-∘ r₂ r₁   where open Functor r.⟦⟧-functor

  (g ∷ʳ (d , d↠e , r₂)) ⟦∘⟧ [ r₁ ] = let open Functor r.⟦⟧-functor in
    begin
      ⟦ (g ∷ʳ (d , d↠e , r₂)) ∘ [ r₁ ] ⟧
    ≡⟨⟩
      ⟦ g ∷ʳ (d , d↠e , r₂ ∘ r₁) ⟧
    ≡⟨⟩
      ⟦ g ⟧ ∘ ⟦ d , d↠e , r₂ ∘ r₁ ⟧
    ≡⟨⟩
      ⟦ g ⟧ ∘ (first ⟦ d↠e ⟧ ∘ ⟦ r₂ ∘ r₁ ⟧)
    ≈⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (∘-resp-≈ʳ {h = first ⟦ d↠e ⟧} (F-∘ r₂ r₁)) ⟩
      ⟦ g ⟧ ∘ (first ⟦ d↠e ⟧ ∘ (⟦ r₂ ⟧ ∘ ⟦ r₁ ⟧))
    ≈˘⟨ ∘-resp-≈ʳ {h = ⟦ g ⟧} (assoc {f = ⟦ r₁ ⟧}{g = ⟦ r₂ ⟧}{h = first ⟦ d↠e ⟧}) ⟩
      ⟦ g ⟧ ∘ ((first ⟦ d↠e ⟧ ∘ ⟦ r₂ ⟧) ∘ ⟦ r₁ ⟧)
    ≈˘⟨ assoc {g = first ⟦ d↠e ⟧ ∘ ⟦ r₂ ⟧}{h = ⟦ g ⟧}⟩
      (⟦ g ⟧ ∘ (first ⟦ d↠e ⟧ ∘ ⟦ r₂ ⟧)) ∘ ⟦ r₁ ⟧
    ≡⟨⟩
      ⟦ g ∷ʳ (d , d↠e , r₂) ⟧ ∘ ⟦ [ r₁ ] ⟧
    ∎

  g ⟦∘⟧ (f ∷ʳ inst) = let open Functor r.⟦⟧-functor in
    begin
      ⟦ g ∘ (f ∷ʳ inst) ⟧
    ≡⟨⟩
      ⟦ (g ∘ f) ∷ʳ inst ⟧
    ≡⟨⟩
      ⟦ g ∘ f ⟧ ∘ ⟦ inst ⟧
    ≈⟨ ∘-resp-≈ˡ {h = ⟦ g ∘ f ⟧} (g ⟦∘⟧ f) ⟩
      (⟦ g ⟧ ∘ ⟦ f ⟧) ∘ ⟦ inst ⟧
    ≈⟨ assoc {g = ⟦ f ⟧}{h = ⟦ g ⟧} ⟩
      ⟦ g ⟧ ∘ (⟦ f ⟧ ∘ ⟦ inst ⟧)
    ≡⟨⟩
      ⟦ g ⟧ ∘ ⟦ f ∷ʳ inst ⟧
    ∎

  ⟦⟧-functor : Functor _⇨_ ty._⇨_ 0ℓ
  ⟦⟧-functor = record
    { Fₒ = λ (i , zⁱ) → i × zⁱ
    ; Fₘ = ⟦_⟧
    ; F-id = λ _ → swizzle-id
    ; F-∘ = _⟦∘⟧_
    }

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = F-equiv ⟦⟧-functor

  lawful-category : LawfulCategory 0ℓ _⇨_
  lawful-category = LawfulCategoryᶠ ⟦⟧-functor

  push : (a × b) , c ⇨ a , (b × c)
  push = route assocʳ

  pop : a , (b × c) ⇨ (a × b) , c
  pop = route assocˡ

  stacked : (a , (b × z) ⇨ c , (b × z)) → ((a × b) , z) ⇨ ((c × b) , z)
  stacked f = pop ∘ f ∘ push

  prim : i ↠ o → i , zⁱ ⇨ o , zⁱ
  prim {i} i↠o = [ id ] ∷ʳ (i , i↠o , id)


open k using (stacked)

-- Stack-preserving function
module sf where

  infix 0 _⇨_
  record _⇨_ (i o : Ty) : Set where
    constructor mk
    field
      f : ∀ {z} → i , z k.⇨ o , z

  prim : i ↠ o → i ⇨ o
  prim i↠o = mk (k.prim i↠o)

  route : i r.⇨ o → i ⇨ o
  route r = mk (k.route (first r))

  instance

    meaningful : ∀ {a b} → Meaningful {μ = a ty.⇨ b} (a ⇨ b)
    meaningful {a}{b} = record { ⟦_⟧ = λ (mk f) → unitorᵉʳ ∘ ⟦ f ⟧ ∘ unitorⁱʳ }

    category : Category _⇨_
    category = record { id = route id  ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

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
       first′ (mk f) = mk (stacked f)

       second′ : (b ⇨ d) → (a × b ⇨ a × d)
       second′ f = route swap ∘ first′ f ∘ route swap

    braided : Braided _⇨_
    braided = record { swap = route swap }

    cartesian : Cartesian _⇨_
    cartesian = record { exl = route exl ; exr = route exr ; dup = route dup }

    logic : ⦃ Logic _↠_ ⦄ → Logic _⇨_
    logic = record { ∧ = prim ∧ ; ∨ = prim ∨ ; xor = prim xor ; not = prim not
                   ; false = prim false ; true = prim true }

  import Symbolic _↠_ as s

  -- Functorial compilation
  compile : a s.⇨ b → a ⇨ b
  compile (s.`route r) = route r
  compile (s.`prim  p) = prim p
  compile ( g s.`∘ f ) = compile g ∘ compile f
  compile ( f s.`⊗ g ) = compile f ⊗ compile g
