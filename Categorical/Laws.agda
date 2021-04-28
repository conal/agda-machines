{-# OPTIONS --safe --without-K #-}

module Categorical.Laws where

open import Level using (Level; _⊔_) renaming (suc to lsuc)

open import Miscellany
open import Categorical.Raw

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record LawfulCategory {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                      q ⦃ equiv : Equivalent q _⇨′_ ⦄
                      ⦃ ⇨Category : Category _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d}
              → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    ∘-resp-≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  ∘-resp-≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘-resp-≈ˡ h≈k = ∘-resp-≈ h≈k refl

  ∘-resp-≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘-resp-≈ʳ f≈g = ∘-resp-≈ refl f≈g

  assoc² : {a₀ a₁ a₂ a₃ : obj}
           {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}
         → (f₃ ∘ f₂) ∘ f₁ ≈ f₃ ∘ f₂ ∘ f₁
  assoc² = assoc

  assoc³ : {a₀ a₁ a₂ a₃ a₄ : obj}
           {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}
         → (f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  assoc³ = ∘-resp-≈ʳ assoc² • assoc

  assoc⁴ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
   → (f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  assoc⁴ = ∘-resp-≈ʳ assoc³ • assoc

  assoc⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}{f₆ : a₅ ⇨ a₆}
   → (f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  assoc⁵ = ∘-resp-≈ʳ assoc⁴ • assoc

  -- TODO: can we define general assoc↑ that takes a ℕ?

  assoc-middle : {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{k : d ⇨ e}
               → (k ∘ h) ∘ (g ∘ f) ≈ k ∘ (h ∘ g) ∘ f
  assoc-middle = ∘-resp-≈ʳ (sym assoc) • assoc

  inAssoc : {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{gf : a ⇨ c}
            (g∘f≈gf : g ∘ f ≈ gf) → (h ∘ g) ∘ f ≈ h ∘ gf
  inAssoc {f = f}{g}{h}{gf} g∘f≈gf =
    begin
      (h ∘ g) ∘ f
    ≈⟨ assoc ⟩
      h ∘ g ∘ f
    ≈⟨ ∘-resp-≈ʳ g∘f≈gf ⟩
      h ∘ gf
    ∎

  inAssoc′ : {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{hg : b ⇨ d}
             (h∘g≈hg : h ∘ g ≈ hg) → h ∘ (g ∘ f) ≈ hg ∘ f
  inAssoc′ {f = f}{g}{h}{hg} h∘g≈hg =
    begin
      h ∘ g ∘ f
    ≈⟨ sym assoc ⟩
      (h ∘ g) ∘ f
    ≈⟨ ∘-resp-≈ˡ h∘g≈hg ⟩
      hg ∘ f
    ∎

  g⁻¹∘g∘f : {f : a ⇨ b}{g : b ⇨ c}{g⁻¹ : c ⇨ b}
            (g⁻¹∘g : g⁻¹ ∘ g ≈ id) → g⁻¹ ∘ g ∘ f ≈ f
  g⁻¹∘g∘f {f = f}{g}{g⁻¹} g⁻¹∘g = identityˡ • ∘-resp-≈ˡ g⁻¹∘g • sym assoc
  
  -- infixr 8 _✂_

  infixr 9 _◎_
  _◎_ : {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{gf : a ⇨ c}{k : a ⇨ d}
        (h∘gf≈k : h ∘ gf ≈ k) (g∘f≈gf : g ∘ f ≈ gf) → (h ∘ g) ∘ f ≈ k
  q ◎ g∘f≈gf = q • inAssoc g∘f≈gf


open LawfulCategory ⦃ … ⦄ public


record LawfulMonoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         q ⦃ equiv : Equivalent q _⇨′_ ⦄
         ⦃ _ : Monoidal _⇨′_ ⦄
       : Set (lsuc o ⊔ ℓ ⊔ lsuc q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ lawful-cat ⦄ : LawfulCategory _⇨_ q

    id⊗id : ∀ {a b : obj} → id {a = a} ⊗ id {a = b} ≈ id

    ∘⊗ : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : obj}
           {f : a₁ ⇨ a₂}{g : b₁ ⇨ b₂}
           {h : a₂ ⇨ a₃}{k : b₂ ⇨ b₃}
       → (h ⊗ k) ∘ (f ⊗ g) ≈ (h ∘ f) ⊗ (k ∘ g)

    unitorᵉˡ∘unitorⁱˡ : ∀ {a : obj} → unitorᵉˡ ∘ unitorⁱˡ {a = a} ≈ id
    unitorⁱˡ∘unitorᵉˡ : ∀ {a : obj} → unitorⁱˡ ∘ unitorᵉˡ {a = a} ≈ id

    unitorᵉʳ∘unitorⁱʳ : ∀ {a : obj} → unitorᵉʳ ∘ unitorⁱʳ {a = a} ≈ id
    unitorⁱʳ∘unitorᵉʳ : ∀ {a : obj} → unitorⁱʳ ∘ unitorᵉʳ {a = a} ≈ id

    assocʳ∘assocˡ : ∀ {a b c : obj} → assocʳ ∘ assocˡ ≈ id {a = a × (b × c)}
    assocˡ∘assocʳ : ∀ {a b c : obj} → assocˡ ∘ assocʳ ≈ id {a = (a × b) × c}

    assocˡ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
             → assocˡ ∘ (f ⊗ (g ⊗ h)) ≈ ((f ⊗ g) ⊗ h) ∘ assocˡ

    assocʳ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
             → assocʳ ∘ ((f ⊗ g) ⊗ h) ≈ (f ⊗ (g ⊗ h)) ∘ assocʳ

    ⊗-resp-≈ : ∀ {f h : a ⇨ c} {g k : b ⇨ d} (f≈h : f ≈ h) (g≈k : g ≈ k) → f ⊗ g ≈ h ⊗ k

  ⊗-resp-≈ʳ : ∀ {f : a ⇨ c} {g k : b ⇨ d} → g ≈ k → f ⊗ g ≈ f ⊗ k
  ⊗-resp-≈ʳ g≈k = ⊗-resp-≈ refl g≈k

  ⊗-resp-≈ˡ : ∀ {f h : a ⇨ c} {g : b ⇨ d} → f ≈ h → f ⊗ g ≈ h ⊗ g
  ⊗-resp-≈ˡ f≈h = ⊗-resp-≈ f≈h refl

  first∘second : ∀ {a b c d : obj} {f : a ⇨ c} {g : b ⇨ d}
               → first f ∘ second g ≈ f ⊗ g
  first∘second {f = f}{g = g} =
    begin
      first f ∘ second g
    ≡⟨⟩
      (f ⊗ id) ∘ (id ⊗ g)
    ≈⟨ ∘⊗ ⟩
      (f ∘ id) ⊗ (id ∘ g)
    ≈⟨ ⊗-resp-≈ identityʳ identityˡ ⟩
      f ⊗ g
    ∎

  second∘first : ∀ {a b c d : obj} {f : a ⇨ c} {g : b ⇨ d}
               → second g ∘ first f ≈ f ⊗ g
  second∘first {f = f}{g = g} =
    begin
      second g ∘ first f
    ≡⟨⟩
      (id ⊗ g) ∘ (f ⊗ id)
    ≈⟨ ∘⊗ ⟩
      (id ∘ f) ⊗ (g ∘ id)
    ≈⟨ ⊗-resp-≈ identityˡ identityʳ ⟩
      f ⊗ g
    ∎

  first∘first : ∀ {f : a ⇨ b} {g : b ⇨ c} {z : obj}
              → first g ∘ first f ≈ first {b = z} (g ∘ f)
  first∘first {f = f}{g} =
    begin
      first g ∘ first f
    ≡⟨⟩
      (g ⊗ id) ∘ (f ⊗ id)
    ≈⟨ ∘⊗ ⟩
     (g ∘ f) ⊗ (id ∘ id)
    ≈⟨ ⊗-resp-≈ʳ identityʳ ⟩
      (g ∘ f) ⊗ id
    ≡⟨⟩
      first (g ∘ f)
    ∎

  second∘second : ∀ {f : a ⇨ b} {g : b ⇨ c} {z : obj}
                → second g ∘ second f ≈ second {a = z} (g ∘ f)
  second∘second {f = f}{g} =
    begin
      second g ∘ second f
    ≡⟨⟩
      (id ⊗ g) ∘ (id ⊗ f)
    ≈⟨ ∘⊗ ⟩
     (id ∘ id) ⊗ (g ∘ f)
    ≈⟨ ⊗-resp-≈ˡ identityʳ ⟩
      id ⊗ (g ∘ f)
    ≡⟨⟩
      second (g ∘ f)
    ∎

  assocˡ∘⊗∘assocʳ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
                  → assocˡ ∘ (f ⊗ (g ⊗ h)) ∘ assocʳ ≈ (f ⊗ g) ⊗ h
  assocˡ∘⊗∘assocʳ {f = f}{g}{h} =
    begin
      assocˡ ∘ (f ⊗ (g ⊗ h)) ∘ assocʳ
    ≈˘⟨ ∘-resp-≈ʳ assocʳ∘⊗ ⟩
      assocˡ ∘ assocʳ ∘ ((f ⊗ g) ⊗ h)
    ≈˘⟨ assoc ⟩
      (assocˡ ∘ assocʳ) ∘ ((f ⊗ g) ⊗ h)
    ≈⟨ ∘-resp-≈ˡ (assocˡ∘assocʳ) ⟩
      id ∘ ((f ⊗ g) ⊗ h)
    ≈⟨ identityˡ ⟩
      (f ⊗ g) ⊗ h
    ∎

  assocʳ∘⊗∘assocˡ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
                  → assocʳ ∘ ((f ⊗ g) ⊗ h) ∘ assocˡ ≈ f ⊗ (g ⊗ h)
  assocʳ∘⊗∘assocˡ {f = f}{g}{h} =
    begin
      assocʳ ∘ ((f ⊗ g) ⊗ h) ∘ assocˡ
    ≈˘⟨ ∘-resp-≈ʳ assocˡ∘⊗ ⟩
      assocʳ ∘ assocˡ ∘ (f ⊗ (g ⊗ h))
    ≈˘⟨ assoc ⟩
      (assocʳ ∘ assocˡ) ∘ (f ⊗ (g ⊗ h))
    ≈⟨ ∘-resp-≈ˡ (assocʳ∘assocˡ) ⟩
      id ∘ (f ⊗ (g ⊗ h))
    ≈⟨ identityˡ ⟩
      f ⊗ (g ⊗ h)
    ∎

  first-first : ∀ {a a′ b c : obj} {f : a ⇨ a′}
              → first {b = c} (first {b = b} f) ≈ assocˡ ∘ first f ∘ assocʳ
  first-first {f = f} =
    begin
      first (first f)
    ≡⟨⟩
      (f ⊗ id) ⊗ id
    ≈˘⟨ assocˡ∘⊗∘assocʳ ⟩
      assocˡ ∘ (f ⊗ (id ⊗ id)) ∘ assocʳ
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ id⊗id)) ⟩
      assocˡ ∘ (f ⊗ id) ∘ assocʳ
    ≡⟨⟩
      assocˡ ∘ first f ∘ assocʳ
    ∎

  second-second : ∀ {a b c c′ : obj} {g : c ⇨ c′}
                → second {a = a} (second {a = b} g) ≈ assocʳ ∘ second g ∘ assocˡ
  second-second {g = g} =
    begin
      second (second g)
    ≡⟨⟩
      id ⊗ (id ⊗ g)
    ≈˘⟨ assocʳ∘⊗∘assocˡ ⟩
      assocʳ ∘ ((id ⊗ id) ⊗ g) ∘ assocˡ
    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ id⊗id)) ⟩
      assocʳ ∘ (id ⊗ g) ∘ assocˡ
    ≡⟨⟩
      assocʳ ∘ second g ∘ assocˡ
    ∎

  ⊗⁻¹ : {f : a ⇨ c}{f⁻¹ : c ⇨ a}{g : b ⇨ d}{g⁻¹ : d ⇨ b}
      → (f⁻¹∘f≈id : f⁻¹ ∘ f ≈ id) (g⁻¹∘g : g⁻¹ ∘ g ≈ id) → (f⁻¹ ⊗ g⁻¹) ∘ (f ⊗ g) ≈ id
  ⊗⁻¹ {f = f}{f⁻¹}{g}{g⁻¹} f⁻¹∘f≈id g⁻¹∘g =
    begin
      (f⁻¹ ⊗ g⁻¹) ∘ (f ⊗ g)
    ≈⟨ ∘⊗ ⟩
      (f⁻¹ ∘ f) ⊗ (g⁻¹ ∘ g)
    ≈⟨ ⊗-resp-≈ f⁻¹∘f≈id g⁻¹∘g ⟩
      id ⊗ id
    ≈⟨ id⊗id ⟩
      id
    ∎

  first⁻¹  : {f : a ⇨ c}{f⁻¹ : c ⇨ a}{b : obj}
           → (f⁻¹∘f : f⁻¹ ∘ f ≈ id) → first  {b = b} f⁻¹ ∘ first  f ≈ id
  first⁻¹  f⁻¹∘f = ⊗⁻¹ f⁻¹∘f identityˡ

  second⁻¹ : {g : b ⇨ d}{g⁻¹ : d ⇨ b}{a : obj}
           → (g⁻¹∘g : g⁻¹ ∘ g ≈ id) → second {a = a} g⁻¹ ∘ second g ≈ id
  second⁻¹ g⁻¹∘g = ⊗⁻¹ identityˡ g⁻¹∘g

  -- -- Experimental:
  -- first⁻¹∘first∘ : {f : a ⇨ c}{f⁻¹ : c ⇨ a}{k : d ⇨ a × e}
  --                → (f⁻¹∘f : f⁻¹ ∘ f ≈ id) → first f⁻¹ ∘ first f ∘ k ≈ k
  -- first⁻¹∘first∘ f⁻¹∘f = g⁻¹∘g∘f (first⁻¹ f⁻¹∘f)

open LawfulMonoidal ⦃ … ⦄ public


-------------------------------------------------------------------------------
-- | Some generally useful categories. Perhaps should go elsewhere.
-------------------------------------------------------------------------------


{-

module _ {obj : Set o} (_⇨_ : obj → obj → Set ℓ) ⦃ cat : Category _⇨_ ⦄ where

  open ⟺ _⇨_
  -- A pair of opposite arrows. See also _≅_ in Laws.
  infix 0 _≅_ 
  record _≅_ (a b : obj) : Set (lsuc o ⊔ ℓ) where
    constructor mk≅
    field
      a⟺b : a ⟺ b
    open _⟺_ a⟺b public
    field
      from∘to : from ∘ to ≈ id
      to∘from : to ∘ from ≈ id

  -- instance
  --   ≅-cat : Category _≅_
  --   ≅-cat = record
  --    { id = mk≅ id id
  --    ; _∘_ = λ { (mk≅ g g⁻¹) (mk≅ f f⁻¹) → mk≅ (g ∘ f) (f⁻¹ ∘ g⁻¹) }
  --    }

-}
