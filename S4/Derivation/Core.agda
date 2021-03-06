module S4.Derivation.Core where

open import S4.Context
open import S4.Type


infixr 0 _∙_⊢_

data _∙_⊢_ (Δ Γ : Cx) : ∀ (A : Ty) → Set where
  -- Variable reference.
  var : ∀ {A}
      → (i : Γ ∋ A)
      → Δ ∙ Γ ⊢ A

  -- Lambda abstraction. (⊃I)
  lam : ∀ {A B}
      → (d : Δ ∙ Γ , A ⊢ B)
      → Δ ∙ Γ ⊢ A ⊃ B

  -- Function application. (⊃E)
  app : ∀ {A B}
      → (d : Δ ∙ Γ ⊢ A ⊃ B)    → (c : Δ ∙ Γ ⊢ A)
      → Δ ∙ Γ ⊢ B

  -- Modal variable reference.
  var* : ∀ {A}
      → (i : Δ ∋ A)
      → Δ ∙ Γ ⊢ A

  -- Modality introduction. (□I)
  box : ∀ {A}
      → (d : Δ ∙ ∅ ⊢ A)
      → Δ ∙ Γ ⊢ □ A

  -- Modality elimination. (□E)
  unbox : ∀ {A C}
      → (d : Δ ∙ Γ ⊢ □ A)    → (c : Δ , A ∙ Γ ⊢ C)
      → Δ ∙ Γ ⊢ C


infixr 0 ⊩_

⊩_ : ∀ (A : Ty) → Set
⊩ A = ∀ {{Δ Γ : Cx}} → Δ ∙ Γ ⊢ A


ty : ∀ {Δ Γ A} (d : Δ ∙ Γ ⊢ A) → Ty
ty {A = A} d = A
