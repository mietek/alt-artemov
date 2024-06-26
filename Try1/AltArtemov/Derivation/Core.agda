module Try1.AltArtemov.Derivation.Core where

open import Try1.AltArtemov.Context
open import Try1.AltArtemov.Term
open import Try1.AltArtemov.TermVector
open import Try1.AltArtemov.Type


infixr 0 _⊢_

data _⊢_ (Γ : Cx) : ∀ (A : Ty) → Set where
  -- Variable reference.
  var[_] : ∀ n {A}
      → (i : Γ ∋ A)
      → Γ ⊢ VARs[ n ] (ix i) ∶⋯∶ A

  -- Lambda abstraction. (⊃I)
  lam[_] : ∀ n {ts : Tms n} {A B}
      → (d : Γ , A ⊢ ts ∶⋯∶ B)
      → Γ ⊢ LAMs[ n ] ts ∶⋯∶ (A ⊃ B)

  -- Function application. (⊃E)
  app[_] : ∀ n {ts ss : Tms n} {A B}
      → (d : Γ ⊢ ts ∶⋯∶ (A ⊃ B))    → (c : Γ ⊢ ss ∶⋯∶ A)
      → Γ ⊢ APPs[ n ] ts ss ∶⋯∶ B

  -- Product. (∧I)
  pair[_] : ∀ n {ts ss : Tms n} {A B}
      → (d : Γ ⊢ ts ∶⋯∶ A)    → (c : Γ ⊢ ss ∶⋯∶ B)
      → Γ ⊢ PAIRs[ n ] ts ss ∶⋯∶ (A ∧ B)

  -- First projection. (∧E₁)
  fst[_] : ∀ n {ts : Tms n} {A B}
      → (d : Γ ⊢ ts ∶⋯∶ (A ∧ B))
      → Γ ⊢ FSTs[ n ] ts ∶⋯∶ A

  -- Second projection. (∧E₂)
  snd[_] : ∀ n {ts : Tms n} {A B}
      → (d : Γ ⊢ ts ∶⋯∶ (A ∧ B))
      → Γ ⊢ SNDs[ n ] ts ∶⋯∶ B

  -- Reification.
  up[_] : ∀ n {ts : Tms n} {u A}
      → (d : Γ ⊢ ts ∶⋯∶ u ∶ A)
      → Γ ⊢ UPs[ n ] ts ∶⋯∶ quo u ∶ u ∶ A

  -- Reflection.
  down[_] : ∀ n {ts : Tms n} {u A}
      → (d : Γ ⊢ ts ∶⋯∶ u ∶ A)
      → Γ ⊢ DOWNs[ n ] ts ∶⋯∶ A

  -- Explosion. (⊥E)
  boom[_] : ∀ n {ts : Tms n} {A}
      → (d : Γ ⊢ ts ∶⋯∶ ⊥)
      → Γ ⊢ BOOMs[ n ] ts ∶⋯∶ A

  -- Type equality. (≑I)
  eq[_] : ∀ n {ts ss : Tms n} {u A B}
      → (d : Γ ⊢ ts ∶⋯∶ u ∶ A)    → (c : Γ ⊢ ss ∶⋯∶ u ∶ B)
      → Γ ⊢ EQs[ n ] ts ss ∶⋯∶ (A ≑ B)
