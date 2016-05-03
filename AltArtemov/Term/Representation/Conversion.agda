module AltArtemov.Term.Representation.Conversion where

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation.Core
open import AltArtemov.Term.Representation.Substitution
open import AltArtemov.Variable.Representation


data _▷ᵗ_ {g : CxR} : g ⊢◌ → g ⊢◌ → Set where
  ▷ᵗ-refl  : {t : g ⊢◌} → t ▷ᵗ t
  ▷ᵗ-sym   : {t t′ : g ⊢◌} → t ▷ᵗ t′ → t′ ▷ᵗ t
  ▷ᵗ-trans : {t t′ t″ : g ⊢◌} → t ▷ᵗ t′ → t′ ▷ᵗ t″ → t ▷ᵗ t″

  ▷ᵗ-cong-LAM  : ∀ {n} {t t′ : g ,◌ ⊢◌} → t ▷ᵗ t′ → LAM[ n ] t ▷ᵗ LAM[ n ] t′
  ▷ᵗ-cong-APP  : ∀ {n} {t t′ u u′ : g ⊢◌} → t ▷ᵗ t′ → u ▷ᵗ u′ → APP[ n ] t u ▷ᵗ APP[ n ] t′ u′
  ▷ᵗ-cong-PAIR : ∀ {n} {t t′ u u′ : g ⊢◌} → t ▷ᵗ t′ → u ▷ᵗ u′ → PAIR[ n ] t u ▷ᵗ PAIR[ n ] t′ u′
  ▷ᵗ-cong-FST  : ∀ {n} {t t′ : g ⊢◌} → t ▷ᵗ t′ → FST[ n ] t ▷ᵗ FST[ n ] t′
  ▷ᵗ-cong-SND  : ∀ {n} {t t′ : g ⊢◌} → t ▷ᵗ t′ → SND[ n ] t ▷ᵗ SND[ n ] t′
  ▷ᵗ-cong-UP   : ∀ {n} {t t′ : g ⊢◌} → t ▷ᵗ t′ → UP[ n ] t ▷ᵗ UP[ n ] t′
  ▷ᵗ-cong-DOWN : ∀ {n} {t t′ : g ⊢◌} → t ▷ᵗ t′ → DOWN[ n ] t ▷ᵗ DOWN[ n ] t′
  ▷ᵗ-cong-BOOM : ∀ {n} {t t′ : g ⊢◌} → t ▷ᵗ t′ → BOOM[ n ] t ▷ᵗ BOOM[ n ] t′

  ▷ᵗ-conv-LAM  : ∀ {n} {t : g ⊢◌} → LAM[ n ] (APP[ n ] (wkᵗ top t) (VAR[ n ] top)) ▷ᵗ t
  ▷ᵗ-conv-APP  : ∀ {n} {t : g ,◌ ⊢◌} → {u : g ⊢◌} → APP[ n ] (LAM[ n ] t) u ▷ᵗ substᵗ t top u
  ▷ᵗ-conv-PAIR : ∀ {n} {t : g ⊢◌} → PAIR[ n ] (FST[ n ] t) (SND[ n ] t) ▷ᵗ t
  ▷ᵗ-conv-FST  : ∀ {n} {t u : g ⊢◌} → FST[ n ] (PAIR[ n ] t u) ▷ᵗ t
  ▷ᵗ-conv-SND  : ∀ {n} {t u : g ⊢◌} → SND[ n ] (PAIR[ n ] t u) ▷ᵗ u
  ▷ᵗ-conv-UP   : ∀ {n} {t : g ⊢◌} → UP[ n ] (DOWN[ n ] t) ▷ᵗ t
  ▷ᵗ-conv-DOWN : ∀ {n} {t : g ⊢◌} → DOWN[ n ] (UP[ n ] t) ▷ᵗ t
