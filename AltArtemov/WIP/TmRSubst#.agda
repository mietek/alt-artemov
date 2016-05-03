module AltArtemov.WIP.TmRSubst# where

open import Data.Nat using (suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation.Core
open import AltArtemov.Term.Representation.Substitution
open import AltArtemov.Variable.Representation
open import Data.Fin.Missing


{-
_∖ᵍ#_ : (g : CxR) → Fin (suc ⌊ g ⌋ᵍ) → CxR
g      ∖ᵍ# zero   = g
∅      ∖ᵍ# suc ()
(g ,◌) ∖ᵍ# suc k  = ((g ,◌) ∖ᵍ top) ∖ᵍ# k


_↦∅ᵍ : (g : CxR) → ∅ ≡ g ∖ᵍ# sup ⌊ g ⌋ᵍ
∅      ↦∅ᵍ = refl
(g ,◌) ↦∅ᵍ = g ↦∅ᵍ


wkⁱ# : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → ◌∈ (g ∖ᵍ# k) → ◌∈ g
wkⁱ# {g}    zero     i = i
wkⁱ# {∅}    (suc ()) i
wkⁱ# {g ,◌} (suc k)  i = wkⁱ top (wkⁱ# k i)


wkⁱ* : ∀ {g} → ◌∈ ∅ → ◌∈ g
wkⁱ* ()


wkᵗ# : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → (g ∖ᵍ# k) ⊢◌ → g ⊢◌
wkᵗ# {g}    zero     t = t
wkᵗ# {∅}    (suc ()) t
wkᵗ# {g ,◌} (suc k)  t = wkᵗ top (wkᵗ# k t)


wkᵗ* : ∀ {g} → ∅ ⊢◌ → g ⊢◌
wkᵗ* {g} rewrite g ↦∅ᵍ = wkᵗ# (sup ⌊ g ⌋ᵍ)
-}


data VarRs (g : CxR) : Set where
  []  : VarRs g
  _∷_ : (i : ◌∈ g) → VarRs (g ∖ᵍ i) → VarRs g


topsᵍ : (g : CxR) → VarRs g
topsᵍ ∅      = []
topsᵍ (g ,◌) = top ∷ topsᵍ g


_∖ᵍ#_ : (g : CxR) → VarRs g → CxR
g ∖ᵍ# []       = g
g ∖ᵍ# (i ∷ is) = (g ∖ᵍ i) ∖ᵍ# is


_↦∅ᵍ : (g : CxR) → ∅ ≡ g ∖ᵍ# topsᵍ g
∅      ↦∅ᵍ = refl
(g ,◌) ↦∅ᵍ = g ↦∅ᵍ


wkⁱ# : ∀ {g} → (is : VarRs g) → ◌∈ (g ∖ᵍ# is) → ◌∈ g
wkⁱ# []       x = x
wkⁱ# (i ∷ is) x = wkⁱ i (wkⁱ# is x)


wkᵗ# : ∀ {g} → (is : VarRs g) → (g ∖ᵍ# is) ⊢◌ → g ⊢◌
wkᵗ# []       t = t
wkᵗ# (i ∷ is) t = wkᵗ i (wkᵗ# is t)


wkᵗ* : ∀ {g} → ∅ ⊢◌ → g ⊢◌
wkᵗ* {g} rewrite g ↦∅ᵍ = wkᵗ# (topsᵍ g)
