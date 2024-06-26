{-# OPTIONS --allow-unsolved-metas #-}

module Try2.AltArtemov.WIP.TySubst# where

open import Data.Nat using (suc)
open import Data.Fin using (Fin ; zero ; suc)

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation
open import Try2.AltArtemov.Type.Core
-- open import Try2.AltArtemov.Type.Substitution
open import Try2.AltArtemov.Variable.Representation
open import Try2.Data.Fin.Missing

open import Try2.AltArtemov.WIP.TmRSubst#


wkᴬ# : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → Ty (g ∖ᵍ# k) → Ty g
wkᴬ# {g}    zero     A = A
wkᴬ# {∅}    (suc ()) A
wkᴬ# {g ,◌} (suc k)  A = {!wkᴬ top (wkᴬ# k A)!}


wkᴬ* : ∀ {g} → Ty ∅ → Ty g
wkᴬ* {g} rewrite g ↦∅ᵍ = wkᴬ# (sup ⌊ g ⌋ᵍ)


infixr 15 _∴_

_∴_ : ∀ {g n} → Vec g n → Ty ∅ → Ty g
[]       ∴ A = wkᴬ* A
(t ∷ ts) ∴ A = t ∶ ts ∴ A
