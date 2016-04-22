module AltArtemov.Derivation.Properties where

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ ; zero ; suc ; _<′_ ; _⊓_) renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Unit using () renaming (⊤ to Unit)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type
open import Data.Nat.Missing


-- Derivations have types.
ty : ∀ {Γ A} (d : Γ ⊢ A) → Ty
ty {A = A} d = A


-- Derivations of type that is of level greater than 0 have terms.
tm : ∀ {Γ A} (d : Γ ⊢ A) (z<′tl : zero <′ ty-lev A) → Tm
tm d z<′tl = ty-tm (ty d) z<′tl


-- Derivations have levels.
lev : ∀ {Γ A} (d : Γ ⊢ A) → ℕ
lev (var[ n ] i)   = n
lev (lam[ n ] d)   = n ⊓ lev d
lev (app[ n ] d c) = n ⊓ lev d ⊓ lev c
lev (up[ n ] d)    = n ⊓ lev d
lev (down[ n ] d)  = n ⊓ lev d
lev (boom[ n ] d)  = n ⊓ lev d
lev (eq[ n ] d c)  = n ⊓ lev d ⊓ lev c


-- Derivations can be represented as terms.
rep : ∀ {Γ A} (d : Γ ⊢ A) → Tm
rep (var[ n ] i)   = VAR[ n ] (ix i)
rep (lam[ n ] d)   = LAM[ n ] (rep d)
rep (app[ n ] d c) = APP[ n ] (rep d) (rep c)
rep (up[ n ] d)    = UP[ n ] (rep d)
rep (down[ n ] d)  = DOWN[ n ] (rep d)
rep (boom[ n ] d)  = BOOM[ n ] (rep d)
rep (eq[ n ] d c)  = EQ[ n ] (rep d) (rep c)


-- Representing a derivation preserves its level.
tm-lev-rep-d≡lev-d : ∀ {Γ A} (d : Γ ⊢ A) → tm-lev (rep d) ≡ lev d
tm-lev-rep-d≡lev-d (var[ n ] i)   = refl
tm-lev-rep-d≡lev-d (lam[ n ] d)   rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (app[ n ] d c) rewrite tm-lev-rep-d≡lev-d d | tm-lev-rep-d≡lev-d c = refl
tm-lev-rep-d≡lev-d (up[ n ] d)    rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (down[ n ] d)  rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (boom[ n ] d)  rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (eq[ n ] d c)  rewrite tm-lev-rep-d≡lev-d d | tm-lev-rep-d≡lev-d c = refl


-- Derivations can be internalised.
int : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊢ rep d ∶ A
int (var[ n ] i)             = var[ suc n ] i
int (lam[ n ] {ts} d)        = lam[ suc n ] {ts = rep d ∷ ts} (int d)
int (app[ n ] {ts} {ss} d c) = app[ suc n ] {ts = rep d ∷ ts} {ss = rep c ∷ ss} (int d) (int c)
int (up[ n ] {ts} d)         = up[ suc n ] {ts = rep d ∷ ts} (int d)
int (down[ n ] {ts} d)       = down[ suc n ] {ts = rep d ∷ ts} (int d)
int (boom[ n ] {ts} d)       = boom[ suc n ] {ts = rep d ∷ ts} (int d)
int (eq[ n ] {ts} {ss} d c)  = eq[ suc n ] {ts = rep d ∷ ts} {ss = rep c ∷ ss} (int d) (int c)


-- Weakening a context preserves derivations from the context.
weak-dn : ∀ Γ Δ {A} (d : ∅ ++ Γ ⊢ A) → Δ ++ Γ ⊢ A
weak-dn Γ Δ (var[ n ] i)         rewrite sym (ix-weak-cx≡ix Γ i) = var[ n ] (weak-ix Γ Δ i)
weak-dn Γ Δ (lam[ n ] {A = A} d) = lam[ n ] (weak-dn (Γ , A) Δ d)
weak-dn Γ Δ (app[ n ] d c)       = app[ n ] (weak-dn Γ Δ d) (weak-dn Γ Δ c)
weak-dn Γ Δ (up[ n ] d)          = up[ n ] (weak-dn Γ Δ d)
weak-dn Γ Δ (down[ n ] d)        = down[ n ] (weak-dn Γ Δ d)
weak-dn Γ Δ (boom[ n ] d)        = boom[ n ] (weak-dn Γ Δ d)
weak-dn Γ Δ (eq[ n ] d c)        = eq[ n ] (weak-dn Γ Δ d) (weak-dn Γ Δ c)


-- Necessitation is a special case of internalisation.
nec : ∀ {Γ A} (d : ∅ ⊢ A) → Γ ⊢ rep d ∶ A
nec {Γ} d = weak-dn ∅ Γ (int d)


-- Internalising a derivation asserts its type.
ty-int-d≡rep-d∶ty-d : ∀ {Γ A} (d : Γ ⊢ A) → ty (int d) ≡ rep d ∶ A
ty-int-d≡rep-d∶ty-d d = refl


-- Internalising a derivation increments its level.
lev-int-d≡suc-lev-d : ∀ {Γ A} (d : Γ ⊢ A) → lev (int d) ≡ suc (lev d)
lev-int-d≡suc-lev-d (var[ n ] i)   = refl
lev-int-d≡suc-lev-d (lam[ n ] d)   rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (app[ n ] d c) rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = refl
lev-int-d≡suc-lev-d (up[ n ] d)    rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (down[ n ] d)  rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (boom[ n ] d)  rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (eq[ n ] d c)  rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = refl


-- Internalising a derivation increments the level of its type.
ty-lev-int-d≡suc-ty-lev-d : ∀ {Γ A} (d : Γ ⊢ A) → ty-lev (ty (int d)) ≡ suc (ty-lev A)
ty-lev-int-d≡suc-ty-lev-d d = refl


-- The level of an internalised derivation is greater than 0.
z<′lev-int-d : ∀ {Γ A} (d : Γ ⊢ A) → zero <′ lev (int d)
z<′lev-int-d (var[ n ] i)   = z<′sn
z<′lev-int-d (lam[ n ] d)   rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (app[ n ] d c) rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = z<′sn
z<′lev-int-d (up[ n ] d)    rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (down[ n ] d)  rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (boom[ n ] d)  rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (eq[ n ] d c)  rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = z<′sn


-- The level of the type of an internalised derivation is greater than 0.
z<′ty-lev-int-d : ∀ {Γ A} (d : Γ ⊢ A) → zero <′ ty-lev (ty (int d))
z<′ty-lev-int-d d = z<′sn


-- Derivations of level greater than 0, and of type that is of level greater than 0, can be uninternalised.
unint : ∀ {Γ A} (d : Γ ⊢ A) (z<′l : zero <′ lev d) (z<′tl : zero <′ ty-lev A) → Γ ⊢ lower A z<′tl
unint (var[ zero ] i)                      ()   z<′tl
unint (lam[ zero ] d)                      ()   z<′tl
unint (app[ zero ] d c)                    ()   z<′tl
unint (up[ zero ] d)                       ()   z<′tl
unint (down[ zero ] d)                     ()   z<′tl
unint (boom[ zero ] d)                     ()   z<′tl
unint (eq[ zero ] d c)                     ()   z<′tl
unint (var[ suc n ] i)                     z<′l z<′tl = var[ n ] i
unint (lam[ suc n ] {t ∷ ts} d)            z<′l z<′tl = lam[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (app[ suc n ] {t ∷ ts} {s ∷ ss} d c) z<′l z<′tl = app[ n ] (unint d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l) z<′sn)
                                                                 (unint c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l) z<′sn)
unint (up[ suc n ] {t ∷ ts} d)             z<′l z<′tl = up[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (down[ suc n ] {t ∷ ts} d)           z<′l z<′tl = down[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (boom[ suc n ] {t ∷ ts} d)           z<′l z<′tl = boom[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (eq[ suc n ] {t ∷ ts} {s ∷ ss} d c)  z<′l z<′tl = eq[ n ] (unint d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l) z<′sn)
                                                                (unint c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l) z<′sn)


-- Unnecessitation is a special case of uninternalisation.
unnec : ∀ {A} (d : ∅ ⊢ A) (z<′l : zero <′ lev d) (z<′tl : zero <′ ty-lev A) → ∅ ⊢ lower A z<′tl
unnec = unint


-- TODO

unint2 : ∀ {Γ A} (d : Γ ⊢ A) (z<′l : zero <′ lev d) {HA : HighTy A} → Γ ⊢ lower′ A {HA}
unint2 (var[ zero ] i)                      ()
unint2 (lam[ zero ] d)                      ()
unint2 (app[ zero ] d c)                    ()
unint2 (up[ zero ] d)                       ()
unint2 (down[ zero ] d)                     ()
unint2 (boom[ zero ] d)                     ()
unint2 (eq[ zero ] d c)                     ()
unint2 (var[ suc n ] i)                     z<′l = var[ n ] i
unint2 (lam[ suc n ] {t ∷ ts} d)            z<′l = lam[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (app[ suc n ] {t ∷ ts} {s ∷ ss} d c) z<′l = app[ n ] (unint2 d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l))
                                                            (unint2 c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l))
unint2 (up[ suc n ] {t ∷ ts} d)             z<′l = up[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (down[ suc n ] {t ∷ ts} d)           z<′l = down[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (boom[ suc n ] {t ∷ ts} d)           z<′l = boom[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (eq[ suc n ] {t ∷ ts} {s ∷ ss} d c)  z<′l = eq[ n ] (unint2 d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l))
                                                           (unint2 c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l))


can-unint : ∀ {Γ A} (d : Γ ⊢ A) {HA : HighTy A} → Maybe (Γ ⊢ lower′ A {HA})
can-unint d with lev d
...           | zero  = nothing
...           | suc n with suc n ℕ≟ lev d
...                   | no  sn≢l = nothing
...                   | yes sn≡l = just (unint2 d (subst (λ n → zero <′ n) sn≡l z<′sn))

HighDn : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} → Set
HighDn d {HA} with can-unint d {HA}
...         | just d′ = Unit
...         | _       = Empty

unint′ : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} {Hd : HighDn d {HA}} → ∅ ⊢ lower′ A {HA}
unint′ d {HA} {Hd} with can-unint d {HA}
unint′ d {HA} {Hd} | just d′ = d′
unint′ d {HA} {()} | nothing

unnec′ : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} {Hd : HighDn d {HA}} → ∅ ⊢ lower′ A {HA}
unnec′ = unint′
