module AltArtemov.Term.Properties where

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ ; zero ; suc ; _⊓_ ; _<′_ ; pred) renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Unit using () renaming (⊤ to Unit)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Term.Core
open import AltArtemov.Term.Inversions
open import Data.Nat.Missing


-- Terms have levels.
lev : ∀ t → ℕ
lev (VAR[ n ] i)   = n
lev (LAM[ n ] t)   = n ⊓ lev t
lev (APP[ n ] t s) = n ⊓ lev t ⊓ lev s
lev (UP[ n ] t)    = n ⊓ lev t
lev (DOWN[ n ] t)  = n ⊓ lev t
lev (BOOM[ n ] t)  = n ⊓ lev t
lev (EQ[ n ] t s)  = n ⊓ lev t ⊓ lev s


-- Terms can be quoted.
quo : ∀ t → Tm
quo (VAR[ n ] i)   = VAR[ suc n ] i
quo (LAM[ n ] t)   = LAM[ suc n ] (quo t)
quo (APP[ n ] t s) = APP[ suc n ] (quo t) (quo s)
quo (UP[ n ] t)    = UP[ suc n ] (quo t)
quo (DOWN[ n ] t)  = DOWN[ suc n ] (quo t)
quo (BOOM[ n ] t)  = BOOM[ suc n ] (quo t)
quo (EQ[ n ] t s)  = EQ[ suc n ] (quo t) (quo s)


-- Quoting a term increments its level.
lev-quo-t≡suc-lev-t : ∀ t → lev (quo t) ≡ suc (lev t)
lev-quo-t≡suc-lev-t (VAR[ n ] i)   = refl
lev-quo-t≡suc-lev-t (LAM[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (APP[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl
lev-quo-t≡suc-lev-t (UP[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (DOWN[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (BOOM[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (EQ[ n ] t s)  rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl


-- The level of a quoted term is greater than 0.
z<′lev-quo-t : ∀ t → zero <′ lev (quo t)
z<′lev-quo-t (VAR[ n ] i)   = z<′sn
z<′lev-quo-t (LAM[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (APP[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn
z<′lev-quo-t (UP[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (DOWN[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (BOOM[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (EQ[ n ] t s)  rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn


-- Terms of level greater than 0 can be unquoted.
unquo : ∀ t (z<′l : zero <′ lev t) → Tm
unquo (VAR[ zero ] i)    ()
unquo (LAM[ zero ] t)    ()
unquo (APP[ zero ] t s)  ()
unquo (UP[ zero ] t)     ()
unquo (DOWN[ zero ] t)   ()
unquo (BOOM[ zero ] t)   ()
unquo (EQ[ zero ] t s)   ()
unquo (VAR[ suc n ] i)   z<′l = VAR[ n ] i
unquo (LAM[ suc n ] t)   z<′l = LAM[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (APP[ suc n ] t s) z<′l = APP[ n ] (unquo t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l))
                                         (unquo s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l))
unquo (UP[ suc n ] t)    z<′l = UP[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (DOWN[ suc n ] t)  z<′l = DOWN[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (BOOM[ suc n ] t)  z<′l = BOOM[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (EQ[ suc n ] t s)  z<′l = EQ[ n ] (unquo t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l))
                                        (unquo s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l))


-- Unquoting a term decrements its level.
lev-unquo-t≡pred-lev-t : ∀ t (z<′l : zero <′ lev t) → lev (unquo t z<′l) ≡ pred (lev t)
lev-unquo-t≡pred-lev-t (VAR[ zero ] i)    ()
lev-unquo-t≡pred-lev-t (LAM[ zero ] t)    ()
lev-unquo-t≡pred-lev-t (APP[ zero ] t s)  ()
lev-unquo-t≡pred-lev-t (UP[ zero ] t)     ()
lev-unquo-t≡pred-lev-t (DOWN[ zero ] t)   ()
lev-unquo-t≡pred-lev-t (BOOM[ zero ] t)   ()
lev-unquo-t≡pred-lev-t (EQ[ zero ] t s)   ()
lev-unquo-t≡pred-lev-t (VAR[ suc n ] i)   z<′l = refl
lev-unquo-t≡pred-lev-t (LAM[ suc n ] t)   z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (APP[ suc n ] t s) z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                                     | lev-unquo-t≡pred-lev-t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = m⊓pn⊓po≡p[sm⊓n⊓o] n (lev t) (lev s)
lev-unquo-t≡pred-lev-t (UP[ suc n ] t)    z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (DOWN[ suc n ] t)  z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (BOOM[ suc n ] t)  z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (EQ[ suc n ] t s)  z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                                     | lev-unquo-t≡pred-lev-t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = m⊓pn⊓po≡p[sm⊓n⊓o] n (lev t) (lev s)


-- Unquoting after quoting is identity.
unquo-quo-t≡t : ∀ t → unquo (quo t) (z<′lev-quo-t t) ≡ t
unquo-quo-t≡t t = aux t (z<′lev-quo-t t)
  where
    aux : ∀ t (z<′l : zero <′ lev (quo t)) → unquo (quo t) z<′l ≡ t    -- TODO: Simplify!
    aux (VAR[ n ] i)   z<′l = refl
    aux (LAM[ n ] t)   z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (APP[ n ] t s) z<′l rewrite aux t (z<′sm⊓n⊓o⇒z<′n (lev (quo s)) z<′l)
                                  | aux s (z<′sm⊓n⊓o⇒z<′o (lev (quo t)) z<′l) = refl
    aux (UP[ n ] t)    z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (DOWN[ n ] t)  z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (BOOM[ n ] t)  z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (EQ[ n ] t s)  z<′l rewrite aux t (z<′sm⊓n⊓o⇒z<′n (lev (quo s)) z<′l)
                                  | aux s (z<′sm⊓n⊓o⇒z<′o (lev (quo t)) z<′l) = refl


-- Quoting after unquoting is identity.
quo-unquo-t≡t : ∀ t (z<′l : zero <′ lev t) → quo (unquo t z<′l) ≡ t
quo-unquo-t≡t (VAR[ zero ] i)    ()
quo-unquo-t≡t (LAM[ zero ] t)    ()
quo-unquo-t≡t (APP[ zero ] t s)  ()
quo-unquo-t≡t (UP[ zero ] t)     ()
quo-unquo-t≡t (DOWN[ zero ] t)   ()
quo-unquo-t≡t (BOOM[ zero ] t)   ()
quo-unquo-t≡t (EQ[ zero ] t s)   ()
quo-unquo-t≡t (VAR[ suc n ] i)   z<′l = refl
quo-unquo-t≡t (LAM[ suc n ] t)   z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (APP[ suc n ] t s) z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                            | quo-unquo-t≡t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = refl
quo-unquo-t≡t (UP[ suc n ] t)    z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (DOWN[ suc n ] t)  z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (BOOM[ suc n ] t)  z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (EQ[ suc n ] t s)  z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                            | quo-unquo-t≡t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = refl


-- Term equality is decidable.
_≟_ : Decidable {A = Tm} _≡_
VAR[ n ] i   ≟ VAR[ n′ ] i′    with n ℕ≟ n′ | i ℕ≟ i′
VAR[ n ] i   ≟ VAR[ .n ] .i    | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ VAR-inv-n)
...                            | _        | no  i≢i′ = no (i≢i′ ∘ VAR-inv-i)
VAR[ _ ] i   ≟ LAM[ _ ] t′     = no λ ()
VAR[ _ ] i   ≟ APP[ _ ] t′ s′  = no λ ()
VAR[ _ ] i   ≟ UP[ _ ] t′      = no λ ()
VAR[ _ ] i   ≟ DOWN[ _ ] t′    = no λ ()
VAR[ _ ] i   ≟ BOOM[ _ ] t′    = no λ ()
VAR[ _ ] i   ≟ EQ[ _ ] t′ s′   = no λ ()
LAM[ _ ] t   ≟ VAR[ _ ] i′     = no λ ()
LAM[ n ] t   ≟ LAM[ n′ ] t′    with n ℕ≟ n′ | t ≟ t′
LAM[ n ] t   ≟ LAM[ .n ] .t    | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ LAM-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ LAM-inv-t)
LAM[ _ ] t   ≟ APP[ _ ] t′ s′  = no λ ()
LAM[ _ ] t   ≟ UP[ _ ] t′      = no λ ()
LAM[ _ ] t   ≟ DOWN[ _ ] t′    = no λ ()
LAM[ _ ] t   ≟ BOOM[ _ ] t′    = no λ ()
LAM[ _ ] i   ≟ EQ[ _ ] t′ s′   = no λ ()
APP[ _ ] t s ≟ VAR[ _ ] i′     = no λ ()
APP[ _ ] t s ≟ LAM[ _ ] t′     = no λ ()
APP[ n ] t s ≟ APP[ n′ ] t′ s′ with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
APP[ n ] t s ≟ APP[ .n ] .t .s | yes refl | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        | _        = no (n≢n′ ∘ APP-inv-n)
...                            | _        | no  t≢t′ | _        = no (t≢t′ ∘ APP-inv-t)
...                            | _        | _        | no  s≢s′ = no (s≢s′ ∘ APP-inv-s)
APP[ _ ] t s ≟ UP[ _ ] t′      = no λ ()
APP[ _ ] t s ≟ DOWN[ _ ] t′    = no λ ()
APP[ _ ] t s ≟ BOOM[ _ ] t′    = no λ ()
APP[ _ ] t s ≟ EQ[ _ ] t′ s′   = no λ ()
UP[ _ ] t    ≟ VAR[ _ ] i′     = no λ ()
UP[ _ ] t    ≟ LAM[ _ ] t′     = no λ ()
UP[ _ ] t    ≟ APP[ _ ] t′ s′  = no λ ()
UP[ n ] t    ≟ UP[ n′ ] t′     with n ℕ≟ n′ | t ≟ t′
UP[ n ] t    ≟ UP[ .n ] .t     | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ UP-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ UP-inv-t)
UP[ _ ] t    ≟ DOWN[ _ ] t′    = no λ ()
UP[ _ ] t    ≟ BOOM[ _ ] t′    = no λ ()
UP[ _ ] t    ≟ EQ[ _ ] t′ s′   = no λ ()
DOWN[ _ ] t  ≟ VAR[ _ ] i′     = no λ ()
DOWN[ _ ] t  ≟ LAM[ _ ] t′     = no λ ()
DOWN[ _ ] t  ≟ APP[ _ ] t′ s′  = no λ ()
DOWN[ _ ] t  ≟ UP[ _ ] t′      = no λ ()
DOWN[ n ] t  ≟ DOWN[ n′ ] t′   with n ℕ≟ n′ | t ≟ t′
DOWN[ n ] t  ≟ DOWN[ .n ] .t   | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ DOWN-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ DOWN-inv-t)
DOWN[ _ ] t  ≟ BOOM[ _ ] t′    = no λ ()
DOWN[ _ ] t  ≟ EQ[ _ ] t′ s′   = no λ ()
BOOM[ _ ] t  ≟ VAR[ _ ] i′     = no λ ()
BOOM[ _ ] t  ≟ LAM[ _ ] t′     = no λ ()
BOOM[ _ ] t  ≟ APP[ _ ] t′ s′  = no λ ()
BOOM[ _ ] t  ≟ UP[ _ ] t′      = no λ ()
BOOM[ _ ] t  ≟ DOWN[ _ ] t′    = no λ ()
BOOM[ n ] t  ≟ BOOM[ n′ ] t′   with n ℕ≟ n′ | t ≟ t′
BOOM[ n ] t  ≟ BOOM[ .n ] .t   | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ BOOM-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ BOOM-inv-t)
BOOM[ _ ] t  ≟ EQ[ _ ] t′ s′   = no λ ()
EQ[ _ ] t s  ≟ VAR[ _ ] i′     = no λ ()
EQ[ _ ] t s  ≟ LAM[ _ ] t′     = no λ ()
EQ[ _ ] t s  ≟ APP[ _ ] t′ s′  = no λ ()
EQ[ _ ] t s  ≟ UP[ _ ] t′      = no λ ()
EQ[ _ ] t s  ≟ DOWN[ _ ] t′    = no λ ()
EQ[ _ ] t s  ≟ BOOM[ _ ] t′    = no λ ()
EQ[ n ] t s  ≟ EQ[ n′ ] t′ s′  with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
EQ[ n ] t s  ≟ EQ[ .n ] .t .s  | yes refl | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        | _        = no (n≢n′ ∘ EQ-inv-n)
...                              | _        | no  t≢t′ | _        = no (t≢t′ ∘ EQ-inv-t)
...                              | _        | _        | no  s≢s′ = no (s≢s′ ∘ EQ-inv-s)


-- TODO

can-unquo : ∀ t → Maybe Tm
can-unquo t with lev t
...           | zero  = nothing
...           | suc n with suc n ℕ≟ lev t
...                   | no  sn≢l = nothing
...                   | yes sn≡l = just (unquo t (subst (λ n → zero <′ n) sn≡l z<′sn))

HighTm : ∀ t → Set
HighTm t with can-unquo t
...      | just t′ = Unit
...      | _       = Empty

unquo′ : ∀ t {Ht : HighTm t} → Tm
unquo′ t {Ht} with can-unquo t
unquo′ t {Ht} | just t′ = t′
unquo′ t {()} | nothing
