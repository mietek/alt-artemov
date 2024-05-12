module Try2.Common.Delay.Convergence where

open import Data.Product using (∃)
open import Size using (Size ; Size<_ ; ∞)

open import Try2.Common.Delay.Core
open import Try2.Common.Delay.StrongBisimilarity




data _⇓_ {A} : Delay ∞ A → A → Set where
  ⇓now   : ∀ {a}                                       → now a    ⇓ a
  ⇓later : ∀ {a} {a∞ : ∞Delay ∞ A} (a⇓ : force a∞ ⇓ a) → later a∞ ⇓ a

_⇓ : ∀ {A} → Delay ∞ A → Set
a? ⇓ = ∃ λ a → a? ⇓ a


⇓map : ∀ {A B a} {a? : Delay ∞ A} (f : A → B)
    → a? ⇓ a
    → (f <$> a?) ⇓ f a
⇓map f ⇓now        = ⇓now
⇓map f (⇓later ⇓a) = ⇓later (⇓map f ⇓a)


⇓≈subst : ∀ {A a} {a? a?′ : Delay ∞ A}
    → a? ⇓ a    → a? ≈ a?′
    → a?′ ⇓ a
⇓≈subst ⇓now        (≈now a)   = ⇓now
⇓≈subst (⇓later ⇓a) (≈later p) = ⇓later (⇓≈subst ⇓a (≈force p))


⇓bind : ∀ {A B a b} {a? : Delay ∞ A} {f : A → Delay ∞ B}
    → a? ⇓ a    → f a ⇓ b
    → (a? >>= f) ⇓ b
⇓bind ⇓now        ⇓b = ⇓b
⇓bind (⇓later ⇓a) ⇓b = ⇓later (⇓bind ⇓a ⇓b)
