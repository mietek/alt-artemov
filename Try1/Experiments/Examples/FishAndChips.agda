module Try1.Experiments.Examples.FishAndChips where

open import Relation.Binary.PropositionalEquality using (refl)

open import Try1.AltArtemov
open import Try1.Experiments.FishAndChips


-- Some theorems of propositional logic.

I : ∀ {A Γ} → Γ ⊢ A ⊃ A
I = fun x ⇒ x {{refl}}

K : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
K = fun x ⇒ fun y ⇒ x {{refl}}

S : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S = fun f ⇒ fun g ⇒ fun x ⇒ app (app (f {{refl}}) (x {{refl}})) (app (g {{refl}}) (x {{refl}}))


-- Some theorems of the λ-calculus.

I² : ∀ {A Γ} → Γ ⊢ LAM V0 ∶ (A ⊃ A)
I² = fun² x ⇒ x {{refl}}

K² : ∀ {A B Γ} → Γ ⊢ LAM (LAM V1) ∶ (A ⊃ B ⊃ A)
K² = fun² x ⇒ fun² y ⇒ x {{refl}}

S² : ∀ {A B C Γ} → Γ ⊢ LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S² = fun² f ⇒ fun² g ⇒ fun² x ⇒ app² (app² (f {{refl}}) (x {{refl}})) (app² (g {{refl}}) (x {{refl}}))


-- Some theorems of third-level logic.

I³ : ∀ {A Γ} → Γ ⊢ LAM² V0² ∶ LAM V0 ∶ (A ⊃ A)
I³ = fun³ x ⇒ x {{refl}}

K³ : ∀ {A B Γ} → Γ ⊢ LAM² (LAM² V1²) ∶ LAM (LAM V1) ∶ (A ⊃ B ⊃ A)
K³ = fun³ x ⇒ fun³ y ⇒ x {{refl}}

S³ : ∀ {A B C Γ} → Γ ⊢ LAM² (LAM² (LAM² (APP² (APP² V2² V0²) (APP² V1² V0²)))) ∶ LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S³ = fun³ f ⇒ fun³ g ⇒ fun³ x ⇒ app³ (app³ (f {{refl}}) (x {{refl}})) (app³ (g {{refl}}) (x {{refl}}))


-- Some first-level realisations of theorems of the modal logic S4.

D : ∀ {f x A B Γ} → Γ ⊢ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B
D = fun f ⇒ fun x ⇒ app² (f {{refl}}) (x {{refl}})

T : ∀ {x A Γ} → Γ ⊢ x ∶ A ⊃ A
T = fun x ⇒ down (x {{refl}})

#4 : ∀ {x A Γ} → Γ ⊢ x ∶ A ⊃ quo x ∶ x ∶ A
#4 = fun x ⇒ up (x {{refl}})


-- Some second-level realisations of theorems of the modal logic S4.

D² : ∀ {f x A B Γ} → Γ ⊢ LAM (LAM (APP² V1 V0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B)
D² = fun² f ⇒ fun² x ⇒ app³ (f {{refl}}) (x {{refl}})

T² : ∀ {x A Γ} → Γ ⊢ LAM (DOWN V0) ∶ (x ∶ A ⊃ A)
T² = fun² x ⇒ down² (x {{refl}})

#4² : ∀ {x A Γ} → Γ ⊢ LAM (UP V0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
#4² = fun² x ⇒ up² (x {{refl}})


-- Some third-level realisations of theorems of the modal logic S4.

D³ : ∀ {f x A B Γ} → Γ ⊢ LAM² (LAM² (APP³ V1² V0²)) ∶ LAM (LAM (APP² V1 V0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B)
D³ = fun³ f ⇒ fun³ x ⇒ app⁴ (f {{refl}}) (x {{refl}})

T³ : ∀ {x A Γ} → Γ ⊢ LAM² (DOWN² V0²) ∶ LAM (DOWN V0) ∶ (x ∶ A ⊃ A)
T³ = fun³ x ⇒ down³ (x {{refl}})

#4³ : ∀ {x A Γ} → Γ ⊢ LAM² (UP² V0²) ∶ LAM (UP V0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
#4³ = fun³ x ⇒ up³ (x {{refl}})
