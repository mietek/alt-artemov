module AltArtemov.Term.Notation.Level4 where

open import AltArtemov.Term.Core


VAR⁴ : ∀ i → Tm
VAR⁴ i₄ = VAR[ 3 ] i₄

LAM⁴ : ∀ t₄ → Tm
LAM⁴ t₄ = LAM[ 3 ] t₄

APP⁴ : ∀ t₄ s₄ → Tm
APP⁴ t₄ s₄ = APP[ 3 ] t₄ s₄

UP⁴ : ∀ t₄ → Tm
UP⁴ t₄ = UP[ 3 ] t₄

DOWN⁴ : ∀ t₄ → Tm
DOWN⁴ t₄ = DOWN[ 3 ] t₄

BOOM⁴ : ∀ t₄ → Tm
BOOM⁴ t₄ = BOOM[ 3 ] t₄

EQ⁴ : ∀ t₄ s₄ → Tm
EQ⁴ t₄ s₄ = EQ[ 3 ] t₄ s₄


V0⁴ : Tm
V0⁴ = VAR⁴ 0

V1⁴ : Tm
V1⁴ = VAR⁴ 1

V2⁴ : Tm
V2⁴ = VAR⁴ 2

V3⁴ : Tm
V3⁴ = VAR⁴ 3

V4⁴ : Tm
V4⁴ = VAR⁴ 4

V5⁴ : Tm
V5⁴ = VAR⁴ 5

V6⁴ : Tm
V6⁴ = VAR⁴ 6

V7⁴ : Tm
V7⁴ = VAR⁴ 7

V8⁴ : Tm
V8⁴ = VAR⁴ 8

V9⁴ : Tm
V9⁴ = VAR⁴ 9
