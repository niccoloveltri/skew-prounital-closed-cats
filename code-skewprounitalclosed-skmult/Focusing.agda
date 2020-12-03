{-# OPTIONS --rewriting #-}

open import SkMults

module Focusing where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.Unit
open import Data.List
open import Data.Product hiding (uncurry;curry)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae
open import FreeSkewProunitalClosed
open import SeqCalcVar

-- =======================================================================

-- focused sequent calculus

mutual
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
    switch :  {S : Stp} → 
              {Γ : Cxt} → {C : Fma} →
              (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → S ∣ Γ ⊢L C

  data _∣_⊢R_ : Stp → Cxt → Fma → Set where
    base : ∀ {T S Γ Δ Y} → T ∣ Γ ⊢b Y
      → S ≡ mmap ` T → Δ ≡ lmap ` Γ
      → S ∣ Δ ⊢R ` Y
    ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) → (g : just B ∣ Δ ⊢R C) →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢R C
    ⊸c : ∀ {T S} (Δ₀ : Cxt) {Ψ Γ Δ₁ A B C}
      → S ≡ mmap ` T → Δ₀ ≡ lmap ` Ψ
      → nothing ∣ Γ ⊢L A → S ∣ Δ₀ ++ B ∷ Δ₁ ⊢R C
      → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢R C

-- ====================================================================

-- embedding focused derivations into general derivations

mutual
  embL : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢L A → S ∣ Γ ⊢V A
  embL (⊸r f) = ⊸r (embL f)
  embL (switch q f) = embR f

  embR : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢R A → S ∣ Γ ⊢V A
  embR (base f eq1 eq2) = base f eq1 eq2
  embR (⊸l f g) = ⊸l (embL f) (embR g)
  embR (⊸c Δ₀ eq1 eq2 f g) = ⊸c Δ₀ (embL f) (embR g)

-- ====================================================================

-- admissibility of unrestricted ⊸l

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (switch p g) = switch p (⊸l f g)

-- admissibility of unrestricted base

base-focus : ∀ {T S Γ Δ Y} → T ∣ Γ ⊢b Y
  → S ≡ mmap ` T → Δ ≡ lmap ` Γ
  → S ∣ Δ ⊢L ` Y
base-focus f eq1 eq2 = switch tt (base f eq1 eq2)

-- admissibility of unrestricted ⊸c

⊸c-focusR' : ∀ {S} (Δ₀ : Cxt) {Δ Γ Δ₁ A B C}
  → nothing ∣ Γ ⊢L A → S ∣ Δ ⊢R C
  → Δ ≡ Δ₀ ++ B ∷ Δ₁
  → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢R C
⊸c-focus' : ∀ {S} (Δ₀ : Cxt) {Δ Γ Δ₁ A B C}
  → nothing ∣ Γ ⊢L A → S ∣ Δ ⊢L C
  → Δ ≡ Δ₀ ++ B ∷ Δ₁
  → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢L C

⊸c-focusR' Δ₀ {Δ₁ = Δ₁} f (base {T} {Γ = Γ} g eq1 eq2) eq
  with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Γ (trans (sym eq) eq2)
... | (Ψ₀ , Ψ₁ , eq3 , eq4 , eq5) = 
  ⊸c {T} Δ₀ {Ψ₀} eq1 eq3 f (base g eq1 (trans (sym eq) eq2))
⊸c-focusR' Δ₀ {Δ₁ = Δ₁} f (⊸l {Γ} {Δ} g h) eq
  with cases++ Δ₀ Γ Δ₁ Δ eq
... | inj₁ (Γ₀ , refl , refl) = ⊸l (⊸c-focus' Δ₀ f g refl) h
... | inj₂ (Γ₀ , refl , refl) = ⊸l g (⊸c-focusR' Γ₀ f h refl)
⊸c-focusR' Δ₀ {Δ₁ = Δ₂} f (⊸c {T} Δ₁ {Ψ} {Γ = Γ} {Δ₃} eq1 eq2 g h) eq
  with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (_ ∷ Δ₂) (sym eq)
... | inj₁ (Γ₀ , refl , r) with cases++ Γ₀ Γ Δ₂ Δ₃ r
... | inj₁ (Γ₀' , refl , refl) =
  ⊸c {T} Δ₁ {Ψ} eq1 eq2 (⊸c-focus' Γ₀ f g refl) h
... | inj₂ (Γ₀' , refl , refl) =
  ⊸c {T} Δ₁ {Ψ} eq1 eq2 g (⊸c-focusR' (Δ₁ ++ _ ∷ Γ₀') f h refl)
⊸c-focusR' Δ₀ {Δ₁ = .(Γ ++ Δ₃)} f (⊸c {T} .(Δ₀ ++ []) {Ψ} {Γ = Γ} {Δ₃} eq1 eq2 g h) eq | inj₂ ([] , refl , refl) =
  ⊸c {T} Δ₀ {Ψ} eq1 eq2 f (⊸c {T} Δ₀ {Ψ} eq1 eq2 g h)
⊸c-focusR' Δ₀ {Δ₁ = .(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} f (⊸c {T} .(Δ₀ ++ X ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₃} eq1 eq2 g h) eq | inj₂ (X ∷ Γ₀ , refl , refl)
  with cases++-lmap ` Δ₀ (_ ∷ Γ₀) Ψ eq2
... | (Ψ₀ , ._ ∷ Ψ₁ , refl , refl , eq5) =
  ⊸c {T} Δ₀ {Ψ₀} eq1 refl f (⊸c {T} (Δ₀ ++ _ ∷ lmap ` Ψ₁) {Ψ₀ ++ _ ∷ Ψ₁} eq1 refl g h)

⊸c-focus' Δ₀ f (⊸r g) refl = ⊸r (⊸c-focus' Δ₀ f g refl)
⊸c-focus' Δ₀ {Δ₁ = Δ₁} f (switch q g) eq =
  switch q (⊸c-focusR' Δ₀ f g eq)

⊸c-focus : ∀ {S} (Δ₀ : Cxt) {Γ Δ₁ A B C}
  → nothing ∣ Γ ⊢L A → S ∣ Δ₀ ++ B ∷ Δ₁ ⊢L C
  → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢L C
⊸c-focus Δ₀ f g = ⊸c-focus' Δ₀ f g refl

inj-lmap` : ∀ Γ Δ → lmap ` Γ ≡ lmap ` Δ → Γ ≡ Δ
inj-lmap` [] [] eq = refl
inj-lmap` (x ∷ Γ) (x₁ ∷ Δ) eq with inj∷ eq
... | refl , q = cong (x ∷_) (inj-lmap` Γ Δ q)

⊸c-focusR'-eq : ∀ {T S} (Δ₀ : Cxt) {Ψ Δ Γ Δ₁ A B C}
  → (eq1 : S ≡ mmap ` T) (eq2 : Δ₀ ≡ lmap ` Ψ)
  → (f : nothing ∣ Γ ⊢L A) (g : S ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁)
  → ⊸c-focusR' Δ₀ f g eq
    ≡ ⊸c {T} Δ₀ {Ψ} eq1 eq2 f (subst (λ a → S ∣ a ⊢R C) eq g)
⊸c-focusR'-eq {nothing} Δ₀ () eq2 f (⊸l f₁ g) eq
⊸c-focusR'-eq {just x} Δ₀ () eq2 f (⊸l f₁ g) eq
⊸c-focusR'-eq Δ₀ {Ψ} {Δ₁ = Δ₂} eq1 eq2 f (⊸c Δ₁ {Γ = Γ} {Δ₃} eq3 eq4 g h) eq
  with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (_ ∷ Δ₂) (sym eq)
... | inj₁ (Γ₀ , refl , q) with cases++-lmap ` Δ₁ (_ ∷ Γ₀) Ψ eq2
... | Ψ₀ , X ∷ Ψ₁ , p , () , r
⊸c-focusR'-eq {nothing} ._ {Ψ}{Δ₁ = .(Γ ++ Δ₃)} refl refl f (⊸c {nothing} ._ {Ψ'} {Γ = Γ} {Δ₃} refl eq4 g h) refl | inj₂ ([] , refl , refl) with inj-lmap` Ψ Ψ' eq4
⊸c-focusR'-eq {nothing} .(lmap ` Ψ) {Ψ} {Γ = _} {.(Γ ++ Δ₃)} refl refl f (⊸c {nothing} .(lmap ` Ψ ++ []) {.Ψ} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ ([] , refl , refl) | refl = refl
⊸c-focusR'-eq {just x} ._ {Ψ} {Δ₁ = .(Γ ++ Δ₃)} refl refl f (⊸c {just .x} ._ {Ψ'} {Γ = Γ} {Δ₃} refl eq4 g h) refl | inj₂ ([] , refl , refl) with inj-lmap` Ψ Ψ' eq4
⊸c-focusR'-eq {just x} .(lmap ` Ψ) {Ψ} {Γ = _} {.(Γ ++ Δ₃)} refl refl f (⊸c {just .x} .(lmap ` Ψ ++ []) {.Ψ} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ ([] , refl , refl) | refl = refl
⊸c-focusR'-eq Δ₀ {Δ₁ = .(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} eq1 eq2 f (⊸c .(Δ₀ ++ X ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₃} eq3 eq4 g h) refl | inj₂ (X ∷ Γ₀ , refl , refl)
  with cases++-lmap ` Δ₀ (X ∷ Γ₀) Ψ eq4
⊸c-focusR'-eq {nothing} .(lmap ` Ψ₀) {Ψ} {Γ = _} {.(lmap ` Ψ₁ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} refl eq2 f (⊸c {nothing} .(lmap ` Ψ₀ ++ ` _ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ _ ∷ Ψ₁)} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ (.(` _) ∷ .(lmap ` Ψ₁) , refl , refl) | Ψ₀ , _ ∷ Ψ₁ , refl , refl , refl with inj-lmap` Ψ₀ Ψ eq2
⊸c-focusR'-eq {nothing} .(lmap ` Ψ₀) {.Ψ₀} {Γ = _} {.(lmap ` Ψ₁ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} refl refl f (⊸c {nothing} .(lmap ` Ψ₀ ++ ` _ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ _ ∷ Ψ₁)} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ (.(` _) ∷ .(lmap ` Ψ₁) , refl , refl) | Ψ₀ , _ ∷ Ψ₁ , refl , refl , refl | refl = refl
⊸c-focusR'-eq {just x} .(lmap ` Ψ₀) {Ψ} {Γ = _} {.(lmap ` Ψ₁ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} refl eq2 f (⊸c {just .x} .(lmap ` Ψ₀ ++ ` _ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ _ ∷ Ψ₁)} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ (.(` _) ∷ .(lmap ` Ψ₁) , refl , refl) | Ψ₀ , _ ∷ Ψ₁ , refl , refl , refl  with inj-lmap` Ψ₀ Ψ eq2
⊸c-focusR'-eq {just x} .(lmap ` Ψ₀) {.Ψ₀} {Γ = _} {.(lmap ` Ψ₁ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} refl refl f (⊸c {just .x} .(lmap ` Ψ₀ ++ ` _ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ _ ∷ Ψ₁)} {Γ = Γ} {Δ₃} refl refl g h) refl | inj₂ (.(` _) ∷ .(lmap ` Ψ₁) , refl , refl) | Ψ₀ , _ ∷ Ψ₁ , refl , refl , refl | refl = refl
⊸c-focusR'-eq {nothing} Δ₀ {Ψ} {Δ₁ = Δ₁} refl refl f (base {nothing} {Γ = Γ} g refl eq4) refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Γ eq4
... | (Ψ₀ , Ψ₁ , p , q , r) with inj-lmap` Ψ Ψ₀ p
⊸c-focusR'-eq {nothing} .(lmap ` Ψ) {Ψ} {Δ₁ = Δ₁} {B = _} {` _} refl refl f (base {nothing} {Γ = Γ} g refl eq4) refl | Ψ , Ψ₁ , refl , q , r | refl = refl
⊸c-focusR'-eq {just X} Δ₀ {Ψ} {Δ₁ = Δ₁} refl refl f (base {just .X} {Γ = Γ} g refl eq4) refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Γ eq4
... | (Ψ₀ , Ψ₁ , p , q , r) with inj-lmap` Ψ Ψ₀ p
⊸c-focusR'-eq {just X} .(lmap ` Ψ) {Ψ} {Δ₁ = Δ₁} {B = _} {` _} refl refl f (base {just .X} {Γ = Γ} g refl eq4) refl | Ψ , Ψ₁ , refl , q , r | refl = refl

-- the focusing function itself

focus : ∀{S}{Γ}{A} → S ∣ Γ ⊢V A → S ∣ Γ ⊢L A
focus (base f eq1 eq2) = base-focus f eq1 eq2
focus (⊸r f) = ⊸r (focus f)
focus (⊸l f g) = ⊸l-focus (focus f) (focus g)
focus (⊸c Δ₀ f g) = ⊸c-focus Δ₀ (focus f) (focus g)

-- focus sends ≗V-related derivations to the equal focused derivations

⊸c⊸l-focus' : ∀ {Γ Δ Δ' Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢L A} {f' : nothing ∣ Γ' ⊢L A'} (g : just B ∣ Δ' ⊢L C)
    → (eq : Δ' ≡ Δ ++ B' ∷ Λ)
    → ⊸c-focus' (Γ ++ Δ) f' (⊸l-focus f g) (cong (Γ ++_) eq)
                ≡ ⊸l-focus f (⊸c-focus' Δ f' g eq)
⊸c⊸l-focus' (⊸r g) refl = cong ⊸r (⊸c⊸l-focus' g refl)
⊸c⊸l-focus' {Γ} {Δ} {Λ = Λ} {B' = B'} (switch q g) refl
  rewrite cases++-inj₂ Δ Γ Λ B' = refl

⊸c⊸l2-focus : {Γ Δ Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ ++ B' ∷ Λ ⊢L A} {f' : nothing ∣ Γ'  ⊢L A'} (g : just B ∣ Γ ⊢L C)
    → ⊸c-focus Δ f' (⊸l-focus f g) ≡ ⊸l-focus (⊸c-focus Δ f' f) g
⊸c⊸l2-focus (⊸r g) = cong ⊸r (⊸c⊸l2-focus g)
⊸c⊸l2-focus {Γ} {Δ} {Λ = Λ} {B' = B'} (switch q f)
  rewrite cases++-inj₁ Δ Λ Γ B' = refl

⊸c⊸c-focus' : {S : Stp} {Δ Γ Γ' Δ₀ Δ₁ Δ₂ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢L A} {f' : nothing ∣ Γ' ⊢L A'} (g : S ∣ Δ ⊢L C)
    → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂)
    → ⊸c-focus (Δ₀ ++ _ ∷ Γ ++ Δ₁) f' (⊸c-focus' Δ₀ f g eq)
        ≡ ⊸c-focus Δ₀ f (⊸c-focus' (Δ₀ ++ B ∷ Δ₁) f' g eq)
⊸c⊸c-focusR' : {S : Stp} {Δ Γ Γ' Δ₀ Δ₁ Δ₂ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢L A} {f' : nothing ∣ Γ' ⊢L A'} (g : S ∣ Δ ⊢R C)
    → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂)
    → ⊸c-focusR' (Δ₀ ++ _ ∷ Γ ++ Δ₁) f' (⊸c-focusR' Δ₀ f g eq) refl
        ≡ ⊸c-focusR' Δ₀ f (⊸c-focusR' (Δ₀ ++ B ∷ Δ₁) f' g eq) refl

⊸c⊸c-focus' (⊸r g) refl = cong ⊸r (⊸c⊸c-focus' g refl)
⊸c⊸c-focus' (switch q f) refl =
  cong (switch q) (⊸c⊸c-focusR' f refl)

⊸c⊸c-focusR' {Γ = Γ} {Γ'} {Δ₀ = Δ₀} {Δ₁} {Δ₂} {A} {B} {A'} {B'} (base {Γ = Γ₁} g eq1 eq2) refl  with cases++-lmap ` (Δ₀ ++ B ∷ Δ₁) (B' ∷ Δ₂) Γ₁ eq2
... | (Ψ₀ , Ψ₁ , p , q , r)  with cases++-lmap ` Δ₀ (B ∷ Δ₁) Ψ₀ p
⊸c⊸c-focusR' {Γ = Γ} {Γ'} {Δ₀ = .(lmap ` Ψ₀')} {.(lmap ` Ψ₁')} {.(lmap ` Ψ₁)} {A} {.(` x₁)} {A'} {.(` x)} {` _} (base {Γ = .((Ψ₀' ++ x₁ ∷ Ψ₁') ++ x ∷ Ψ₁)} g eq1 refl) refl | .(Ψ₀' ++ x₁ ∷ Ψ₁') , x ∷ Ψ₁ , refl , refl , refl | Ψ₀' , x₁ ∷ Ψ₁' , refl , refl , refl
  rewrite cases++-lmap-refl ` Ψ₀' (x₁ ∷ Ψ₁' ++ x ∷ Ψ₁)
        | cases++-inj₁ (lmap ` Ψ₀') (Γ ++ lmap ` Ψ₁') (` x ∷ lmap ` Ψ₁) (A ⊸ ` x₁) | cases++-inj₂ (` x₁ ∷ lmap ` Ψ₁') (lmap ` Ψ₀') (Γ' ++ lmap ` Ψ₁) (A' ⊸ ` x)
        | cases++-inj₂ (lmap ` Ψ₁') Γ (lmap ` Ψ₁) (` x) | cases++-lmap-refl ` Ψ₀' (x₁ ∷ Ψ₁') | cases++-lmap-refl ` (Ψ₀' ++ x₁ ∷ Ψ₁') (x ∷ Ψ₁) = refl
⊸c⊸c-focusR' {Δ₀ = Δ₀} {Δ₁} {Δ₂} {B = B} {B' = B'} (⊸l {Γ}{Δ} g g') eq with cases++ Δ₀ Γ (Δ₁ ++ B' ∷ Δ₂) Δ eq
⊸c⊸c-focusR' {just (_ ⊸ _)} {Γ = Γ₁} {Γ' = Γ'} {Δ₀ = .(Γ ++ Γ₀)} {Δ₁} {Δ₂} {A} {B = B} {A'} {B' = B'} (⊸l {Γ} {.(Γ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂)} g g') refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ A ⊸ B ∷ Γ₁ ++ Δ₁) Γ Δ₂ B' | cases++-inj₂ (Γ₀ ++ B ∷ Δ₁) Γ Δ₂ B'
        | cases++-inj₂ Γ₀ Γ (Δ₁ ++ A' ⊸ B' ∷ Γ' ++ Δ₂) B
        = cong (⊸l {Δ = Γ₀ ++ _ ∷ Γ₁ ++ Δ₁ ++ _ ∷ Γ' ++ Δ₂} g) (⊸c⊸c-focusR' g' refl)
... | inj₁ (Γ₀ , refl , q) with cases++ Δ₁ Γ₀ Δ₂ Δ (sym q)
⊸c⊸c-focusR' {just (_ ⊸ _)} {Γ = Γ}{Γ'} {Δ₀ = Δ₀} {Δ₁} {.(Γ₀' ++ Δ)} {A} {B = B} {A'} {B' = B'} (⊸l {.(Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Γ₀')} {Δ} g g') refl | inj₁ (.(Δ₁ ++ B' ∷ Γ₀') , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ (Δ₀ ++ B ∷ Δ₁) Γ₀' Δ B' | cases++-inj₂ Δ₀  (Δ₁ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') Δ B
        | cases++-inj₁ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) Γ₀' Δ B' | cases++-inj₁ Δ₀ (Δ₁ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') Δ B
        = cong₂ (⊸l {Γ = Δ₀ ++ _ ∷ Γ ++ Δ₁ ++ _ ∷ Γ' ++ Γ₀'}{Δ}) (⊸c⊸c-focus' g refl) refl
⊸c⊸c-focusR' {just (_ ⊸ _)} {Γ = Γ} {Γ'} {Δ₀ = Δ₀} {.(Γ₀ ++ Γ₀')} {Δ₂} {A} {B = B} {A'} {B' = B'} (⊸l {.(Δ₀ ++ B ∷ Γ₀)} {.(Γ₀' ++ B' ∷ Δ₂)} g g') refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' (Δ₀ ++ A ⊸ B ∷ Γ ++ Γ₀) Δ₂ B' | cases++-inj₂ Γ₀' (Δ₀ ++ B ∷ Γ₀) Δ₂ B'
        | cases++-inj₁ Δ₀ Γ₀ (Γ₀' ++ A' ⊸ B' ∷ Γ' ++ Δ₂) B  = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c Δ₀ {Γ = Γ} {Δ₄} eq1 eq2 g g') eq with cases++ Δ₀ Δ₁ (Γ ++ Δ₄) (B ∷ Δ₂ ++ B' ∷ Δ₃) (sym eq)
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c {T} .(Δ₁ ++ []) {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') eq | inj₂ ([] , p , refl) with inj∷ p
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {_} {Δ₂} {Δ₃} {A} {.(A₁ ⊸ B₁)} {A'} {B'} (⊸c {T} _ {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') eq | inj₂ ([] , p , refl) | refl , q with cases++ Δ₂ Γ Δ₃ Δ₄ (sym q)
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₁} {Δ₂} {.(Γ₀ ++ Δ₄)} {A} {.(A₁ ⊸ B₁)} {A'} {B'} (⊸c {T} .Δ₁ {Ψ} {Γ = .(Δ₂ ++ B' ∷ Γ₀)} {Δ₄} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ ([] , refl , refl) | refl , refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ₁ ++ Δ₂) (B' ∷ Γ₀ ++ Δ₄) (A ⊸ (A₁ ⊸ B₁)) | cases++-inj₂ Δ₂ Γ₁ (Γ₀ ++ Δ₄) B' | cases++-inj₁ Δ₁ Δ₂ (B' ∷ Γ₀ ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₁ Δ₂ Γ₀ Δ₄ B'
        | cases++-inj₂ [] Δ₁ (Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀ ++ Δ₄) (A₁ ⊸ B₁) = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₁} {.(Γ ++ Γ₀)} {Δ₃} {A} {.(A₁ ⊸ B₁)} {A'} {B'} (⊸c {T} .Δ₁ {Ψ} {Γ = Γ} {.(Γ₀ ++ B' ∷ Δ₃)} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ ([] , refl , refl) | refl , refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ₁ ++ Γ ++ Γ₀) (B' ∷ Δ₃) (A ⊸ (A₁ ⊸ B₁)) | cases++-inj₂ (Γ ++ Γ₀) Γ₁ Δ₃ B' | cases++-inj₁ Δ₁ (Γ ++ Γ₀) (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ Γ₀ Γ Δ₃ B'
        | cases++-inj₂ [] Δ₁ (Γ ++ Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B₁) = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c {T} .(Δ₁ ++ x ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') eq | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c {T} .(Δ₁ ++ x ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') eq | inj₂ (x ∷ Γ₀ , p , refl) | (p'' , q) with cases++ Γ₀ Δ₂ (Γ ++ Δ₄) (_ ∷ Δ₃) q
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {.(Γ₀ ++ A₁ ⊸ B₁ ∷ Γ₀')} {Δ₃} {A} {x} {A'} {B'} (⊸c {T} .(Δ₁ ++ x ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') eq | inj₂ (x ∷ Γ₀ , p , refl) | refl , q | inj₁ (Γ₀' , refl , q') with cases++ Γ₀' Γ Δ₃ Δ₄ q'
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {.(Γ₀ ++ A₁ ⊸ B₁ ∷ Γ₀')} {.(Γ₀'' ++ Δ₄)} {A} {x} {A'} {B'} (⊸c {T} .(Δ₁ ++ x ∷ Γ₀) {Ψ} {Γ = .(Γ₀' ++ B' ∷ Γ₀'')} {Δ₄} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ (x ∷ Γ₀ , refl , refl) | refl , refl | inj₁ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) with cases++-lmap ` Δ₁ (x ∷ Γ₀) Ψ eq2
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = .(lmap ` Ψ₀)} {.(lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ₀')} {.(Γ₀'' ++ Δ₄)} {A} {.(` x₁)} {A'} {B'} (⊸c {T} .(lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ x₁ ∷ Ψ₁)} {.(Γ₀' ++ B' ∷ Γ₀'')} {Δ₄} {A₁} {B₁} eq1 refl g g') refl | inj₂ (.(` x₁) ∷ .(lmap ` Ψ₁) , refl , refl) | refl , refl | inj₁ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) | Ψ₀ , x₁ ∷ Ψ₁ , refl , refl , refl
 rewrite cases++-inj₁ (lmap ` Ψ₀) (Γ₁ ++ lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ₀') (B' ∷ Γ₀'' ++ Δ₄) (A ⊸ ` x₁) | cases++-inj₁ (lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) Γ₀' (B' ∷ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁)
       | cases++-inj₂ (lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ₀') Γ₁ (Γ₀'' ++ Δ₄) B' | cases++-inj₁ Γ₀' Γ₀'' Δ₄ B'
       | cases++-inj₁ (lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) Γ₀' (B' ∷ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₂ (` x₁ ∷ lmap ` Ψ₁) (lmap ` Ψ₀) (Γ₀' ++ A' ⊸ B' ∷ Γ' ++ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁)
       | cases++-inj₁ Γ₀' Γ₀'' Δ₄ B' | cases++-lmap-refl ` Ψ₀ (x₁ ∷ Ψ₁) = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {.(Γ₀ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀'')} {Δ₃} {A} {x} {A'} {B'} (⊸c {T} .(Δ₁ ++ x ∷ Γ₀) {Ψ} {Γ = Γ} {.(Γ₀'' ++ B' ∷ Δ₃)} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ (x ∷ Γ₀ , refl , refl) | refl , refl | inj₁ (.(Γ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) with cases++-lmap ` Δ₁ (x ∷ Γ₀) Ψ eq2
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = .(lmap ` Ψ₀)} {.(lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀'')} {Δ₃} {A} {.(` x)} {A'} {B'} (⊸c {T} .(lmap ` Ψ₀ ++ ` x ∷ lmap ` Ψ₁) {.(Ψ₀ ++ x ∷ Ψ₁)} {Γ = Γ} {.(Γ₀'' ++ B' ∷ Δ₃)} {A₁} {B₁} eq1 refl g g') refl | inj₂ (.(` x) ∷ .(lmap ` Ψ₁) , refl , refl) | refl , refl | inj₁ (.(Γ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) | Ψ₀ , x ∷ Ψ₁ , refl , refl , refl
  rewrite cases++-inj₁  (lmap ` Ψ₀) (Γ₁ ++ lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀'') (B' ∷ Δ₃) (A ⊸ ` x) | cases++-inj₁ (lmap ` Ψ₀ ++ ` x ∷ lmap ` Ψ₁) (Γ ++ Γ₀'') (B' ∷ Δ₃) (A₁ ⊸ B₁)
        | cases++-inj₂ (lmap ` Ψ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀'') Γ₁ Δ₃ B' | cases++-inj₂ Γ₀'' Γ Δ₃ B'
        | cases++-inj₁ (lmap ` Ψ₀ ++ ` x ∷ lmap ` Ψ₁) (Γ ++ Γ₀'') (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ (` x ∷ lmap ` Ψ₁) (lmap ` Ψ₀) (Γ ++ Γ₀'' ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B₁)
        | cases++-inj₂ Γ₀''  Γ Δ₃ B' | cases++-lmap-refl ` Ψ₀ (x ∷ Ψ₁) = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {.(Γ ++ Δ₄)} {A} {x} {A'} {.(A₁ ⊸ B₁)} (⊸c {T} .(Δ₁ ++ x ∷ Δ₂) {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ (x ∷ Δ₂ , refl , refl) | refl , refl | inj₂ ([] , refl , refl) with  cases++-lmap ` Δ₁ (x ∷ Δ₂) Ψ eq2
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = .(lmap ` Ψ₀)} {.(lmap ` Ψ₁)} {.(Γ ++ Δ₄)} {A} {.(` x₁)} {A'} {.(A₁ ⊸ B₁)} (⊸c {T} .(lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ x₁ ∷ Ψ₁)} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 refl g g') refl | inj₂ (.(` x₁) ∷ .(lmap ` Ψ₁) , refl , refl) | refl , refl | inj₂ ([] , refl , refl) | Ψ₀ , x₁ ∷ Ψ₁ , refl , refl , refl
  rewrite cases++-inj₁ (lmap ` Ψ₀) (Γ₁ ++ lmap ` Ψ₁) (A₁ ⊸ B₁ ∷ Γ ++ Δ₄) (A ⊸ ` x₁) | cases++-inj₂ [] (lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) (Γ ++ Δ₄) (A₁ ⊸ B₁)
        | cases++-inj₂ (lmap ` Ψ₁) Γ₁ (Γ ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₂ (` x₁ ∷ lmap ` Ψ₁) (lmap ` Ψ₀) (Γ' ++ Γ ++ Δ₄) (A' ⊸ (A₁ ⊸ B₁))
        | cases++-inj₂ [] (lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) (Γ ++ Δ₄) (A₁ ⊸ B₁) | cases++-lmap-refl ` Ψ₀ (x₁ ∷ Ψ₁) = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = Δ₁} {Δ₂} {.(Γ₀' ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₄)} {A} {x} {A'} {.x₁} (⊸c {T} .(Δ₁ ++ x ∷ Δ₂ ++ x₁ ∷ Γ₀') {Ψ} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 eq2 g g') refl | inj₂ (x ∷ .(Δ₂ ++ x₁ ∷ Γ₀') , refl , refl) | refl , refl | inj₂ (x₁ ∷ Γ₀' , refl , refl) with cases++-lmap ` Δ₁ (x ∷ Δ₂ ++ x₁ ∷ Γ₀') Ψ eq2
... | Ψ₀ , x₂ ∷ Ψ₁ , refl , eq' , refl with inj∷ eq'
... | (refl , eq'') with cases++-lmap ` Δ₂ (_ ∷ Γ₀') Ψ₁ eq''
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {.(lmap ` Ψ₀)} {.(lmap ` Ψ₀')} {.(lmap ` Ψ₁' ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₄)} {A} {.(` x₂)} {A'} {.(` x₂')} (⊸c {T} .(lmap ` Ψ₀ ++ ` x₂ ∷ lmap ` Ψ₀' ++ ` x₂' ∷ lmap ` Ψ₁') {.(Ψ₀ ++ x₂ ∷ Ψ₀' ++ x₂' ∷ Ψ₁')} {Γ = Γ} {Δ₄} {A₁} {B₁} eq1 refl g g') refl | inj₂ (.(` x₂) ∷ .(lmap ` Ψ₀' ++ ` x₂' ∷ lmap ` Ψ₁') , refl , refl) | refl , refl | inj₂ (.(` x₂') ∷ .(lmap ` Ψ₁') , refl , refl) | Ψ₀ , x₂ ∷ .(Ψ₀' ++ x₂' ∷ Ψ₁') , refl , refl , refl | refl , refl | Ψ₀' , x₂' ∷ Ψ₁' , refl , refl , refl
  rewrite cases++-inj₁ (lmap ` Ψ₀) (Γ₁ ++ lmap ` Ψ₀') (` x₂' ∷ lmap ` Ψ₁' ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₄) (A ⊸ ` x₂) | cases++-inj₂ (` x₂' ∷ lmap ` Ψ₁') (lmap ` Ψ₀ ++ ` x₂ ∷ lmap ` Ψ₀') (Γ ++ Δ₄) (A₁ ⊸ B₁)
        | cases++-inj₂ (lmap ` Ψ₀') Γ₁ (lmap ` Ψ₁' ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₄) (` x₂') | cases++-lmap-refl ` (Ψ₀ ++ x₂ ∷ Ψ₀') (x₂' ∷ Ψ₁')
        | cases++-inj₂ (` x₂' ∷ lmap ` Ψ₁') (lmap ` Ψ₀ ++ ` x₂ ∷ lmap ` Ψ₀') (Γ ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₂ (` x₂ ∷ lmap ` Ψ₀') (lmap ` Ψ₀) (Γ' ++ lmap ` Ψ₁' ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₄) (A' ⊸ ` x₂')
        | cases++-lmap-refl ` (Ψ₀ ++ x₂ ∷ Ψ₀') (x₂' ∷ Ψ₁') | cases++-lmap-refl ` Ψ₀ (x₂ ∷ Ψ₀') = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = .(Δ₀ ++ _ ⊸ _ ∷ Γ₀)} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c Δ₀ {Γ = Γ} {Δ₄} eq1 eq2 g g') eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ (Δ₂ ++ B' ∷ Δ₃) Δ₄ q
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {Δ₀ = .(Δ₀ ++ _ ⊸ _ ∷ Γ₀)} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c Δ₀ {Γ = Γ} {Δ₄} eq1 eq2 g g') eq | inj₁ (Γ₀ , refl , q) | inj₁ (Γ₀' , refl , q') with cases++ Δ₂ Γ₀' Δ₃ Δ₄ (sym q')
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {.(Δ₀ ++ _ ⊸ _ ∷ Γ₀)} {Δ₂} {.(Γ₀'' ++ Δ₄)} {A} {B} {A'} {B'} (⊸c {T} Δ₀ {Ψ} {.(Γ₀ ++ B ∷ Δ₂ ++ B' ∷ Γ₀'')} {Δ₄} {A = A₁}{B₁} eq1 eq2 g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (.(Δ₂ ++ B' ∷ Γ₀'') , refl , refl) | inj₁ (Γ₀'' , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ A ⊸ B ∷ Γ₁ ++ Δ₂) (B' ∷ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₁ (Γ₀ ++ A ⊸ B ∷ Γ₁ ++ Δ₂) Γ₀'' Δ₄ B'
        | cases++-inj₁ Δ₀ (Γ₀ ++ B ∷ Δ₂) (B' ∷ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₁ (Γ₀ ++ B ∷ Δ₂) Γ₀'' Δ₄ B'
        | cases++-inj₁ Δ₀ Γ₀ (B ∷ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀'' ++ Δ₄) (A₁ ⊸ B₁) | cases++-inj₁ Γ₀ (Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀'') Δ₄ B
        = cong₂ (⊸c {T} Δ₀ {Ψ}{Γ₀ ++ _ ∷ Γ₁ ++ Δ₂ ++ _ ∷ Γ' ++ Γ₀''}{Δ₄} eq1 eq2) (⊸c⊸c-focus' g refl) refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {.(Δ₀ ++ A₁ ⊸ B₁ ∷ Γ₀)} {.(Γ₀' ++ Γ₀'')} {Δ₃} {A} {B} {A'} {B'} (⊸c {T} Δ₀ {Ψ} {.(Γ₀ ++ B ∷ Γ₀')} {.(Γ₀'' ++ B' ∷ Δ₃)} {A₁} {B₁} eq1 eq2 g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₂ (Γ₀'' , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ A ⊸ B ∷ Γ₁ ++ Γ₀' ++ Γ₀'') (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ Γ₀'' (Γ₀ ++ A ⊸ B ∷ Γ₁ ++ Γ₀') Δ₃ B'
        | cases++-inj₁ Δ₀ (Γ₀ ++ B ∷ Γ₀' ++ Γ₀'') (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ Γ₀'' (Γ₀ ++ B ∷ Γ₀') Δ₃ B'
        | cases++-inj₁ Δ₀ Γ₀ (B ∷ Γ₀' ++ Γ₀'' ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B₁) | cases++-inj₁ Γ₀ Γ₀' (Γ₀'' ++ A' ⊸ B' ∷ Γ' ++ Δ₃) B = refl
⊸c⊸c-focusR' {Γ = Γ₁} {Γ'} {.(Δ₀ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀')} {Δ₂} {Δ₃} {A} {B} {A'} {B'} (⊸c {T} Δ₀ {Ψ} {Γ = Γ} {.(Γ₀' ++ B ∷ Δ₂ ++ B' ∷ Δ₃)} {A₁} {B₁} eq1 eq2 g g') refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀' ++ A ⊸ B ∷ Γ₁ ++ Δ₂) (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ (Γ₀' ++ A ⊸ B ∷ Γ₁ ++ Δ₂) Γ Δ₃ B'
        | cases++-inj₁ Δ₀ (Γ ++ Γ₀' ++ B ∷ Δ₂) (B' ∷ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ (Γ₀' ++ B ∷ Δ₂) Γ Δ₃ B'
        | cases++-inj₁ Δ₀ (Γ ++ Γ₀') (B ∷ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B₁) | cases++-inj₂ Γ₀' Γ (Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) B
        = cong (⊸c {T} Δ₀ {Ψ} eq1 eq2 g) (⊸c⊸c-focusR' {Γ = Γ₁}{Δ₀ =  Δ₀ ++ B₁ ∷ Γ₀'}{Δ₁ = Δ₂} g' refl) 

⊸c⊸c-focus2' : {S : Stp} {Γ Δ Δ₀ Δ₁ Δ₂ Δ₃ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ₀ ++ B ∷ Δ₁ ⊢L A} {f' : nothing ∣ Γ ⊢L A'} (g : S ∣ Δ ⊢L C)
    → (eq : Δ ≡ Δ₂ ++ B' ∷ Δ₃)
    → ⊸c-focus (Δ₂ ++ _ ∷  Δ₀) f' (⊸c-focus' Δ₂ f g eq)
          ≡ ⊸c-focus' Δ₂ (⊸c-focus Δ₀ f' f) g eq
⊸c⊸c-focusR2' : {S : Stp} {Γ Δ Δ₀ Δ₁ Δ₂ Δ₃ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ₀ ++ B ∷ Δ₁ ⊢L A} {f' : nothing ∣ Γ ⊢L A'} (g : S ∣ Δ ⊢R C)
    → (eq : Δ ≡ Δ₂ ++ B' ∷ Δ₃)
    → ⊸c-focusR' (Δ₂ ++ _ ∷  Δ₀) f' (⊸c-focusR' Δ₂ f g eq) refl
          ≡ ⊸c-focusR' Δ₂ (⊸c-focus Δ₀ f' f) g eq

⊸c⊸c-focus2' (⊸r g) refl = cong ⊸r (⊸c⊸c-focus2' g refl)
⊸c⊸c-focus2' (switch q f) eq = cong (switch q) (⊸c⊸c-focusR2' f eq)

⊸c⊸c-focusR2' {Δ₂ = Δ₂} {Δ₃} {B' = B'} (base {Γ = Γ} g eq1 eq2) refl with cases++-lmap ` Δ₂ (B' ∷ Δ₃) Γ eq2
⊸c⊸c-focusR2' {Δ₀ = Δ₀} {Δ₁} {Δ₂ = .(lmap ` Ψ₀)} {.(lmap ` Ψ₁)} {A} {B} {B' = .(` x)} {` _} (base {Γ = .(Ψ₀ ++ x ∷ Ψ₁)} g eq1 refl) refl | Ψ₀ , x ∷ Ψ₁ , refl , refl , refl
  rewrite cases++-inj₁ (lmap ` Ψ₀) Δ₀ (B ∷ Δ₁ ++ lmap ` Ψ₁) (A ⊸ ` x) | cases++-inj₁ Δ₀ Δ₁ (lmap ` Ψ₁) B = refl
⊸c⊸c-focusR2' {Δ₂ = Δ₂} {Δ₃} (⊸l {Γ} {Δ} f g) eq with cases++ Δ₂ Γ Δ₃ Δ eq
⊸c⊸c-focusR2' {just (_ ⊸ _)} {Γ} {Δ₀ = Δ₀} {Δ₁} {Δ₂ = Δ₂} {.(Γ₀ ++ Δ)} {A} {B} {B' = B'} (⊸l {.(Δ₂ ++ B' ∷ Γ₀)} {Δ} f g) refl | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₁ (Δ₂ ++ A ⊸ B' ∷ Δ₀) (Δ₁ ++ Γ₀) Δ B = cong₂ (⊸l {Δ₂ ++ _ ∷ Δ₀ ++ _ ∷ Γ ++ Δ₁ ++ Γ₀}{Δ}) (⊸c⊸c-focus2' f refl) refl
⊸c⊸c-focusR2' {just (_ ⊸ _)} {Γ₁} {Δ₀ = Δ₀} {Δ₁} {Δ₂ = .(Γ ++ Γ₀)} {Δ₃} {A} {B} {B' = B'} (⊸l {Γ} {.(Γ₀ ++ B' ∷ Δ₃)} f g) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ A ⊸ B' ∷ Δ₀) Γ (Δ₁ ++ Δ₃) B = cong (⊸l {Γ}{Γ₀ ++ _ ∷ Δ₀ ++ _ ∷ Γ₁ ++ Δ₁ ++ Δ₃} f) (⊸c⊸c-focusR2' g refl)
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {Δ₂ = Δ₂} {Δ₃} {A₁} {B₁} {A'} {B' = B'} (⊸c {T} Δ₀ {Ψ} {Γ} {Δ₁} {A} {B} eq1 eq2 g g') eq with cases++ Δ₀ Δ₂ (Γ ++ Δ₁) (B' ∷ Δ₃) (sym eq)
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {Δ₂ = .(Δ₀ ++ A ⊸ B ∷ Γ₀)} {Δ₃} {A₁} {B₁} {A'} {B' = B'} (⊸c {T} Δ₀ {Ψ} {Γ} {Δ₁} {A} {B} eq1 eq2 g g') eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₃ Δ₁ q
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {.(Δ₀ ++ A ⊸ B ∷ Γ₀)} {.(Γ₀' ++ Δ₁)} {A₁} {B₁} {A'} {B' = B'} (⊸c {T} Δ₀ {Ψ} {.(Γ₀ ++ B' ∷ Γ₀')} {Δ₁} {A} {B} eq1 eq2 g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ A₁ ⊸ B' ∷ Δ₄) (B₁ ∷ Δ₅ ++ Γ₀' ++ Δ₁) (A ⊸ B) | cases++-inj₁ (Γ₀ ++ A₁ ⊸ B' ∷ Δ₄) (Δ₅ ++ Γ₀') Δ₁ B₁
  = cong₂ (⊸c {T} Δ₀ {Ψ}{Γ₀ ++ _ ∷ Δ₄ ++ _ ∷ Γ₁ ++ Δ₅ ++ Γ₀'}{Δ₁} eq1 eq2) (⊸c⊸c-focus2' g refl) refl
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {.(Δ₀ ++ A ⊸ B ∷ Γ ++ Γ₀')} {Δ₃} {A₁} {B₁} {A'} {B' = B'} (⊸c {T} Δ₀ {Ψ} {Γ} {.(Γ₀' ++ B' ∷ Δ₃)} {A} {B} eq1 eq2 g g') refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀' ++ A₁ ⊸ B' ∷ Δ₄) (B₁ ∷ Δ₅ ++ Δ₃) (A ⊸ B) | cases++-inj₂ (Γ₀' ++ A₁ ⊸ B' ∷ Δ₄) Γ (Δ₅ ++ Δ₃) B₁
  = cong (⊸c {T} Δ₀ {Ψ} {Γ}{Γ₀' ++ _ ∷ Δ₄ ++ _ ∷ Γ₁ ++ Δ₅ ++ Δ₃} eq1 eq2 g) (⊸c⊸c-focusR2' {Δ₀ = Δ₄} {Δ₂ = Δ₀ ++ B ∷ Γ₀'} g' refl)
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {Δ₂ = .Δ₀} {.(Γ ++ Δ₁)} {A₁} {B₁} {A'} {B' = .(A ⊸ B)} (⊸c {T} Δ₀ {Ψ} {Γ} {Δ₁} {A} {B} eq1 eq2 g g') refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ Δ₀ Δ₄ (B₁ ∷ Δ₅ ++ Γ ++ Δ₁) (A₁ ⊸ (A ⊸ B)) | cases++-inj₁ Δ₄ Δ₅ (Γ ++ Δ₁) B₁ = refl
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {Δ₂ = Δ₂} {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Δ₁)} {A₁} {B₁} {A'} {B' = .x} (⊸c {T} .(Δ₂ ++ x ∷ Γ₀) {Ψ} {Γ} {Δ₁} {A} {B} eq1 eq2 g g') refl | inj₂ (x ∷ Γ₀ , refl , refl) with cases++-lmap ` Δ₂ (x ∷ Γ₀) Ψ eq2
⊸c⊸c-focusR2' {Γ = Γ₁} {Δ₀ = Δ₄} {Δ₅} {Δ₂ = .(lmap ` Ψ₀)} {.(lmap ` Ψ₁ ++ A ⊸ B ∷ Γ ++ Δ₁)} {A₁} {B₁} {A'} {.(` x₁)} (⊸c {T} .(lmap ` Ψ₀ ++ ` x₁ ∷ lmap ` Ψ₁) {.(Ψ₀ ++ x₁ ∷ Ψ₁)} {Γ} {Δ₁} {A} {B} eq1 refl g g') refl | inj₂ (.(` x₁) ∷ .(lmap ` Ψ₁) , refl , refl) | Ψ₀ , x₁ ∷ Ψ₁ , refl , refl , refl
  rewrite cases++-inj₁ (lmap ` Ψ₀) Δ₄ (B₁ ∷ Δ₅ ++ lmap ` Ψ₁ ++ A ⊸ B ∷ Γ ++ Δ₁) (A₁ ⊸ ` x₁) | cases++-inj₁ Δ₄ Δ₅ (lmap ` Ψ₁ ++ A ⊸ B ∷ Γ ++ Δ₁) B₁ = refl

congfocus : ∀{S}{Γ}{A} {f g : S ∣ Γ ⊢V A} → f ≗V g
  → focus f ≡ focus g
congfocus refl = refl
congfocus (~ eq) = sym (congfocus eq)
congfocus (eq ∙ eq₁) = trans (congfocus eq) (congfocus eq₁)
congfocus (⊸r p) = cong ⊸r (congfocus p)
congfocus (⊸l p p₁) = cong₂ ⊸l-focus (congfocus p) (congfocus p₁)
congfocus (⊸c Δ₀ p p₁) =
  cong₂ (⊸c-focus Δ₀) (congfocus p) (congfocus p₁)
congfocus ⊸r⊸l = refl
congfocus ⊸r⊸c = refl
congfocus ⊸c⊸l = ⊸c⊸l-focus' _ refl
congfocus ⊸c⊸l2 = ⊸c⊸l2-focus _
congfocus ⊸c⊸c = ⊸c⊸c-focus' _ refl
congfocus ⊸c⊸c2 = ⊸c⊸c-focus2' _ refl

-- ====================================================================

-- focus after embL is identity

mutual 
  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              (f : S ∣ Γ ⊢L C) → focus (embL f) ≡ f
  focus-embL (⊸r f) = cong ⊸r (focus-embL f)
  focus-embL (switch q f) = focus-embR q f

  focus-embR : {S : Stp} → {Γ : Cxt} → {C : Fma} (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → focus (embR f) ≡ switch q f
  focus-embR q (base f eq1 eq2) = refl
  focus-embR q (⊸l f g) =
    cong₂ ⊸l-focus (focus-embL f) (focus-embR q g)
  focus-embR q (⊸c Δ₀ eq1 eq2 f g) =
    trans (cong₂ (⊸c-focus Δ₀) (focus-embL f) (focus-embR q g))
      (cong (switch q) (⊸c-focusR'-eq Δ₀ eq1 eq2 f g refl))

-- embL after focus is ≗V-related to identity

embL-⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C) →
              embL (⊸l-focus f g) ≗V ⊸l (embL f) (embL g)
embL-⊸l-focus f (⊸r g) = ⊸r (embL-⊸l-focus f g) ∙ ⊸r⊸l
embL-⊸l-focus f (switch p g) = refl

embL-⊸c-focus' : ∀{S} Δ₀ {Δ Γ Δ₁ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) (g : S ∣ Δ ⊢L C) →
              (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁) →
              embL (⊸c-focus' Δ₀ f g eq) ≗V ⊸c Δ₀ (embL f) (embL (subst (λ a → S ∣ a ⊢L C) eq g))
embR-⊸c-focus' : ∀{S} Δ₀ {Δ Γ Δ₁ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) (g : S ∣ Δ ⊢R C) →
              (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁) →
              embR (⊸c-focusR' Δ₀ f g eq) ≗V ⊸c Δ₀ (embL f) (embR (subst (λ a → S ∣ a ⊢R C) eq g))

embL-⊸c-focus' Δ₀ f (⊸r g) refl = ⊸r (embL-⊸c-focus' Δ₀ f g refl) ∙ ⊸r⊸c
embL-⊸c-focus' Δ₀ f (switch q f₁) refl = embR-⊸c-focus' Δ₀ f f₁ refl

embR-⊸c-focus' Δ₀ f (base g eq1 eq2) refl = refl
embR-⊸c-focus' Δ₀ {Δ₁ = Δ₁} f (⊸l {Γ} {Δ} g h) eq with cases++ Δ₀ Γ Δ₁ Δ eq
embR-⊸c-focus' {just (_ ⊸ _)} Δ₀ {Δ₁ = .(Γ₀ ++ Δ)} f (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g h) refl | inj₁ (Γ₀ , refl , refl) = ⊸l (embL-⊸c-focus' Δ₀ f g refl) refl ∙ ~ ⊸c⊸l2
embR-⊸c-focus' {just (_ ⊸ _)} .(Γ ++ Γ₀) {Δ₁ = Δ₁} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} g h) refl | inj₂ (Γ₀ , refl , refl) = ⊸l refl (embR-⊸c-focus' Γ₀ f h refl) ∙ ~ ⊸c⊸l
embR-⊸c-focus' Δ₀ {Δ₁ = Δ₂} f (⊸c Δ₁ {Γ = Γ} {Δ₃} eq1 eq2 g h) eq with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (_ ∷ Δ₂) (sym eq)
... | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₂ Δ₃ q
embR-⊸c-focus' .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ₁ = .(Γ₀' ++ Δ₃)} f (⊸c Δ₁ {Γ = .(Γ₀ ++ _ ∷ Γ₀')} {Δ₃} eq1 eq2 g h) refl | inj₁ (Γ₀ , refl , q) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (embL-⊸c-focus' Γ₀ f g refl) refl ∙ ~ ⊸c⊸c2
embR-⊸c-focus' .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') {Δ₁ = Δ₂} f (⊸c Δ₁ {Γ = Γ} {.(Γ₀' ++ _ ∷ Δ₂)} eq1 eq2 g h) refl | inj₁ (.(Γ ++ Γ₀') , refl , q) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ refl (embR-⊸c-focus' (Δ₁ ++ _ ∷ Γ₀') f h refl) ∙ ~ ⊸c⊸c
embR-⊸c-focus' Δ₀ {Δ₁ = .(Γ ++ Δ₃)} f (⊸c .(Δ₀ ++ []) {Γ = Γ} {Δ₃} eq1 eq2 g h) refl | inj₂ ([] , refl , refl) = refl
embR-⊸c-focus' Δ₀ {Δ₁ = .(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Ψ} {Γ = Γ} {Δ₃} eq1 eq2 g h) refl | inj₂ (x ∷ Γ₀ , refl , refl) with cases++-lmap ` Δ₀ (x ∷ Γ₀) Ψ eq2
... | Ψ₀ , _ ∷ Ψ₁ , refl , refl , refl = refl

embL-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              (f : S ∣ Γ ⊢V C) → embL (focus f) ≗V f
embL-focus (base f eq1 eq2) = refl
embL-focus (⊸r f) = ⊸r (embL-focus f)
embL-focus (⊸l f g) =
  embL-⊸l-focus (focus f) (focus g) ∙ ⊸l (embL-focus f) (embL-focus g)
embL-focus (⊸c Δ₀ f g) =
  embL-⊸c-focus' Δ₀ (focus f) (focus g) refl ∙ ⊸c Δ₀ (embL-focus f) (embL-focus g)



