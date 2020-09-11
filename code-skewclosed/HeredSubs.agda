{-# OPTIONS --rewriting #-}

module HeredSubs where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Maybe renaming (map to mmap)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Data.Unit 
open import Formulae
open import Focusing

-- =======================================================================
-- -- Natural deduction and hereditary substitutions
-- =======================================================================

infix 2 _⊢_

data _⊢_ : Cxt → Fma → Set where
  ax : {A : Fma} → A ∷ [] ⊢ A 
  ⊸i : {Γ : Cxt} {A B : Fma}
    → Γ ++ A ∷ [] ⊢ B → Γ ⊢ A ⊸ B
  ⊸e : {Γ Δ : Cxt} {A B : Fma}
    → Γ ⊢ A ⊸ B → Δ ⊢ A → Γ ++ Δ ⊢ B
  Ii : [] ⊢ I
  Ie : {Γ Δ : Cxt} {C : Fma}
    → Γ ⊢ I → Δ ⊢ C → Γ ++ Δ ⊢ C

subst-cxt : {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → Γ ⊢ A → Γ' ⊢ A 
subst-cxt refl f = f

-- Substitution is admissible

sub : ∀{Γ Δ} Δ₀ {Δ₁ A C} (t : Γ ⊢ A) (u : Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → Δ₀ ++ Γ ++ Δ₁ ⊢ C
sub Δ₀ t (⊸i u) refl = ⊸i (sub Δ₀ t u refl)
sub Δ₀ t Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
sub Δ₀ {Δ₁} t (⊸e {Γ} {Δ} u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub Δ₀ {.(Γ₀ ++ Δ)} t (⊸e {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} u v) eq | inj₁ (Γ₀ , refl , refl) = ⊸e (sub Δ₀ t u refl) v
sub .(Γ ++ Γ₀) {Δ₁} t (⊸e {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} u v) eq | inj₂ (Γ₀ , refl , refl) = ⊸e u (sub Γ₀ t v refl)
sub Δ₀ {Δ₁} t (Ie {Γ} {Δ} u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub Δ₀ {.(Γ₀ ++ Δ)} t (Ie {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} u v) eq | inj₁ (Γ₀ , refl , refl) = Ie (sub Δ₀ t u refl) v
sub .(Γ ++ Γ₀) {Δ₁} t (Ie {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} u v) eq | inj₂ (Γ₀ , refl , refl) = Ie u (sub Γ₀ t v refl)
sub [] t ax refl = t
sub (_ ∷ Δ₀) t ax eq = ⊥-elim ([]disj∷ Δ₀ (inj∷ eq .proj₂))

-- =======================================================================

infixl 20 _∙_
infix 21 ~_

-- Equational theory of terms

data _≑_ : {Γ : Cxt}{A : Fma} → Γ ⊢ A → Γ ⊢ A → Set where
  refl : ∀{Γ}{A}{t : Γ ⊢ A} → t ≑ t
  ~_ : ∀{Γ}{A}{t u : Γ ⊢ A} → t ≑ u → u ≑ t
  _∙_ : ∀{Γ}{A}{t u v : Γ ⊢ A} → t ≑ u → u ≑ v → t ≑ v
  ⊸i : ∀{Γ}{A}{B}{t u : Γ ++ A ∷ [] ⊢ B} → t ≑ u → ⊸i t ≑ ⊸i u
  ⊸e : ∀{Γ}{Δ}{A}{B}{t t' : Γ ⊢ A ⊸ B}{u u' : Δ ⊢ A}
    → t ≑ t' → u ≑ u' → ⊸e t u ≑ ⊸e t' u'
  Ie : ∀{Γ}{Δ}{C}{t t' : Γ ⊢ I}{u u' : Δ ⊢ C}
    → t ≑ t' → u ≑ u' → Ie t u ≑ Ie t' u'
  beta : ∀{Γ}{Δ}{A}{B} {t :  Γ ++ A ∷ [] ⊢ B} {u : Δ ⊢ A}
    → ⊸e (⊸i t) u ≑ sub Γ u t refl --sub t (idS Γ ++S u ∷ [])
  eta : ∀{Γ}{A}{B} {t : Γ ⊢ A ⊸ B} → t ≑ ⊸i (⊸e t ax)
  betaI : ∀{Γ}{C} {t : Γ ⊢ C} → Ie Ii t ≑ t
  etaI : ∀{Γ} {t : Γ ⊢ I} → t ≑ Ie t Ii
  ⊸eIe : ∀ {Γ Δ Λ A B} {t : Γ ⊢ I} {u : Δ ⊢ A ⊸ B} {v : Λ ⊢ A}
    → ⊸e (Ie t u) v ≑ Ie t (⊸e u v)
  IeIe : ∀ {Γ Δ Λ C} {t : Γ ⊢ I} {u : Δ ⊢ I} {v : Λ ⊢ C}
    → Ie (Ie t u) v ≑ Ie t (Ie u v)
  ⊸iIe : ∀ {Γ Δ A B} {t : Γ ⊢ I} {u : Δ ++ A ∷ [] ⊢ B} 
    → ⊸i {Γ ++ Δ} (Ie t u) ≑ Ie t (⊸i u)

≡-to-≑ : ∀{Γ A} {t u : Γ ⊢ A} → t ≡ u → t ≑ u
≡-to-≑ refl = refl


-- =======================================================================

-- Normal forms, neutrals, spines

infix 2 _⊢Nf_ _⊢Ne_ 

data _⊢Nf_ : Cxt → Fma → Set
data _⊢Ne_ : Cxt → Fma → Set
data Sp : Cxt → Fma → Fma → Set

data _⊢Nf_ where
  ⊸i : {Γ : Cxt} {A B : Fma}
    → Γ ++ A ∷ [] ⊢Nf B → Γ ⊢Nf A ⊸ B
  Ii : [] ⊢Nf I
  Ie : {Γ Δ : Cxt} {C : Fma} (p : not⊸ C)
    → Γ ⊢Ne I → Δ ⊢Nf C → Γ ++ Δ ⊢Nf C
  switch : {Γ : Cxt} {X : At}
    → Γ ⊢Ne ` X → Γ ⊢Nf ` X

data _⊢Ne_ where
  sp : ∀{Δ A B} (s : Sp Δ A B) → A ∷ Δ ⊢Ne B

data Sp where
  [] : ∀{A} → Sp [] A A
  _∷_ : ∀{Γ Δ A B C} (f : Γ ⊢Nf A) (s : Sp Δ B C) → Sp (Γ ++ Δ) (A ⊸ B) C

-- Embedding of normal forms, neutrals and spines into terms

embNf : ∀ {Γ C} → Γ ⊢Nf C → Γ ⊢ C
embNe : ∀ {Γ C} → Γ ⊢Ne C → Γ ⊢ C
embSp : ∀ {Γ Δ A B} → Γ ⊢ A → Sp Δ A B → Γ ++ Δ ⊢ B

embNf (⊸i f) = ⊸i (embNf f)
embNf Ii = Ii
embNf (Ie p f g) = Ie (embNe f) (embNf g)
embNf (switch f) = embNe f

embNe (sp s) = embSp ax s

embSp f [] = f
embSp f (g ∷ s) = embSp (⊸e f (embNf g)) s

-- Embedding neutrals into normal forms (i.e. eta expansion)

⊸eSp : ∀{Γ Δ A B C} → Sp Γ A (B ⊸ C) → Δ ⊢Nf B → Sp (Γ ++ Δ) A C
⊸eSp [] f = f ∷ []
⊸eSp (g ∷ s) f = g ∷ ⊸eSp s f

ne2nf : ∀{Γ C} → Γ ⊢Ne C → Γ ⊢Nf C
ne2nf {C = ` X} f = switch f
ne2nf {C = I} f = Ie tt f Ii
ne2nf {C = A ⊸ B} (sp s) = ⊸i (ne2nf (sp (⊸eSp s (ne2nf (sp [])))))

-- Axiom rule in Nf

nax : ∀{A} → A ∷ [] ⊢Nf A
nax = ne2nf (sp [])

-- I-elimination in Nf is admissible, called IeNf

Ie-gen : {Γ Δ : Cxt} {C : Fma}
  → Γ ⊢Ne I → Δ ⊢Nf C → Γ ++ Δ ⊢Nf C
Ie-gen t (⊸i u) = ⊸i (Ie-gen t u)
Ie-gen t Ii = Ie tt t Ii
Ie-gen t (Ie p u v) = Ie p t (Ie-gen u v)
Ie-gen t (switch u) = Ie tt t (switch u)

Ie-gen-eq : {Γ Δ : Cxt} {C : Fma} (p : not⊸ C)
  → (t : Γ ⊢Ne I) (u : Δ ⊢Nf C)
  → Ie p t u ≡ Ie-gen t u
Ie-gen-eq tt t Ii = refl
Ie-gen-eq p t (Ie q u v) with not⊸-isprop _ p q
... | refl = cong (Ie p t) (Ie-gen-eq p u v)
Ie-gen-eq tt t (switch u) = refl

IeNf : {Γ Δ : Cxt} {C : Fma}
  → Γ ⊢Nf I → Δ ⊢Nf C → Γ ++ Δ ⊢Nf C
IeNf Ii u = u
IeNf (Ie p t u) v = Ie-gen t (IeNf u v)

-- Some equalities involving IeNf

IeNf⊸i : {Γ Δ : Cxt} {A B : Fma}
  → (t : Γ ⊢Nf I) (u : Δ ++ A ∷ [] ⊢Nf B)
  → IeNf t (⊸i u) ≡ ⊸i (IeNf t u)
IeNf⊸i Ii u = refl
IeNf⊸i (Ie p t v) u = cong (Ie-gen t) (IeNf⊸i v u)

Ie-genIeNf : {Γ Δ Λ : Cxt} {C : Fma}
  → (t : Γ ⊢Ne I) (u : Δ ⊢Nf I) (v : Λ ⊢Nf C)
  → Ie-gen t (IeNf u v) ≡ IeNf (Ie-gen t u) v
Ie-genIeNf t Ii v = refl
Ie-genIeNf t (Ie p u u') v = cong (Ie-gen t) (Ie-genIeNf u u' v)

IeNfIeNf : {Γ Δ Λ : Cxt} {C : Fma}
  → (t : Γ ⊢Nf I) (u : Δ ⊢Nf I) (v : Λ ⊢Nf C)
  → IeNf t (IeNf u v) ≡ IeNf (IeNf t u) v
IeNfIeNf Ii u v = refl
IeNfIeNf (Ie p t t') u v =
  trans (cong (Ie-gen t) (IeNfIeNf t' u v))
    (Ie-genIeNf t (IeNf t' u) v)  

-- =======================================================================

-- Hereditary substitutions

-- Simultaneously define
-- -- subNf: substitution of a normal form in a normal form
-- -- subSp and ◇: substitutions of a normal form in a spine
-- -- napp : ⊸-elimination in Nf

subNf : ∀{Γ Δ} Δ₀ {Δ₁ A C} (t : Γ ⊢Nf A) (u : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → Δ₀ ++ Γ ++ Δ₁ ⊢Nf C
subSp : ∀{Γ Δ} Δ₀ {Δ₁ A B C} (t : Γ ⊢Nf A) (s : Sp Δ B C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → Sp (Δ₀ ++ Γ ++ Δ₁) B C
_◇_ : ∀{Γ Δ A B} → Γ ⊢Nf A → Sp Δ A B → Γ ++ Δ ⊢Nf B
napp : ∀{Γ Δ A B} → Γ ⊢Nf A ⊸ B → Δ ⊢Nf A → Γ ++ Δ ⊢Nf B

subNf Δ₀ u (⊸i t) refl = ⊸i (subNf Δ₀ u t refl)
subNf Δ₀ u Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
subNf Δ₀ {Δ₁} u (Ie {Γ} {Δ} p t t') eq with cases++ Δ₀ Γ Δ₁ Δ eq
subNf .(_ ++ Γ₀) u (Ie p t t') eq | inj₂ (Γ₀ , refl , refl) = Ie p t (subNf Γ₀ u t' refl)
subNf [] u (Ie p (sp s) t') eq | inj₁ (Γ₀ , refl , refl) = IeNf (u ◇ s) t'
subNf (B ∷ Δ₀) u (Ie p (sp s) t') eq | inj₁ (Γ₀ , refl , refl) = Ie p (sp (subSp Δ₀ u s refl)) t'
subNf [] u (switch (sp s)) refl = u ◇ s
subNf (B ∷ Δ₀) u (switch (sp s)) refl =
  switch (sp (subSp Δ₀ u s refl))

subSp Δ₀ u [] eq = ⊥-elim ([]disj∷ Δ₀ eq)
subSp Δ₀ {Δ₁} u (_∷_ {Γ} {Δ} t s) eq with cases++ Δ₀ Γ Δ₁ Δ eq
subSp Δ₀ u (t ∷ s) eq | inj₁ (Γ₀ , refl , refl) = subNf Δ₀ u t refl ∷ s
subSp ._ u (t ∷ s) eq | inj₂ (Γ₀ , refl , refl) = t ∷ subSp Γ₀ u s refl

t ◇ [] = t
t ◇ (u ∷ s) = napp t u ◇ s

napp {Γ} (⊸i t) u = subNf Γ u t refl

-- The normalization function

nf : ∀{Γ C} → Γ ⊢ C → Γ ⊢Nf C
nf ax = nax
nf (⊸i t) = ⊸i (nf t)
nf (⊸e t u) = napp (nf t) (nf u)
nf Ii = Ii
nf (Ie t u) = IeNf (nf t) (nf u)

-- =======================================================================

-- We show that nf is well-defined, i.e. it sends ≑-equivalent
-- terms to the same normal form.

-- IeNf commutes with substitution 

sub-Ie-gen : ∀{Γ Δ} Δ₀ {Δ₁ Λ A B C} (t : Γ ⊢Nf A) (u : Sp Δ B I) (v : Λ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf (B ∷ Δ₀) t (Ie-gen (sp u) v) (cong (λ x → B ∷ x ++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq) ≡
     Ie-gen (sp (subSp Δ₀ t u eq)) v
sub-Ie-gen Δ₀ t u (⊸i v) refl = cong ⊸i (sub-Ie-gen Δ₀ t u v refl)
sub-Ie-gen Δ₀ {Δ₁} {A = A} t u Ii refl rewrite cases++-inj₁ Δ₀ Δ₁ [] A = refl
sub-Ie-gen Δ₀ {Δ₁} {A = A} t u (Ie {Γ} {Δ} p v w) refl rewrite cases++-inj₁ Δ₀ Δ₁ (Γ ++ Δ) A = refl
sub-Ie-gen Δ₀ {Δ₁} {Λ} {A} t u (switch v) refl rewrite cases++-inj₁ Δ₀ Δ₁ Λ A = refl

sub-Ie-gen3 : ∀{Γ Δ Λ A C} (t : Γ ⊢Nf A) (s : Sp Λ A I) (u : Δ ⊢Nf C)
  → subNf [] t (Ie-gen (sp s) u) refl ≡ IeNf (t ◇ s) u
sub-Ie-gen3 t s (⊸i u) =
  trans (cong ⊸i (sub-Ie-gen3 t s u))
    (sym (IeNf⊸i (t ◇ s) u))
sub-Ie-gen3 t s Ii = refl
sub-Ie-gen3 t s (Ie p u v) = cong (IeNf (t ◇ s)) (sym (Ie-gen-eq p u v))
sub-Ie-gen3 t s (switch u) = refl

sub-Ie-gen2 : ∀{Γ Δ} Δ₀ {Δ₁ Λ A C} (t : Γ ⊢Nf A) (u : Λ ⊢Ne I) (v : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf (Λ ++ Δ₀) t (Ie-gen u v) (cong (Λ ++_) eq) ≡
     Ie-gen u (subNf Δ₀ t v eq)
sub-Ie-gen2 Δ₀ t u (⊸i v) refl = cong ⊸i (sub-Ie-gen2 Δ₀ t u v refl)
sub-Ie-gen2 Δ₀ t u Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
sub-Ie-gen2 Δ₀ {Δ₁} t u (Ie {Γ} {Δ} p v w) eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub-Ie-gen2 .(Γ ++ Γ₀) {Δ₁} {Λ} {A} t u (Ie {Γ} {.(Γ₀ ++ A ∷ Δ₁)} p v w) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ ++ Γ₀) Λ Δ₁ A = cong (Ie p u) (sub-Ie-gen2 Γ₀ t v w refl)
sub-Ie-gen2 [] {.(Γ₀ ++ Δ)} {Λ} {A} t u (Ie {.(A ∷ Γ₀)} {Δ} p (sp s) w) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ [] Λ (Γ₀ ++ Δ) A =
    trans (Ie-gen-eq p u _)
      (cong (Ie-gen u) (sub-Ie-gen3 t s w)) 
sub-Ie-gen2 (B ∷ Δ₀) {.(Γ₀ ++ Δ)} {Λ} {A} t u (Ie {.(B ∷ Δ₀ ++ A ∷ Γ₀)} {Δ} p (sp s) w) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (B ∷ Δ₀) Λ (Γ₀ ++ Δ) A = cong (Ie p u) (sub-Ie-gen Δ₀ t s w refl)
sub-Ie-gen2 [] {Δ₁} {Λ} {A} t u (switch v) refl
  rewrite cases++-inj₂ [] Λ Δ₁ A = Ie-gen-eq tt u _
sub-Ie-gen2 (B ∷ Δ₀) {Δ₁} {Λ} {A} t u (switch v) refl
  rewrite cases++-inj₂ (B ∷ Δ₀) Λ Δ₁ A = Ie-gen-eq tt u _

sub-IeNf : ∀{Γ Δ} Δ₀ {Δ₁ Λ A C} (t : Γ ⊢Nf A) (u : Δ ⊢Nf I) (v : Λ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf Δ₀ t (IeNf u v) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq) ≡
     IeNf (subNf Δ₀ t u eq) v
sub-IeNf Δ₀ t Ii v eq = ⊥-elim ([]disj∷ Δ₀ eq)
sub-IeNf Δ₀ {Δ₁} t (Ie {Γ} {Δ} p u u') v eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub-IeNf .(_ ∷ _ ++ Γ₀) {Δ₁} t (Ie {.(_ ∷ _)} {.(Γ₀ ++ _ ∷ Δ₁)} p (sp s) u') v refl | inj₂ (Γ₀ , refl , refl) =
  trans (sub-Ie-gen2 Γ₀ t (sp s) (IeNf u' v) refl)
    (cong (Ie-gen (sp s)) (sub-IeNf Γ₀ t u' v refl))
sub-IeNf [] {.(Γ₀ ++ Δ)} t (Ie {.(_ ∷ Γ₀)} {Δ} p (sp s) u) v refl | inj₁ (Γ₀ , refl , refl) =
  trans (sub-Ie-gen3 t s (IeNf u v))
    (IeNfIeNf (t ◇ s) u v)
sub-IeNf (B ∷ Δ₀) {.(Γ₀ ++ Δ)} t (Ie {.(B ∷ Δ₀ ++ _ ∷ Γ₀)} {Δ} p (sp s) u) v refl | inj₁ (Γ₀ , refl , refl) =
  sub-Ie-gen Δ₀ t s (IeNf u v) refl

sub-IeNf2 : ∀{Γ Δ} Δ₀ {Δ₁ Λ A C} (t : Γ ⊢Nf A) (u : Λ ⊢Nf I) (v : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf (Λ ++ Δ₀) t (IeNf u v) (cong (Λ ++_) eq) ≡ IeNf u (subNf Δ₀ t v eq) 
sub-IeNf2 Δ₀ t Ii v refl = refl
sub-IeNf2 Δ₀ t (Ie {Δ = Δ} p u u') v refl =
  trans (sub-Ie-gen2 (Δ ++ Δ₀) t u (IeNf u' v) refl)
    (cong (Ie-gen u) (sub-IeNf2 Δ₀ t u' v refl))

-- ne2nf commutes with substitution

subSp-⊸eSp : ∀{Γ Δ Λ} Δ₀ {Δ₁ A A' B C} (t : Γ ⊢Nf A) (s : Sp Δ A' (B ⊸ C)) (u : Λ ⊢Nf B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subSp Δ₀ t (⊸eSp s u) (cong (_++ Λ) {y =  Δ₀ ++ A ∷ Δ₁} eq) ≡
    ⊸eSp (subSp Δ₀ t s eq) u 
subSp-⊸eSp Δ₀ t [] u eq = ⊥-elim ([]disj∷ Δ₀ eq)
subSp-⊸eSp Δ₀ {Δ₁} t (_∷_ {Γ} {Δ} f s) u eq with cases++ Δ₀ Γ Δ₁ Δ eq
subSp-⊸eSp {Γ} {Λ = Λ} Δ₀ {.(Γ₀ ++ Δ)} {A} t (_∷_ {.(Δ₀ ++ A ∷ Γ₀)} {Δ} f s) u refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ Λ) A = refl
subSp-⊸eSp {Λ = Λ} .(Γ ++ Γ₀) {Δ₁} {A} t (_∷_ {Γ} {.(Γ₀ ++ A ∷ Δ₁)} f s) u refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ₁ ++ Λ) A = cong (f ∷_) (subSp-⊸eSp Γ₀ t s u refl)

subNf-ne2nf : ∀{Γ} Δ₀ {Δ₁ A B C} (t : Γ ⊢Nf A) (s : Sp (Δ₀ ++ A ∷ Δ₁) B C)
  → subNf (B ∷ Δ₀) t (ne2nf (sp s)) refl ≡ ne2nf (sp (subSp Δ₀ t s refl))
subNf-ne2nf Δ₀ {C = ` X} t s = refl
subNf-ne2nf Δ₀ {Δ₁} {A} {C = I} t s rewrite cases++-inj₁ Δ₀ Δ₁ [] A = refl
subNf-ne2nf Δ₀ {C = A ⊸ B} t s =
  cong ⊸i (trans (subNf-ne2nf Δ₀ t (⊸eSp s nax))
    (cong (λ x → ne2nf (sp x)) (subSp-⊸eSp Δ₀ t s nax refl)))

-- eta for unit in Nf

etaI-Nf : ∀{Γ} (t : Γ ⊢Nf I) → t ≡ IeNf t Ii
etaI-Nf Ii = refl
etaI-Nf (Ie p t u) =
  trans (Ie-gen-eq p t u)
    (cong (Ie-gen t) (etaI-Nf u))

-- Composition of spines

_◇'_ : ∀{Γ Δ A B C} → Sp Γ A B → Sp Δ B C → Sp (Γ ++ Δ) A C
s ◇' [] = s
s ◇' (f ∷ s') = ⊸eSp s f ◇' s'

◇'∷ : ∀{Γ Δ Λ A B C D} (t : Γ ⊢Nf A) (s : Sp Δ B C) (s' : Sp Λ C D)
  → (t ∷ s) ◇' s' ≡ t ∷ (s ◇' s')
◇'∷ t s [] = refl
◇'∷ t s (f ∷ s') = ◇'∷ t _ s'

◇'-lid : ∀{Γ A B} (s : Sp Γ A B) → [] ◇' s ≡ s
◇'-lid [] = refl
◇'-lid (f ∷ s) = trans (◇'∷ f [] s) (cong (f ∷_) (◇'-lid s))

-- Unitality of substitution,i.e substituting with nax is
-- identity and substituting into nax is also identity.
-- This is proved mutually with a bunch of other auxiliary results,
-- e.g. eta for ⊸ in Nf.

subNf-nax : ∀ {Δ} Δ₀ {Δ₁ A C} (t : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf Δ₀ nax t eq ≡ subst (λ x → x ⊢Nf C) eq t
subSp-nax : ∀ {Δ} Δ₀ {Δ₁ A B C} (s : Sp Δ B C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subSp Δ₀ nax s eq ≡ subst (λ x → Sp x B C) eq s
subNf-ne2nf2 : ∀{Γ Δ A C} (t : Γ ⊢Nf A) (s : Sp Δ A C)
  → subNf [] t (ne2nf (sp s)) refl ≡ t ◇ s
◇-⊸eSp : ∀{Γ Δ A B C} (t : Γ ⊢Nf A) (s : Sp Δ A (B ⊸ C))
  → ⊸i (t ◇ ⊸eSp s nax ) ≡ t ◇ s
eta-Nf : ∀{Γ}{A}{B} (t : Γ ⊢Nf A ⊸ B) → t ≡ ⊸i (napp t nax)
nax-◇ : ∀{Γ A B} (s : Sp Γ A B) → nax ◇ s ≡ ne2nf (sp s)
◇'-eq : ∀{Γ Δ A B C} (s : Sp Γ A B) (s' : Sp Δ B C) → ne2nf (sp s) ◇ s' ≡ ne2nf (sp (s ◇' s'))
subSp-⊸eSp2 : ∀{Γ Δ A B C} (t : Γ ⊢Nf B) (s : Sp Δ A (B ⊸ C))
  → subSp Δ t (⊸eSp s nax) refl ≡ ⊸eSp s t
subNf-nax2 : ∀{Γ C} (t : Γ ⊢Nf C) 
  → subNf [] t nax refl ≡ t

subNf-nax2 t = subNf-ne2nf2 t []

subSp-⊸eSp2 t [] = cong (_∷ []) (subNf-nax2 t)
subSp-⊸eSp2 {B = B} t (_∷_ {Γ} {Δ} f s) rewrite cases++-inj₂ Δ Γ [] B =
  cong (f ∷_) (subSp-⊸eSp2 t s)

◇'-eq s [] = refl
◇'-eq {Γ} s (_∷_ {Γ₁} f s') =
  trans (cong (λ x → _◇_ {_ ∷ Γ ++ Γ₁} x s')
              (trans (subNf-ne2nf Γ f _)
                (cong (λ x → ne2nf (sp x)) (subSp-⊸eSp2 f s))))
      (◇'-eq (⊸eSp s f) s')


subNf-nax Δ₀ (⊸i t) refl = cong ⊸i (subNf-nax Δ₀ t refl)
subNf-nax Δ₀ Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
subNf-nax Δ₀ {Δ₁} (Ie {Γ} {Δ} p x t) eq with cases++ Δ₀ Γ Δ₁ Δ eq
subNf-nax .(Γ ++ Γ₀) {Δ₁} (Ie {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} p u t) refl | inj₂ (Γ₀ , refl , refl) =
  cong (Ie p u) (subNf-nax Γ₀ t refl)
subNf-nax [] {.(Γ₀ ++ Δ)} (Ie {.(_ ∷ Γ₀)} {Δ} p (sp s) t) refl | inj₁ (Γ₀ , refl , refl) =
  trans (cong (λ x → IeNf x t) (nax-◇ s)) (sym (Ie-gen-eq p (sp s) t))
subNf-nax (B ∷ Δ₀) {.(Γ₀ ++ Δ)} (Ie {.(B ∷ Δ₀ ++ _ ∷ Γ₀)} {Δ} p (sp s) t) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → Ie {_ ∷ Δ₀ ++ _ ∷ Γ₀ } p (sp x) t) (subSp-nax Δ₀ s refl)
subNf-nax [] (switch (sp s)) refl = nax-◇ s
subNf-nax (B ∷ Δ₀) (switch (sp s)) refl =
  cong switch (cong sp (subSp-nax Δ₀ s refl))  

subSp-nax Δ₀ [] eq = ⊥-elim ([]disj∷ Δ₀ eq) 
subSp-nax Δ₀ {Δ₁} (_∷_ {Γ} {Δ} f s) eq with cases++ Δ₀ Γ Δ₁ Δ eq
subSp-nax Δ₀ {.(Γ₀ ++ Δ)} (_∷_ {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} f s) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → _∷_ {Δ₀ ++ _ ∷ Γ₀ } x s) (subNf-nax Δ₀ f refl)
subSp-nax .(Γ ++ Γ₀) {Δ₁} (_∷_ {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} f s) refl | inj₂ (Γ₀ , refl , refl) =
  cong (f ∷_) (subSp-nax Γ₀ s refl)

subNf-ne2nf2 {C = ` X} t s = refl
subNf-ne2nf2 {C = I} t s = sym (etaI-Nf _)
subNf-ne2nf2 {C = A ⊸ B} t s =
  trans (cong ⊸i (subNf-ne2nf2 _ _))
    (◇-⊸eSp t s)

◇-⊸eSp t [] = sym (eta-Nf _)
◇-⊸eSp t (f ∷ s) = ◇-⊸eSp (napp t f) s

eta-Nf {Γ} (⊸i t) = cong ⊸i (sym (subNf-nax Γ t refl))

nax-◇ s =
  trans (◇'-eq [] s)
    (cong (λ x → ne2nf (sp x)) (◇'-lid s))

-- More equations satisfyied by substitution in Nf:
-- -- parallel substitutions commute;
-- -- associativity of substitution

subNf-par-subNf : ∀{Γ Δ Λ} Δ₀ Δ₁ {Δ₂ A B C}
  → (t : Γ ⊢Nf A) (u : Λ ⊢Nf B) (v : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Δ₂)
  → subNf Δ₀ t (subNf (Δ₀ ++ A ∷ Δ₁) u v eq) refl ≡
     subNf (Δ₀ ++ Γ ++ Δ₁) u (subNf Δ₀ t v eq) refl
subSp-par-subSp : ∀{Γ Δ Λ} Δ₀ Δ₁ {Δ₂ A A' B C}
  → (t : Γ ⊢Nf A) (u : Λ ⊢Nf B) (s : Sp Δ A' C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Δ₂)
  → subSp Δ₀ t (subSp (Δ₀ ++ A ∷ Δ₁) u s eq) refl ≡
     subSp (Δ₀ ++ Γ ++ Δ₁) u (subSp Δ₀ t s eq) refl
subNf-par-◇ : ∀{Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : Γ ⊢Nf A) (u : Λ ⊢Nf B) (s : Sp Δ A C)
  → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁)
  → t ◇ subSp Δ₀ u s eq ≡ subNf (Γ ++ Δ₀) u (t ◇ s) (cong (Γ ++_) eq)
subNf-ass-◇ : ∀{Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : Γ ⊢Nf A) (u : Δ ⊢Nf B) (s : Sp Λ B C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf Δ₀ t u eq ◇ s ≡
     subNf Δ₀ t (u ◇ s) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq)
subNf-napp2 : ∀{Γ Δ} Δ₀ {Δ₁ Λ A B C} (t : Γ ⊢Nf A) (u : Λ ⊢Nf B ⊸ C) (v : Δ ⊢Nf B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf (Λ ++ Δ₀) t (napp u v) (cong (Λ ++_) eq) ≡
     napp u (subNf Δ₀ t v eq)
subNf-napp : ∀{Γ Δ} Δ₀ {Δ₁ Λ A B C} (t : Γ ⊢Nf A) (u : Δ ⊢Nf B ⊸ C) (v : Λ ⊢Nf B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf Δ₀ t (napp u v) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq) ≡
     napp (subNf Δ₀ t u eq) v
subNf-ass-subNf : ∀{Γ Δ Λ} Δ₀ {Δ₁ Λ₀ Λ₁ A B C}
  → (t : Γ ⊢Nf A) (u : Δ ⊢Nf B) (v : Λ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → (eq2 : Λ ≡ Λ₀ ++ B ∷ Λ₁)
  → subNf (Λ₀ ++ Δ₀) t (subNf Λ₀ u v eq2) (cong (λ x → Λ₀ ++ x ++ Λ₁) eq) ≡
     subNf Λ₀ (subNf Δ₀ t u eq) v eq2
subSp-ass-subSp : ∀{Γ Δ Λ} Δ₀ {Δ₁ Λ₀ Λ₁ A A' B C}
  → (t : Γ ⊢Nf A) (u : Δ ⊢Nf B) (s : Sp Λ A' C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → (eq2 : Λ ≡ Λ₀ ++ B ∷ Λ₁)
  → subSp (Λ₀ ++ Δ₀) t (subSp Λ₀ u s eq2) (cong (λ x → Λ₀ ++ x ++ Λ₁) eq) ≡
     subSp Λ₀ (subNf Δ₀ t u eq) s eq2

subNf-ass-subNf Δ₀ t u (⊸i v) refl refl = cong ⊸i (subNf-ass-subNf Δ₀ t u v refl refl)
subNf-ass-subNf Δ₀ t u Ii eq eq2 = ⊥-elim ([]disj∷ _ eq2)
subNf-ass-subNf Δ₀ {Λ₀ = Λ₀} {Λ₁} t u (Ie {Γ} {Δ} p x v) eq eq2 with cases++ Λ₀ Γ Λ₁ Δ eq2
subNf-ass-subNf Δ₀ {Δ₁} {.(Γ ++ Γ₀)} {Λ₁} {A} t u (Ie {Γ} {.(Γ₀ ++ _ ∷ Λ₁)} p w v) refl refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ Δ₀) Γ (Δ₁ ++ Λ₁) A = cong (Ie p w) (subNf-ass-subNf Δ₀ t u v refl refl)
subNf-ass-subNf {Γ} Δ₀ {Δ₁} {Λ₀ = []} {.(Γ₀ ++ Δ)} t u (Ie {.(_ ∷ Γ₀)} {Δ} p (sp s) v) refl refl | inj₁ (Γ₀ , refl , refl) =
  trans (sub-IeNf Δ₀ t (u ◇ s) v refl) (cong (λ x → IeNf {Δ₀ ++ Γ ++ Δ₁ ++ Γ₀} x v) (sym (subNf-ass-◇ Δ₀ t u s refl)))
subNf-ass-subNf {Γ} Δ₀ {Δ₁} {A' ∷ Λ₀} {.(Γ₀ ++ Δ)} {A} t u (Ie {.(A' ∷ Λ₀ ++ _ ∷ Γ₀)} {Δ} p (sp s) v) refl refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Λ₀ ++ Δ₀) (Δ₁ ++ Γ₀) Δ A =
    cong (λ x → Ie {_ ∷ Λ₀ ++ Δ₀ ++ Γ ++ Δ₁ ++ Γ₀} p (sp x) v) (subSp-ass-subSp Δ₀ t u s refl refl)
subNf-ass-subNf Δ₀ {Λ₀ = []} t u (switch (sp s)) refl refl = sym (subNf-ass-◇ Δ₀ t u s refl)
subNf-ass-subNf Δ₀ {Λ₀ = A' ∷ Λ₀} t u (switch (sp s)) refl refl =
  cong (λ x → switch (sp x)) (subSp-ass-subSp Δ₀ t u s refl refl)

subSp-ass-subSp Δ₀ t u [] eq eq2 =  ⊥-elim ([]disj∷ _ eq2)
subSp-ass-subSp Δ₀ {Λ₀ = Λ₀} {Λ₁} t u (_∷_ {Γ} {Δ} f s) eq eq2 with cases++ Λ₀ Γ Λ₁ Δ eq2
subSp-ass-subSp {Γ} Δ₀ {Δ₁} {Λ₀} {.(Γ₀ ++ Δ)} {A} t u (_∷_ {.(Λ₀ ++ _ ∷ Γ₀)} {Δ} f s) refl refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Λ₀ ++ Δ₀) (Δ₁ ++ Γ₀) Δ A =
    cong (λ x → _∷_ {Λ₀ ++ Δ₀ ++ Γ ++ Δ₁ ++ Γ₀} x s) (subNf-ass-subNf Δ₀ t u f refl refl)
subSp-ass-subSp Δ₀ {Δ₁} {.(Γ ++ Γ₀)} {Λ₁} {A} t u (_∷_ {Γ} {.(Γ₀ ++ _ ∷ Λ₁)} f s) refl refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ Δ₀) Γ (Δ₁ ++ Λ₁) A = cong (f ∷_) (subSp-ass-subSp Δ₀ t u s refl refl)

subNf-ass-◇ Δ₀ t u [] refl = refl
subNf-ass-◇ {Γ} Δ₀ {Δ₁} t u (_∷_ {Γ₁} f s) refl =
  trans (cong (λ x → _◇_ {Δ₀ ++ Γ ++ Δ₁ ++ Γ₁} x s) (sym (subNf-napp Δ₀ t u f refl)))
    (subNf-ass-◇ Δ₀ t (napp u f) s refl)

subNf-par-subNf Δ₀ Δ₁ t u (⊸i v) refl =
  cong ⊸i (subNf-par-subNf Δ₀ Δ₁ t u v refl)
subNf-par-subNf Δ₀ Δ₁ t u Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
subNf-par-subNf Δ₀ Δ₁ {Δ₂} t u (Ie {Γ} {Δ} p v w) eq with cases++ (Δ₀ ++ _ ∷ Δ₁) Γ Δ₂ Δ eq
subNf-par-subNf Δ₀ Δ₁ {Δ₂} t u (Ie {Γ} {.(Γ₀ ++ _ ∷ Δ₂)} p v w) eq | inj₂ (Γ₀ , refl , r) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym r)
subNf-par-subNf {Γ₁} {Λ = Λ} ._ Δ₁ {Δ₂} {A} {B} t u (Ie {Γ} {.((Γ₀' ++ A ∷ Δ₁) ++ B ∷ Δ₂)} p v w) refl | inj₂ (.(Γ₀' ++ A ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ Λ ++ Δ₂) A | cases++-inj₂ Γ₀' Γ (Δ₁ ++ B ∷ Δ₂) A | cases++-inj₂ (Γ₀' ++ Γ₁ ++ Δ₁) Γ Δ₂ B =
    cong (Ie p v) (subNf-par-subNf Γ₀' Δ₁ t u w refl)
subNf-par-subNf {Λ = Λ} [] .(Γ₀' ++ Γ₀) {Δ₂} {A} {B} t u (Ie {.(A ∷ Γ₀')} {.(Γ₀ ++ B ∷ Δ₂)} p (sp s) w) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ [] Γ₀' (Γ₀ ++ Λ ++ Δ₂) A | cases++-inj₁ [] Γ₀' (Γ₀ ++ B ∷ Δ₂) A = sym (sub-IeNf2 Γ₀ u (t ◇ s) w refl)
subNf-par-subNf {Γ} {Λ = Λ} (A' ∷ Δ₀) .(Γ₀' ++ Γ₀) {Δ₂} {A} {B} t u (Ie p (sp s) w) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) 
  rewrite cases++-inj₁ (A' ∷ Δ₀) Γ₀' (Γ₀ ++ Λ ++ Δ₂) A | cases++-inj₁ (A' ∷ Δ₀) Γ₀' (Γ₀ ++ B ∷ Δ₂) A | cases++-inj₂ Γ₀ (Δ₀ ++ Γ ++ Γ₀') Δ₂ B = refl
subNf-par-subNf {Γ} {Λ = Λ} [] Δ₁ {.(Γ₀ ++ Δ)} {A} {B} t u (Ie {.(A ∷ Δ₁ ++ B ∷ Γ₀)} {Δ} p (sp s) w) refl | inj₁ (Γ₀ , refl , refl) =
  trans (cong (λ x → IeNf {Γ ++ Δ₁ ++ Λ ++ Γ₀} x w) (subNf-par-◇ Δ₁ t u s refl))
    (sym (sub-IeNf (Γ ++ Δ₁) u (t ◇ s) w refl))
subNf-par-subNf {Γ} {Λ = Λ} (A' ∷ Δ₀) Δ₁ {.(Γ₀ ++ Δ)} {A} {B} t u (Ie {.(A' ∷ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Γ₀)} {Δ} p (sp s) w) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Λ ++ Γ₀) Δ A | cases++-inj₁ Δ₀ (Δ₁ ++ B ∷ Γ₀) Δ A | cases++-inj₁ (Δ₀ ++ Γ ++ Δ₁) Γ₀ Δ B =
    cong (λ x → Ie {_ ∷ Δ₀ ++ Γ ++ Δ₁ ++ Λ ++ Γ₀} p (sp x) w) (subSp-par-subSp Δ₀ Δ₁ t u s refl) 
subNf-par-subNf [] Δ₁ t u (switch (sp s)) refl = subNf-par-◇ Δ₁ t u s refl
subNf-par-subNf (A' ∷ Δ₀) Δ₁ t u (switch (sp s)) refl = cong (λ x → switch (sp x)) (subSp-par-subSp Δ₀ Δ₁ t u s refl)

subSp-par-subSp Δ₀ Δ₁ t u [] eq = ⊥-elim ([]disj∷ Δ₀ eq)
subSp-par-subSp Δ₀ Δ₁ {Δ₂} {A} {B = B} t u (_∷_ {Γ} {Δ} f s) eq with cases++ (Δ₀ ++ A ∷ Δ₁) Γ Δ₂ Δ eq
subSp-par-subSp {Γ} {Λ = Λ} Δ₀ Δ₁ {.(Γ₀ ++ Δ)} {A} {B = B} t u (_∷_ {.(Δ₀ ++ A ∷ Δ₁ ++ B ∷ Γ₀)} {Δ} f s) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Λ ++ Γ₀) Δ A | cases++-inj₁ Δ₀ (Δ₁ ++ B ∷ Γ₀) Δ A | cases++-inj₁ (Δ₀ ++ Γ ++ Δ₁) Γ₀ Δ B =
    cong (λ x → _∷_ {Δ₀ ++ Γ ++ Δ₁ ++ Λ ++ Γ₀} x s) (subNf-par-subNf Δ₀ Δ₁ t u f refl)
subSp-par-subSp Δ₀ Δ₁ {Δ₂} {A} {B = B} t u (_∷_ {Γ} {.(Γ₀ ++ B ∷ Δ₂)} f s) eq | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
subSp-par-subSp {Γ} {Λ = Λ} Δ₀ .(Γ₀' ++ Γ₀) {Δ₂} {A} {B = B} t u (_∷_ {.(Δ₀ ++ A ∷ Γ₀')} {.(Γ₀ ++ B ∷ Δ₂)} f s) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ Λ ++ Δ₂) A | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ B ∷ Δ₂) A | cases++-inj₂ Γ₀ (Δ₀ ++ Γ ++ Γ₀') Δ₂ B = refl
subSp-par-subSp {Γ₁} {Λ = Λ} .(Γ ++ Γ₀') Δ₁ {Δ₂} {A} {B = B} t u (_∷_ {Γ} f s) refl | inj₂ (.(Γ₀' ++ A ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ Λ ++ Δ₂) A | cases++-inj₂ Γ₀' Γ (Δ₁ ++ B ∷ Δ₂) A | cases++-inj₂ (Γ₀' ++ Γ₁ ++ Δ₁) Γ Δ₂ B =
    cong (f ∷_) (subSp-par-subSp Γ₀' Δ₁ t u s refl)

subNf-par-◇ Δ₀ t u [] eq = ⊥-elim ([]disj∷ Δ₀ eq)
subNf-par-◇ Δ₀ {Δ₁} t u (_∷_ {Γ} {Δ} f s) eq with cases++ Δ₀ Γ Δ₁ Δ eq
subNf-par-◇ {Γ} {Λ = Λ} Δ₀ {.(Γ₀ ++ Δ)} t u (_∷_ {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} f s) refl | inj₁ (Γ₀ , refl , refl) =
  trans (cong (λ x → _◇_ {Γ ++ Δ₀ ++ Λ ++ Γ₀} x s) (sym (subNf-napp2 Δ₀ u t f refl)))
    (subNf-ass-◇ (Γ ++ Δ₀) u (napp t f) s refl )
subNf-par-◇ .(Γ ++ Γ₀) {Δ₁} t u (_∷_ {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} f s) refl | inj₂ (Γ₀ , refl , refl) =
  subNf-par-◇ Γ₀ (napp t f) u s refl

subNf-napp2 Δ₀ {Δ₁} t (⊸i u) v refl = subNf-ass-subNf Δ₀ t v u refl refl

subNf-napp Δ₀ {Δ₁} t (⊸i u) v refl = subNf-par-subNf Δ₀ Δ₁ t v u refl

-- A key lemma: substitution commutes with normalization

sub-nf : ∀{Γ Δ} Δ₀ {Δ₁ A C} (t : Γ ⊢ A) (u : Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → subNf Δ₀ (nf t) (nf u) eq ≡ nf (sub Δ₀ t u eq)
sub-nf Δ₀ t (⊸i u) refl = cong ⊸i (sub-nf Δ₀ t u refl)
sub-nf Δ₀ t Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
sub-nf Δ₀ {Δ₁} t (⊸e {Γ} {Δ} u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub-nf {Γ} Δ₀ {.(Γ₀ ++ Δ)} t (⊸e {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} u v) refl | inj₁ (Γ₀ , refl , refl) =
  trans (subNf-napp Δ₀ (nf t) (nf u) (nf v) refl)
    (cong (λ x → napp {Δ₀ ++ Γ ++ Γ₀} x (nf v)) (sub-nf Δ₀ t u refl))
sub-nf .(Γ ++ Γ₀) {Δ₁} t (⊸e {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} u v) refl | inj₂ (Γ₀ , refl , refl) =
  trans (subNf-napp2 Γ₀ (nf t) (nf u) (nf v) refl)
    (cong (napp (nf u)) (sub-nf Γ₀ t v refl))
sub-nf Δ₀ {Δ₁} t (Ie {Γ} {Δ} u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
sub-nf {Γ} Δ₀ {.(Γ₀ ++ Δ)} t (Ie {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} u v) refl | inj₁ (Γ₀ , refl , refl) = 
  trans (sub-IeNf Δ₀ (nf t) (nf u) (nf v) refl)
    (cong (λ x → IeNf {Δ₀ ++ Γ ++ Γ₀} x (nf v)) (sub-nf Δ₀ t u refl))
sub-nf .(Γ ++ Γ₀) {Δ₁} t (Ie {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} u v) refl | inj₂ (Γ₀ , refl , refl) =
  trans (sub-IeNf2 Γ₀ (nf t) (nf u) (nf v) refl)
    (cong (IeNf (nf u)) (sub-nf Γ₀ t v refl))
sub-nf [] t ax refl = subNf-nax2 (nf t)
sub-nf (x ∷ Δ₀) t ax eq = ⊥-elim ([]disj∷ Δ₀ (inj∷ eq .proj₂))

IeNf-napp : {Γ Δ Λ : Cxt} {A B : Fma}
  → (t : Γ ⊢Nf I) (u : Δ ⊢Nf A ⊸ B) (v : Λ ⊢Nf A)
  → IeNf t (napp u v) ≡ napp (IeNf t u) v
IeNf-napp {Γ}{Δ} t (⊸i u) v =
  sym (trans (cong (λ x → napp {Γ ++ Δ} x v) (IeNf⊸i t u))
    (sub-IeNf2 Δ v t u refl))

-- nf sends ≑-equivalent terms to the same normal form.

congnf : ∀{Γ C} {t u : Γ ⊢ C} → t ≑ u → nf t ≡ nf u
congnf refl = refl
congnf (~ p) = sym (congnf p)
congnf (p ∙ p₁) = trans (congnf p) (congnf p₁)
congnf (⊸i p) = cong ⊸i (congnf p)
congnf (⊸e p p₁) = cong₂ napp (congnf p) (congnf p₁)
congnf (Ie p p₁) = cong₂ IeNf (congnf p) (congnf p₁)
congnf (beta {Γ} {t = t} {u}) = sub-nf Γ u t refl
congnf {t = t} eta = eta-Nf (nf t)
congnf betaI = refl
congnf {t = t} etaI = etaI-Nf (nf t)
congnf (⊸eIe {t = t} {u} {v}) = sym (IeNf-napp (nf t) (nf u) (nf v))
congnf (IeIe {t = t} {u} {v}) = sym (IeNfIeNf (nf t) (nf u) (nf v))
congnf (⊸iIe {t = t} {u}) = sym (IeNf⊸i (nf t) (nf u))

-- =======================================================================

-- We show that each term is equivalent to the embedding of its normal
-- form

-- First, some auxiliary equalities, stating that the embeddings embNf
-- and embSp commute with other operations.

emb-⊸eSp : ∀ {Γ Δ Λ A B C} (t : Γ ⊢ A) (s : Sp Δ A (B ⊸ C)) (n : Λ ⊢Nf B)
  → embSp t (⊸eSp s n) ≡ ⊸e (embSp t s) (embNf n)
emb-⊸eSp t [] n = refl
emb-⊸eSp t (u ∷ s) n = emb-⊸eSp (⊸e t (embNf u)) s n

emb-Ie-gen : ∀{Γ Δ C} (t : Γ ⊢Ne I) (u : Δ ⊢Nf C)
  → embNf (Ie-gen t u) ≑ Ie (embNe t) (embNf u)
emb-Ie-gen t (⊸i u) =
  ⊸i (emb-Ie-gen t u) ∙ ⊸iIe
emb-Ie-gen t Ii = refl
emb-Ie-gen t (Ie p u v) = Ie refl (emb-Ie-gen u v)
emb-Ie-gen t (switch u) = refl

emb-IeNf : ∀{Γ Δ C} (t : Γ ⊢Nf I) (u : Δ ⊢Nf C)
  → embNf (IeNf t u) ≑ Ie (embNf t) (embNf u)
emb-IeNf Ii u = ~ betaI
emb-IeNf (Ie p t t') u =
  emb-Ie-gen t (IeNf t' u)
  ∙ Ie refl (emb-IeNf t' u)
  ∙ ~ IeIe

embSp≑ : ∀ {Γ Δ A B} {t u : Γ ⊢ A} → t ≑ u → (s : Sp Δ A B) → embSp t s ≑ embSp u s
embSp≑ p [] = p
embSp≑ p (f ∷ s) = embSp≑ (⊸e p refl) s


sub-embSp : ∀{Γ Δ} Δ₀ {Δ₁ Λ A B C} (t : Γ ⊢ A) (u : Δ ⊢ B) (s : Sp Λ B C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → embSp (sub Δ₀ t u eq) s ≑ sub Δ₀ t (embSp u s) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq)
sub-embSp Δ₀ t u [] refl = refl
sub-embSp Δ₀ {Δ₁} {A = A} t u (_∷_ {Γ} f s) refl with sub-embSp Δ₀ t (⊸e u (embNf f)) s refl
... | ih rewrite cases++-inj₁ Δ₀ Δ₁ Γ A = ih


-- Another key lemma: substitution commutes with embedding.

emb-subNf : ∀{Γ Δ} Δ₀ {Δ₁ A C} (t : Γ ⊢Nf A) (u : Δ ⊢Nf C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → embNf (subNf Δ₀ t u eq) ≑ sub Δ₀ (embNf t) (embNf u) eq
emb-subSp : ∀{Γ Δ} Δ₀ {Δ₁ Λ A B C} (u : Λ ⊢ B) (t : Γ ⊢Nf A) (s : Sp Δ B C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → embSp u (subSp Δ₀ t s eq) ≑ sub (Λ ++ Δ₀) (embNf t) (embSp u s) (cong (_ ++_) eq)
emb-◇ : ∀{Γ Δ A B} (t : Γ ⊢Nf A) (s : Sp Δ A B)
  → embNf (t ◇ s) ≑ embSp (embNf t) s 
emb-napp : ∀{Γ Δ A B} (t : Γ ⊢Nf A ⊸ B) (u : Δ ⊢Nf A)
  → embNf (napp t u) ≑ ⊸e (embNf t) (embNf u)

emb-subNf Δ₀ t (⊸i u) refl = ⊸i (emb-subNf Δ₀ t u refl)
emb-subNf Δ₀ t Ii eq = ⊥-elim ([]disj∷ Δ₀ eq)
emb-subNf Δ₀ {Δ₁} t (Ie {Γ} {Δ} p u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
emb-subNf .(Γ ++ Γ₀) {Δ₁} t (Ie {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} p u v) eq | inj₂ (Γ₀ , refl , refl) =
  Ie refl (emb-subNf Γ₀ t v refl)
emb-subNf [] {.(Γ₀ ++ Δ)} t (Ie {.(_ ∷ Γ₀)} {Δ} p (sp s) v) eq | inj₁ (Γ₀ , refl , refl) =
  emb-IeNf (t ◇ s) v
  ∙ Ie (emb-◇ t s ∙ sub-embSp [] (embNf t) ax s refl) refl
emb-subNf (B ∷ Δ₀) {.(Γ₀ ++ Δ)} t (Ie {.(B ∷ Δ₀ ++ _ ∷ Γ₀)} {Δ} p (sp s) v) eq | inj₁ (Γ₀ , refl , refl) =
  Ie (emb-subSp Δ₀ ax t s refl) refl
emb-subNf [] t (switch (sp s)) refl =
  emb-◇ t s ∙ sub-embSp [] (embNf t) ax s refl
emb-subNf (B ∷ Δ₀) t (switch (sp s)) refl = emb-subSp Δ₀ ax t s refl

emb-subSp Δ₀ u t [] eq = ⊥-elim ([]disj∷ Δ₀ eq)
emb-subSp Δ₀ {Δ₁} u t (_∷_ {Γ} {Δ} f s) eq with cases++ Δ₀ Γ Δ₁ Δ eq
emb-subSp Δ₀ {.(Γ₀ ++ Δ)} {Λ} {A} u t (_∷_ {.(Δ₀ ++ A ∷ Γ₀)} {Δ} f s) refl | inj₁ (Γ₀ , refl , refl)
  with sub-embSp (Λ ++ Δ₀) (embNf t) (⊸e u (embNf f)) s refl
... | ih rewrite cases++-inj₂ Δ₀ Λ Γ₀ A =
  embSp≑ (⊸e refl (emb-subNf Δ₀ t f refl)) s ∙ ih
emb-subSp .(Γ ++ Γ₀) {Δ₁} u t (_∷_ {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} f s) refl | inj₂ (Γ₀ , refl , refl) =
  emb-subSp Γ₀ (⊸e u (embNf f)) t s refl

emb-◇ t [] = refl
emb-◇ t (f ∷ s) = 
  emb-◇ (napp t f) s
  ∙ embSp≑ (emb-napp t f) s

emb-napp {Γ} (⊸i t) u =
  emb-subNf Γ u t refl
  ∙ ~ beta

-- Embedding a netral into terms is the equivalent to first embedding
-- the neutral into normal forms and then further into terms.

emb-ne2nf : ∀{Γ C} (t : Γ ⊢Ne C) → embNf (ne2nf t) ≑ embNe t
emb-ne2nf {C = ` X} t = refl
emb-ne2nf {C = I} t = ~ etaI
emb-ne2nf {C = A ⊸ B} (sp s) =
  ⊸i (emb-ne2nf _
      ∙ ≡-to-≑ (emb-⊸eSp ax s _)
      ∙ ⊸e refl (emb-ne2nf _))
  ∙ ~ eta

-- Each term is equivalent to the embedding of its normal form

emb-nf : ∀{Γ C} (t : Γ ⊢ C) → embNf (nf t) ≑ t
emb-nf ax = emb-ne2nf _
emb-nf (⊸i t) = ⊸i (emb-nf t)
emb-nf (⊸e t u) =
  emb-napp (nf t) (nf u)
  ∙ ⊸e (emb-nf t) (emb-nf u)
emb-nf Ii = refl
emb-nf (Ie t u) =
  emb-IeNf (nf t) (nf u)
  ∙ Ie (emb-nf t) (emb-nf u)


-- =======================================================================

-- Each normal form is equal to the normalization of its embedding.

nf-emb : ∀{Γ C} (n : Γ ⊢Nf C) → nf (embNf n) ≡ n
ne-emb : ∀{Γ C} (n : Γ ⊢Ne C) → nf (embNe n) ≡ ne2nf n
nf-embSp : ∀{Γ Δ A B} (n : Γ ⊢ A) (s : Sp Δ A B) → nf (embSp n s) ≡ (nf n ◇ s)

nf-emb (⊸i n) = cong ⊸i (nf-emb n)
nf-emb Ii = refl
nf-emb (Ie p n n') =
  trans (cong₂ IeNf (ne-emb n) (nf-emb n'))
    (sym (Ie-gen-eq p n n'))
nf-emb (switch n) = ne-emb n

ne-emb (sp s) = trans (nf-embSp ax s) (nax-◇ s)

nf-embSp n [] = refl
nf-embSp n (f ∷ s) = trans (nf-embSp (⊸e n (embNf f)) s) (cong (λ x → napp (nf n) x ◇ s) (nf-emb f))

-- =======================================================================
-- =======================================================================

-- Equivalence between the focused sequent calculus and the normalized
-- term calculus

-- I-elimination in the focused calculus

Ie-focus : ∀{S Γ Δ C} (p : not⊸ C)
  → (f : S ∣ Γ ⊢L I) (g : nothing ∣ Δ ⊢L C) 
  → S ∣ Γ ++ Δ ⊢L C
Ie-focusR : ∀{S Γ Δ C} (p : not⊸ C)
  → (f : S ∣ Γ ⊢R I) (g : nothing ∣ Δ ⊢L C) 
  → mmap `⊸ S ∣ Γ ++ Δ ⊢L C

Ie-focus q (Il p f) g = Il q (Ie-focus q f g)
Ie-focus q (uf p f) g = uf q (Ie-focus q f g)
Ie-focus q (switch refl r f) g = Ie-focusR q f g   

Ie-focusR p Ir g = g
Ie-focusR p (⊸l f f') g = switch refl p (⊸l f (Ie-focus p f' g))

-- Translation from terms in normal form to focused calculus

nf2foc : ∀{Γ C} → Γ ⊢Nf C → nothing ∣ Γ ⊢L C
sp2foc : ∀{Γ A C} → Sp Γ A C → just A ∣ Γ ⊢L C

nf2foc (⊸i f) = ⊸r (nf2foc f)
nf2foc Ii = switch refl tt Ir
nf2foc (Ie p (sp s) u) = uf p (Ie-focus p (sp2foc s) (nf2foc u)) 
nf2foc (switch (sp s)) = uf tt (sp2foc s)

sp2foc [] = ax-focus
sp2foc (t ∷ s) = ⊸l-focus (nf2foc t) (sp2foc s)

-- ⊸-left rule in Nf

⊸lNf : ∀{Γ Δ Δ' A B C} → Γ ⊢Nf A → Δ' ⊢Nf C
  → Δ' ≡ B ∷ Δ → A ⊸ B ∷ Γ ++ Δ ⊢Nf C
⊸lNf f (⊸i g) refl = ⊸i (⊸lNf f g refl)
⊸lNf f (Ie p (sp s) h) refl = Ie p (sp (f ∷ s)) h
⊸lNf f (switch (sp s)) refl = switch (sp (f ∷ s))

-- Translation from focused calculus to terms in normal form 

foc2nf : ∀{S Γ C} → S ∣ Γ ⊢L C → asCxt S Γ ⊢Nf C
foc2nfR : ∀{S Γ C} → S ∣ Γ ⊢R C → asCxt (mmap `⊸ S) Γ ⊢Nf C

foc2nf (⊸r f) = ⊸i (foc2nf f)
foc2nf (Il p f) = Ie p (sp []) (foc2nf f)
foc2nf (uf p f) = foc2nf f
foc2nf (switch refl q f) = foc2nfR f

foc2nfR ax = switch (sp [])
foc2nfR Ir = Ii
foc2nfR (⊸l {Δ = Δ} f g) = ⊸lNf (foc2nf f) (foc2nf g) refl

-- Some equalities involving the admissible rules IeNf and ⊸lNf

⊸lNf-ne2nf : ∀{Γ Δ A B C} (f : Γ ⊢Nf A) (s : Sp Δ B C)
  → ⊸lNf f (ne2nf (sp s)) refl ≡ ne2nf (sp (f ∷ s))
⊸lNf-ne2nf {C = ` X} f s = refl
⊸lNf-ne2nf {C = I} f s = refl
⊸lNf-ne2nf {C = C ⊸ D} f s = cong ⊸i (⊸lNf-ne2nf _ _)  

Ie-gen⊸lNf : ∀{Γ Δ Λ A B C}  (t : Γ ⊢Nf A) (s : Sp Δ B I) (u : Λ ⊢Nf C)
  → Ie-gen (sp (t ∷ s)) u ≡ ⊸lNf t (Ie-gen (sp s) u) refl
Ie-gen⊸lNf t s (⊸i u) = cong ⊸i (Ie-gen⊸lNf t s u)
Ie-gen⊸lNf t s Ii = refl
Ie-gen⊸lNf t s (Ie p u v) = refl
Ie-gen⊸lNf t s (switch u) = refl

IeNf⊸lNf : ∀{Γ Δ Δ' Λ A B C}  (t : Γ ⊢Nf A) (u : Δ' ⊢Nf I) (v : Λ ⊢Nf C)
  → (eq : Δ' ≡ B ∷ Δ)
  → IeNf (⊸lNf t u eq) v ≡ ⊸lNf t (IeNf u v) (cong (λ x → x ++ Λ) eq) 
IeNf⊸lNf t (Ie p (sp s) u') v refl = Ie-gen⊸lNf t s _

-- Relation between the translation foc2nf and other admissible rules
-- in the focused calculus

foc2nf-Ie-focus : ∀{S Γ Δ C} (p : not⊸ C)
  → (f : S ∣ Γ ⊢L I) (g : nothing ∣ Δ ⊢L C) 
  → foc2nf (Ie-focus p f g) ≡ IeNf (foc2nf f) (foc2nf g)
foc2nf-Ie-focusR : ∀{S Γ Δ C} (p : not⊸ C)
  → (f : S ∣ Γ ⊢R I) (g : nothing ∣ Δ ⊢L C) 
  → foc2nf (Ie-focusR p f g) ≡ IeNf (foc2nfR f) (foc2nf g)

foc2nf-Ie-focus p (Il q f) g =
  trans (cong (Ie p (sp [])) (foc2nf-Ie-focus p f g))
    (Ie-gen-eq p _ _)
foc2nf-Ie-focus p (uf q f) g = foc2nf-Ie-focus p f g
foc2nf-Ie-focus p (switch refl r f) g = foc2nf-Ie-focusR p f g

foc2nf-Ie-focusR p Ir g = refl
foc2nf-Ie-focusR p (⊸l f f') g =
  sym (trans (IeNf⊸lNf (foc2nf f) (foc2nf f') (foc2nf g) refl)
    (cong (λ x → ⊸lNf (foc2nf f) x refl) (sym (foc2nf-Ie-focus p f' g))))

foc2nf-⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C)
  → foc2nf (⊸l-focus f g) ≡ ⊸lNf (foc2nf f) (foc2nf g) refl                   
foc2nf-⊸l-focus f (⊸r g) = cong ⊸i (foc2nf-⊸l-focus f g)
foc2nf-⊸l-focus f (Il p g) = refl
foc2nf-⊸l-focus f (switch p q g) = refl

foc2nf-uf-focus : {Γ : Cxt} → {A C : Fma}
  → (f : just A ∣ Γ ⊢L C)
  → foc2nf (uf-focus f) ≡ foc2nf f
foc2nf-uf-focus (⊸r f) = cong ⊸i (foc2nf-uf-focus f)
foc2nf-uf-focus (Il p f) = refl
foc2nf-uf-focus (switch p q f) = refl

foc2nf-ax-focus : ∀{A} → foc2nf (ax-focus {A}) ≡ nax
foc2nf-ax-focus {` X} = refl
foc2nf-ax-focus {I} = refl
foc2nf-ax-focus {A ⊸ B} =
  cong ⊸i (trans (foc2nf-⊸l-focus (uf-focus ax-focus) ax-focus)
    (trans (cong₂ (λ x y → ⊸lNf x y refl) (trans (foc2nf-uf-focus ax-focus) foc2nf-ax-focus) foc2nf-ax-focus)
      (⊸lNf-ne2nf nax [])))

-- Translating a term in normal form into the focused calculus and
-- then back to Nf is the identity.

foc2nf2foc : ∀{Γ C} (t : Γ ⊢Nf C)
  → foc2nf (nf2foc t) ≡ t
foc2sp2foc : ∀{Γ A B} (s : Sp Γ A B)
  → foc2nf (sp2foc s) ≡ ne2nf (sp s)

foc2nf2foc (⊸i t) = cong ⊸i (foc2nf2foc t)
foc2nf2foc Ii = refl
foc2nf2foc (Ie p (sp s) u) =
  trans (foc2nf-Ie-focus p (sp2foc s) (nf2foc u))
    (trans (cong₂ IeNf (foc2sp2foc s) (foc2nf2foc u))
      (sym (Ie-gen-eq p _ _)))
foc2nf2foc (switch (sp s)) = foc2sp2foc s  

foc2sp2foc [] = foc2nf-ax-focus
foc2sp2foc (f ∷ s) =
  trans (foc2nf-⊸l-focus (nf2foc f) (sp2foc s))
    (trans (cong₂ (λ x y → ⊸lNf x y refl) (foc2nf2foc f) (foc2sp2foc s))
      (⊸lNf-ne2nf f s))

-- Inverse of uf-1 in the focused calculus

uf-1-focus : {Γ : Cxt} → {A C : Fma}
  → nothing ∣ A ∷ Γ ⊢L C → just A ∣ Γ ⊢L C 
uf-1-focus (⊸r f) = ⊸r (uf-1-focus f)
uf-1-focus (uf p f) = f
uf-1-focus (switch {just _} () q f)

uf-1-uf-focus : {Γ : Cxt} → {A C : Fma}
  → (f : just A ∣ Γ ⊢L C)
  → uf-1-focus (uf-focus f) ≡ f
uf-1-uf-focus (⊸r f) = cong ⊸r (uf-1-uf-focus f)
uf-1-uf-focus (Il p f) = refl
uf-1-uf-focus (switch p q f) = refl  

-- An equality involving the admissible rules Ie-focuse and ⊸l-focus

Ie-focus⊸l-focus : ∀{Γ Δ Λ A B C} (p : not⊸ C)
  → (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L I) (h : nothing ∣ Λ ⊢L C)
  → Ie-focus p (⊸l-focus f g) h ≡ ⊸l-focus f (Ie-focus p g h)
Ie-focus⊸l-focus p f (Il q g) h = refl
Ie-focus⊸l-focus p f (switch {just _} refl r (⊸l g g')) h = refl

-- Relation between the translation nf2foc and other admissible rules
-- in Nf

nf2foc-⊸lNf : ∀{Γ Δ Δ' A B C} (t : Γ ⊢Nf A) (u : Δ' ⊢Nf C)
  → (eq : Δ' ≡ B ∷ Δ)
  → nf2foc (⊸lNf t u eq) ≡ uf-focus (⊸l-focus (nf2foc t) (uf-1-focus (nf2foc (subst (λ x → x ⊢Nf C) eq u))))
nf2foc-⊸lNf t (⊸i u) refl = cong ⊸r (nf2foc-⊸lNf t u refl)
nf2foc-⊸lNf t (Ie {B ∷ Γ} p (sp s) v) refl =
  trans (sym (uf-focus-eq p _))
    (cong uf-focus (Ie-focus⊸l-focus p (nf2foc t) (sp2foc s) (nf2foc v)))
nf2foc-⊸lNf t (switch (sp s)) refl = sym (uf-focus-eq tt _)


-- Translating a derivation in the focused calculus to Nf and then
-- back to the focused calculus is the identity.

nf2foc2nf-n : ∀{Γ C} (f : nothing ∣ Γ ⊢L C)
  → nf2foc (foc2nf f) ≡ f
nf2foc2nf-j : ∀{Γ A C} (f : just A ∣ Γ ⊢L C)
  → nf2foc (foc2nf f) ≡ uf-focus f
nf2focR2nf-n : ∀{Γ C} (f : nothing ∣ Γ ⊢R C) (q : not⊸ C)
  → nf2foc (foc2nfR f) ≡ switch refl q f
nf2focR2nf-j : ∀{Γ A C} (f : just A ∣ Γ ⊢R C) (q : not⊸ C)
  → nf2foc (foc2nfR f) ≡ uf q (switch refl q f)

nf2foc2nf-n (⊸r f) = cong ⊸r (nf2foc2nf-n f)
nf2foc2nf-n (uf p f) =
  trans (nf2foc2nf-j f)
    (uf-focus-eq p f)
nf2foc2nf-n (switch {nothing} refl q f) = nf2focR2nf-n f q

nf2foc2nf-j (⊸r f) = cong ⊸r (nf2foc2nf-j f)
nf2foc2nf-j (Il p f) = cong (λ x → uf p (Il p x)) (nf2foc2nf-n f)
nf2foc2nf-j (switch {just A} refl q f) = nf2focR2nf-j f q

nf2focR2nf-n Ir tt = refl

nf2focR2nf-j ax tt = refl
nf2focR2nf-j (⊸l f g) q =
  trans (nf2foc-⊸lNf (foc2nf f) (foc2nf g) refl)
    (trans (cong uf-focus (cong₂ ⊸l-focus (nf2foc2nf-n f) (cong uf-1-focus (nf2foc2nf-j g))))
      (trans (uf-focus-eq q _) (cong (uf q)
        (trans (cong (⊸l-focus f) (uf-1-uf-focus g))
          (⊸l-focus-eq q f g)))))
