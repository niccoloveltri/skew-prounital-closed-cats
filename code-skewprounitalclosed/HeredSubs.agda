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
open import Compare

-- =======================================================================
-- -- Natural deduction and hereditary substitutions
-- =======================================================================

infix 2 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A 
  uf : {Γ : Cxt} {A C : Fma}
    → just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C
  ⊸i : {S : Stp} {Γ : Cxt} {A B : Fma}
    → S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ⊸e : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
    → S ∣ Γ ⊢ A ⊸ B → nothing ∣ Δ ⊢ A → S ∣ Γ ++ Δ ⊢ B

subst-cxt : ∀{S}{Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f


-- Substitution is admissible

ssub : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢ A) (u : just A ∣ Δ ⊢ C)
  → S ∣ Γ ++ Δ ⊢ C
ssub t ax = t
ssub t (⊸i u) = ⊸i (ssub t u)
ssub t (⊸e u v) = ⊸e (ssub t u) v

csub : ∀{S Γ Δ} Δ₀ {Δ₁ A C} (t : nothing ∣ Γ ⊢ A) (u : S ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢ C
csub Δ₀ t ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
csub Δ₀ t (uf u) eq with cases∷ Δ₀ eq
csub .[] t (uf u) eq | inj₁ (refl , refl , refl) = ssub t u
csub .(_ ∷ Γ₀) t (uf u) eq | inj₂ (Γ₀ , refl , refl) = uf (csub Γ₀ t u refl)
csub Δ₀ t (⊸i u) refl = ⊸i (csub Δ₀ t u refl)
csub Δ₀ {Δ₁} t (⊸e {Γ = Γ} {Δ} u v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
csub Δ₀ t (⊸e u v) eq | inj₁ (Γ₀ , refl , refl) = ⊸e (csub Δ₀ t u refl) v
csub ._ t (⊸e u v) eq | inj₂ (Γ₀ , refl , refl) = ⊸e u (csub Γ₀ t v refl)

-- =======================================================================

infixl 20 _∙_
infix 21 ~_

-- Equational theory of terms

data _≑_ : {S : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{t : S ∣ Γ ⊢ A} → t ≑ t
  ~_ : ∀{S}{Γ}{A}{t u : S ∣ Γ ⊢ A} → t ≑ u → u ≑ t
  _∙_ : ∀{S}{Γ}{A}{t u v : S ∣ Γ ⊢ A} → t ≑ u → u ≑ v → t ≑ v
  uf : ∀{Γ}{A}{C}{t u : just A ∣ Γ ⊢ C} → t ≑ u → uf t ≑ uf u
  ⊸i : ∀{S}{Γ}{A}{B}{t u : S ∣ Γ ++ A ∷ [] ⊢ B} → t ≑ u → ⊸i t ≑ ⊸i u
  ⊸e : ∀{S}{Γ}{Δ}{A}{B}{t t' : S ∣ Γ ⊢ A ⊸ B}{u u' : nothing ∣ Δ ⊢ A}
    → t ≑ t' → u ≑ u' → ⊸e t u ≑ ⊸e t' u'
  beta : ∀{S}{Γ}{Δ}{A}{B} {t :  S ∣ Γ ++ A ∷ [] ⊢ B} {u : nothing ∣ Δ ⊢ A}
    → ⊸e (⊸i t) u ≑ csub Γ u t refl 
  eta : ∀{S}{Γ}{A}{B} {t : S ∣ Γ ⊢ A ⊸ B} → t ≑ ⊸i (⊸e t (uf ax))
  ⊸euf : ∀{Γ}{Δ}{A}{A'}{B}{t : just A' ∣ Γ ⊢ A ⊸ B}{u : nothing ∣ Δ ⊢ A}
    → ⊸e (uf t) u ≑ uf (⊸e t u)
  ⊸iuf : ∀{Γ}{A}{A'}{B}{t : just A' ∣ Γ ++ A ∷ [] ⊢ B}
    → ⊸i (uf t) ≑ uf (⊸i t)

≡-to-≑ : ∀{S Γ A} {t u : S ∣ Γ ⊢ A} → t ≡ u → t ≑ u
≡-to-≑ refl = refl



L2nd : ∀ {S Γ C} → S ∣ Γ ⊢L C → S ∣ Γ ⊢ C
R2nd : ∀ {S Γ Δ A C} → S ∣ Γ ⊢ A → A ∣ Δ ⊢R C → S ∣ Γ ++ Δ ⊢ C

L2nd (⊸r f) = ⊸i (L2nd f)
L2nd (uf f) = uf (L2nd f)
L2nd {just A} {C = ` X} (switch f) = R2nd ax f

R2nd f ax = f
R2nd f (⊸l g t) = R2nd (⊸e f (L2nd g)) t

-- -- Embedding neutrals into normal forms (i.e. eta expansion)

⊸eR : ∀{S Γ Δ B C} → S ∣ Γ ⊢R B ⊸ C → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢R C
⊸eR (⊸l t u) f = ⊸l t (⊸eR u f)
⊸eR ax f = ⊸l f ax

ufL : ∀{Γ A C} (f : just A ∣ Γ ⊢L C) → nothing ∣ A ∷ Γ ⊢L C
ufL (⊸r f) = ⊸r (ufL f)
ufL (switch f) = uf (switch f)

ufL-eq : ∀ {Γ A X}
  → (f : just A ∣ Γ ⊢L ` X)
  → ufL f ≡ uf f
ufL-eq (switch f) = refl

R2L : ∀{S Γ C} → S ∣ Γ ⊢R C → just S ∣ Γ ⊢L C
R2L {C = ` X} f = switch f
R2L {C = C ⊸ D} f = ⊸r (R2L (⊸eR {Δ = _ ∷ []} f (ufL (R2L ax))))

axL : ∀{A} → just A ∣ [] ⊢L A
axL = R2L ax

-- =======================================================================

-- Hereditary substitutions


ssubL : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢L A) (u : just A ∣ Δ ⊢L C)
  → S ∣ Γ ++ Δ ⊢L C
ssubR : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢L A) (u : A ∣ Δ ⊢R C)
  → S ∣ Γ ++ Δ ⊢L C
csubL : ∀{S Γ Δ} Δ₀ {Δ₁ A C} (t : nothing ∣ Γ ⊢L A) (u : S ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢L C
csubR : ∀{S Γ Δ} Δ₀ {Δ₁ A C} (t : nothing ∣ Γ ⊢L A) (u : S ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁) → S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢R C
⊸eL : ∀{S Γ Δ A B} → S ∣ Γ ⊢L A ⊸ B → nothing ∣ Δ ⊢L A
  → S ∣ Γ ++ Δ ⊢L B

ssubL t (⊸r u) = ⊸r (ssubL t u)
ssubL {C = ` X} t (switch f) = ssubR t f

ssubR t ax = t
ssubR {Γ = Γ} t (⊸l f u) = ssubR (⊸eL t f) u

csubL Δ₀ u (uf t) eq with cases∷ Δ₀ eq
... | inj₁ (refl , refl , refl) = ssubL u t 
... | inj₂ (Γ₀ , refl , refl) = uf (csubL Γ₀ u t refl)
csubL Δ₀ u (⊸r t) refl = ⊸r (csubL Δ₀ u t refl)
csubL Δ₀ u (switch f) refl = switch (csubR Δ₀ u f refl)

csubR Δ₀ u ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
csubR Δ₀ {Δ₁} u (⊸l {Γ} {Δ} f t) eq with cases++ Δ₀ Γ Δ₁ Δ eq
csubR Δ₀ u (⊸l f t) eq | inj₁ (Γ₀ , refl , refl) =
  ⊸l (csubL Δ₀ u f refl) t
csubR ._ u (⊸l f t) eq | inj₂ (Γ₀ , refl , refl) =
  ⊸l f (csubR Γ₀ u t refl)

⊸eL {Γ = Γ} (⊸r f) t = csubL Γ t f refl


-- The normalization function

nf : ∀{S Γ C} → S ∣ Γ ⊢ C → S ∣ Γ ⊢L C
nf ax = axL
nf (uf t) = ufL (nf t)
nf (⊸i t) = ⊸r (nf t)
nf (⊸e t u) = ⊸eL (nf t) (nf u)

-- =======================================================================

-- We show that nf is well-defined, i.e. it sends ≑-equivalent
-- terms to the same normal form.

csubL-⊸l : ∀{Γ Δ} Δ₀ {Δ₁ Λ A A' B' C} (t : nothing ∣ Γ ⊢L A)
  → (u : nothing ∣ Δ ⊢L A') (v : just B' ∣ Λ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL Δ₀ t (⊸l-focus u v) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq)
          ≡ ⊸l-focus (csubL Δ₀ t u eq) v
csubL-⊸l Δ₀ t u (⊸r v) refl = cong ⊸r (csubL-⊸l Δ₀ t u v refl)
csubL-⊸l Δ₀ {Δ₁} {Λ} {A} t u (switch f) refl
  rewrite cases++-inj₁ Δ₀ Δ₁ Λ A = refl

csubL-⊸l2 : ∀{Γ Δ} Δ₀ {Δ₁ Λ A A' B' C} (t : nothing ∣ Γ ⊢L A)
  → (u : nothing ∣ Λ ⊢L A') (v : just B' ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL (Λ ++ Δ₀) t (⊸l-focus u v) (cong (Λ ++_) eq)
          ≡ ⊸l-focus u (csubL Δ₀ t v eq)
csubL-⊸l2 Δ₀ t u (⊸r v) refl = cong ⊸r (csubL-⊸l2 Δ₀ t u v refl)
csubL-⊸l2 Δ₀ {Δ₁} {Λ} {A} t u (switch f) refl
  rewrite cases++-inj₂ Δ₀ Λ Δ₁ A = refl

ssubL-⊸r⊸l : ∀ {S Γ Δ Λ A B C}
  → (t : S ∣ Γ ++ A ∷ [] ⊢L B) (u : nothing ∣ Δ ⊢L A) (v : just B ∣ Λ ⊢L C) 
  → ssubL (⊸r t) (⊸l-focus u v)
          ≡ ssubL (csubL Γ u t refl) v
ssubL-⊸r⊸l t u (⊸r v) = cong ⊸r (ssubL-⊸r⊸l t u v)
ssubL-⊸r⊸l {C = ` X} t u (switch f) = refl

ssubL-⊸l : ∀ {Γ Δ Λ A A' B' C}
  → (t : nothing ∣ Γ ⊢L A') (u : just B' ∣ Δ ⊢L A) (v : just A ∣ Λ ⊢L C) 
  → ssubL (⊸l-focus t u) v ≡ ⊸l-focus t (ssubL u v)
ssubR-⊸l : ∀ {Γ Δ Λ A A' B' C}
  → (t : nothing ∣ Γ ⊢L A') (u : just B' ∣ Δ ⊢L A) (v : A ∣ Λ ⊢R C) 
  → ssubR (⊸l-focus t u) v ≡ ⊸l-focus t (ssubR u v)

ssubL-⊸l t u (⊸r v) = cong ⊸r (ssubL-⊸l t u v)
ssubL-⊸l {C = ` X} t u (switch f) = ssubR-⊸l t u f

ssubR-⊸l t u ax = refl
ssubR-⊸l {Γ} {Δ} t (⊸r u) (⊸l {Γ₁} f v) =
  trans (cong (λ x → ssubR {Γ = Γ ++ Δ ++ Γ₁} x v) (csubL-⊸l2 Δ f t u refl))
    (ssubR-⊸l t _ v)


csubL-uf : ∀{Γ Δ A C} (t : nothing ∣ Γ ⊢L A) (u : just A ∣ Δ ⊢L C)
  → csubL [] t (ufL u) refl ≡ ssubL t u
csubL-uf t (⊸r u) = cong ⊸r (csubL-uf t u)
csubL-uf t (switch f) = refl

ssubL-uf : ∀ {Γ Δ A A' C} (t : just A' ∣ Γ ⊢L A) (u : just A ∣ Δ ⊢L C) 
  → ssubL (ufL t) u ≡ ufL (ssubL t u)
ssubR-uf : ∀ {Γ Δ A A' C} (t : just A' ∣ Γ ⊢L A) (u : A ∣ Δ ⊢R C) 
  → ssubR (ufL t) u ≡ ufL (ssubR t u)
csubL-uf2 : ∀{Γ Δ} Δ₀ {Δ₁ A A' C}
  → (t : nothing ∣ Γ ⊢L A) (u : just A' ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL (_ ∷ Δ₀) t (ufL u) (cong (_ ∷_) eq)
          ≡ ufL (csubL Δ₀ t u eq)

ssubL-uf t (⊸r u) = cong ⊸r (ssubL-uf t u)
ssubL-uf {C = ` X} t (switch f) = ssubR-uf t f

ssubR-uf t ax = refl
ssubR-uf (⊸r {Γ = Γ} t) (⊸l {Γ = Γ'} f u) =
  trans (cong (λ x → ssubR {Γ = _ ∷ Γ ++ Γ'} x u) (csubL-uf2 Γ f t refl))
    (ssubR-uf (csubL Γ f t refl) u)

csubL-uf2 Δ₀ t (⊸r u) refl = cong ⊸r (csubL-uf2 Δ₀ t u refl)
csubL-uf2 Δ₀ t (switch f) refl = refl

csubL-⊸eR : ∀{Γ Δ Λ} Δ₀ {Δ₁ A A' B C}
  → (t : nothing ∣ Γ ⊢L A) (f : A' ∣ Δ ⊢R B ⊸ C) (u : nothing ∣ Λ ⊢L B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubR Δ₀ t (⊸eR f u) (cong (_++ Λ) {y =  Δ₀ ++ A ∷ Δ₁} eq) ≡
    ⊸eR (csubR Δ₀ t f eq) u 
csubL-⊸eR Δ₀ t ax u eq = ⊥-elim ([]disj∷ Δ₀ eq)
csubL-⊸eR Δ₀ {Δ₁} t (⊸l {Γ} {Δ} f g) u eq with cases++ Δ₀ Γ Δ₁ Δ eq
csubL-⊸eR {Λ = Λ} Δ₀ {A = A} t (⊸l {Δ = Δ} f g) u refl
  | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ Λ) A = refl
csubL-⊸eR {Λ = Λ} ._ {Δ₁} {A} t (⊸l {Γ} f g) u refl
  | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ₁ ++ Λ) A =
    cong (⊸l f) (csubL-⊸eR Γ₀ t g u refl)
 
csubL-R2L : ∀{Γ} Δ₀ {Δ₁ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : B ∣ Δ₀ ++ A ∷ Δ₁ ⊢R C)
  → csubL Δ₀ t (R2L u) refl ≡ R2L (csubR Δ₀ t u refl)
csubL-R2L Δ₀ {C = ` X} t u = refl
csubL-R2L Δ₀ {C = C ⊸ D} t u =
  cong ⊸r (trans (csubL-R2L Δ₀ t (⊸eR u (ufL (R2L ax))))
    (cong R2L (csubL-⊸eR Δ₀ t u (ufL (R2L ax)) refl)))

ssubRR : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢R A) (u : A ∣ Δ ⊢R C)
  → S ∣ Γ ++ Δ ⊢R C
ssubRR t ax = t
ssubRR t (⊸l f u) = ssubRR (⊸eR t f) u

ssubRR-⊸l : ∀{Γ Δ Λ A B C D}
  → (t : nothing ∣ Γ ⊢L A) (u : B ∣ Δ ⊢R C) (v : C ∣ Λ ⊢R D)
  → ssubRR (⊸l t u) v ≡ ⊸l t (ssubRR u v)
ssubRR-⊸l t u ax = refl
ssubRR-⊸l t u (⊸l f v) = ssubRR-⊸l t (⊸eR u f) v

ssubRR-ax : ∀ {Γ A C} (t : A ∣ Γ ⊢R C) → ssubRR ax t ≡ t 
ssubRR-ax ax = refl
ssubRR-ax (⊸l f t) =
  trans (ssubRR-⊸l f ax t)
    (cong (⊸l f) (ssubRR-ax t))

-- Unitality of substitution,i.e substituting with ax-focus is
-- identity and substituting into ax-focus is also identity.

csubL-ax : ∀ {S Δ} Δ₀ {Δ₁ A C} (t : S ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL Δ₀ (ufL axL) t eq ≡ subst (λ x → S ∣ x ⊢L C) eq t
csubR-ax : ∀ {S Δ} Δ₀ {Δ₁ A C} (t : S ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubR Δ₀ (ufL axL) t eq ≡ subst (λ x → S ∣ x ⊢R C) eq t
ssubL-ax : ∀ {Γ A C} (t : just A ∣ Γ ⊢L C) → ssubL axL t ≡ t 
ssubR-ax : ∀ {Γ A X} (t : A ∣ Γ ⊢R ` X) → ssubR axL t ≡ switch t 
ssubL-ax2 : ∀ {S Γ A} (t : S ∣ Γ ⊢L A) → ssubL t axL ≡ t
ssubR-R2L : ∀{Γ Δ A B C}
  → (t : A ∣ Γ ⊢R B) (u : B ∣ Δ ⊢R C)
  → ssubR (R2L t) u ≡ R2L (ssubRR t u)
csubR-⊸eR2 : ∀{Γ Λ A A' C}
  → (t : nothing ∣ Γ ⊢L A) (f : A' ∣ Λ ⊢R A ⊸ C) 
  → csubR Λ t (⊸eR f (ufL axL)) refl ≡ ⊸eR f t
ssubR-⊸eR : ∀{S Γ Δ A B C} (t : S ∣ Γ ⊢L A) (u : A ∣ Δ ⊢R B ⊸ C)
  → ⊸r {Γ = Γ ++ Δ} (ssubR t (⊸eR u (ufL axL))) ≡ ssubR t u
ssubL-R2L : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢L A) (u : A ∣ Δ ⊢R C)
  → ssubL t (R2L u) ≡ ssubR t u
etaL : ∀{S Γ A B} (t : S ∣ Γ ⊢L A ⊸ B)
  → t ≡ ⊸r (⊸eL t (ufL axL))

etaL (⊸r {Γ = Γ} t) = cong ⊸r (sym (csubL-ax Γ t refl))  

ssubR-⊸eR t ax = sym (etaL t)
ssubR-⊸eR t (⊸l f u) = ssubR-⊸eR (⊸eL t f) u

ssubL-R2L {C = ` X} t u = refl
ssubL-R2L {C = C ⊸ D} t u =
  trans (cong ⊸r (ssubL-R2L t (⊸eR u (ufL axL))))
    (ssubR-⊸eR t u)

csubR-⊸eR2 t ax =
  cong (λ x → ⊸l x ax) (trans (csubL-uf t axL)
    (ssubL-ax2 t))
csubR-⊸eR2 {A = A} t (⊸l {Γ} {Δ} f u)
  rewrite cases++-inj₂ Δ Γ [] A =
    cong (⊸l f) (csubR-⊸eR2 t u)

ssubR-R2L t ax = refl
ssubR-R2L {Γ} t (⊸l {Γ₁} f u) =
  trans (cong (λ x → ssubR {Γ = Γ ++ Γ₁} x u)
              (trans (csubL-R2L Γ f (⊸eR t (ufL (R2L ax))))
                (cong R2L (csubR-⊸eR2 f t))))
    (ssubR-R2L (⊸eR t f) u)

csubL-ax Δ₀ (⊸r t) refl =
  cong ⊸r (csubL-ax Δ₀ t refl)
csubL-ax Δ₀ (uf t) eq with cases∷ Δ₀ eq
csubL-ax ._ (uf t) refl | inj₁ (refl , refl , refl) =
  trans (ssubL-uf axL t)
    (trans (ufL-eq _) (cong uf (ssubL-ax t)))
csubL-ax ._ (uf t) refl | inj₂ (Γ₀ , refl , refl) =
  cong uf (csubL-ax Γ₀ t refl)
csubL-ax Δ₀ (switch f) refl =
  cong switch (csubR-ax Δ₀ f refl)

csubR-ax Δ₀ ax eq =  ⊥-elim ([]disj∷ Δ₀ eq)
csubR-ax Δ₀ {Δ₁} (⊸l {Γ} {Δ} f t) eq with cases++ Δ₀ Γ Δ₁ Δ eq
csubR-ax Δ₀ (⊸l f t) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → ⊸l {Γ = Δ₀ ++ _ ∷ Γ₀} x t) (csubL-ax Δ₀ f refl)
csubR-ax ._ (⊸l f t) refl | inj₂ (Γ₀ , refl , refl) =
  cong (⊸l f) (csubR-ax Γ₀ t refl)

ssubL-ax (⊸r t) = cong ⊸r (ssubL-ax t)
ssubL-ax {C = ` X} (switch f) = ssubR-ax f

ssubR-ax ax = refl
ssubR-ax (⊸l f t) =
  trans (cong (λ x → ssubR x t) (csubL-R2L [] f (⊸l (ufL axL) ax)))
    (trans (ssubR-R2L (⊸l (csubL [] f (ufL axL) refl) ax) t)
      (cong switch (trans (ssubRR-⊸l (csubL [] f (ufL axL) refl) ax t)
        (cong₂ ⊸l (trans (csubL-uf f axL) (ssubL-ax2 f))
                  (ssubRR-ax t)))))

ssubL-ax2 (⊸r {Γ = Γ} t) =
  cong ⊸r (trans (ssubL-R2L (⊸r t) (⊸l (ufL axL) ax))
    (csubL-ax Γ t refl))
ssubL-ax2 (uf t) = refl
ssubL-ax2 (switch f) = refl

-- More equations satisfyied by substitution in foc. calculus:
-- parallel substitutions commute;
-- associativity of substitution

csubL-par-csubL : ∀{S Γ Δ Λ} Δ₀ Δ₁ {Δ₂ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : nothing ∣ Λ ⊢L B) (v : S ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Δ₂)
  → csubL Δ₀ t (csubL (Δ₀ ++ A ∷ Δ₁) u v eq) refl ≡
     csubL (Δ₀ ++ Γ ++ Δ₁) u (csubL Δ₀ t v eq) refl
csubR-par-csubR : ∀{Γ Δ Λ} Δ₀ Δ₁ {Δ₂ A A' B C}
  → (t : nothing ∣ Γ ⊢L A) (u : nothing ∣ Λ ⊢L B) (s : A' ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁ ++ B ∷ Δ₂)
  → csubR Δ₀ t (csubR (Δ₀ ++ A ∷ Δ₁) u s eq) refl ≡
     csubR (Δ₀ ++ Γ ++ Δ₁) u (csubR Δ₀ t s eq) refl
csubL-par-ssubR : ∀{S Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : S ∣ Γ ⊢L A) (u : nothing ∣ Λ ⊢L B) (s : A ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁)
  → ssubR t (csubR Δ₀ u s eq)
          ≡ csubL (Γ ++ Δ₀) u (ssubR t s) (cong (Γ ++_) eq)
csubL-par-ssubL : ∀{S Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : S ∣ Γ ⊢L A) (u : nothing ∣ Λ ⊢L B) (s : just A ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁)
  → ssubL t (csubL Δ₀ u s eq)
          ≡ csubL (Γ ++ Δ₀) u (ssubL t s) (cong (Γ ++_) eq)
csubL-ass-ssubL : ∀{Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : nothing ∣ Δ ⊢L B) (s : just B ∣ Λ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → ssubL (csubL Δ₀ t u eq) s ≡
     csubL Δ₀ t (ssubL u s) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq)
csubL-ass-ssubR : ∀{S Γ Δ Λ} Δ₀ {Δ₁ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : S ∣ Δ ⊢L B) (s : B ∣ Λ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → ssubR (csubL Δ₀ t u eq) s ≡
     csubL Δ₀ t (ssubR u s) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq)
csubL-⊸eL2 : ∀{S Γ Δ} Δ₀ {Δ₁ Λ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : S ∣ Λ ⊢L B ⊸ C) (v : nothing ∣ Δ ⊢L B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL (Λ ++ Δ₀) t (⊸eL u v) (cong (Λ ++_) eq) ≡
     ⊸eL u (csubL Δ₀ t v eq)
csubL-⊸eL : ∀{S Γ Δ} Δ₀ {Δ₁ Λ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : S ∣ Δ ⊢L B ⊸ C) (v : nothing ∣ Λ ⊢L B)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL Δ₀ t (⊸eL u v) (cong (_++ Λ) {y = Δ₀ ++ A ∷ Δ₁} eq) ≡
     ⊸eL (csubL Δ₀ t u eq) v
csubL-ass-csubL : ∀{S Γ Δ Λ} Δ₀ {Δ₁ Λ₀ Λ₁ A B C}
  → (t : nothing ∣ Γ ⊢L A) (u : nothing ∣ Δ ⊢L B) (v : S ∣ Λ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → (eq2 : Λ ≡ Λ₀ ++ B ∷ Λ₁)
  → csubL (Λ₀ ++ Δ₀) t (csubL Λ₀ u v eq2) (cong (λ x → Λ₀ ++ x ++ Λ₁) eq)
          ≡ csubL Λ₀ (csubL Δ₀ t u eq) v eq2
csubR-ass-csubR : ∀{Γ Δ Λ} Δ₀ {Δ₁ Λ₀ Λ₁ A A' B C}
  → (t : nothing ∣ Γ ⊢L A) (u : nothing ∣ Δ ⊢L B) (s : A' ∣ Λ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → (eq2 : Λ ≡ Λ₀ ++ B ∷ Λ₁)
  → csubR (Λ₀ ++ Δ₀) t (csubR Λ₀ u s eq2) (cong (λ x → Λ₀ ++ x ++ Λ₁) eq)
          ≡ csubR Λ₀ (csubL Δ₀ t u eq) s eq2

csubL-ass-csubL Δ₀ t u (⊸r v) refl refl =
  cong ⊸r (csubL-ass-csubL Δ₀ t u v refl refl)
csubL-ass-csubL Δ₀ {Λ₀ = Λ₀} t u (uf v) refl eq2 with cases∷ Λ₀ eq2
... | inj₁ (refl , refl , refl) = sym (csubL-ass-ssubL Δ₀ t u v refl)
... | inj₂ (Γ₀ , refl , refl) = cong uf (csubL-ass-csubL Δ₀ t u v refl refl)
csubL-ass-csubL Δ₀ t u (switch v) refl refl =
  cong switch (csubR-ass-csubR Δ₀ t u v refl refl)

csubR-ass-csubR Δ₀ t u ax eq eq2 =  ⊥-elim ([]disj∷ _ eq2)
csubR-ass-csubR Δ₀ {Λ₀ = Λ₀} {Λ₁} t u (⊸l {Γ} {Δ} f s) eq eq2
  with cases++ Λ₀ Γ Λ₁ Δ eq2
csubR-ass-csubR {Γ} Δ₀ {Δ₁} {Λ₀} {A = A} t u (⊸l {Δ = Δ} f s) refl refl
  | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Λ₀ ++ Δ₀) (Δ₁ ++ Γ₀) Δ A =
    cong (λ x → ⊸l {Λ₀ ++ Δ₀ ++ Γ ++ Δ₁ ++ Γ₀} x s)
      (csubL-ass-csubL Δ₀ t u f refl refl)
csubR-ass-csubR Δ₀ {Δ₁} {Λ₁ = Λ₁} {A} t u (⊸l {Γ} f s) refl refl
  | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Γ₀ ++ Δ₀) Γ (Δ₁ ++ Λ₁) A =
    cong (⊸l f) (csubR-ass-csubR Δ₀ t u s refl refl)

csubL-ass-ssubR Δ₀ t u ax refl = refl
csubL-ass-ssubR {_}{Γ} Δ₀ {Δ₁} t u (⊸l {Γ₁} f s) refl =
  trans (cong (λ x → ssubR {Γ = Δ₀ ++ Γ ++ Δ₁ ++ Γ₁} x s)
              (sym (csubL-⊸eL Δ₀ t u f refl)))
    (csubL-ass-ssubR Δ₀ t (⊸eL u f) s refl)

csubL-par-csubL Δ₀ Δ₁ t u (⊸r v) refl =
  cong ⊸r (csubL-par-csubL Δ₀ Δ₁ t u v refl)
csubL-par-csubL Δ₀ Δ₁ t u (uf v) eq with cases∷ Δ₀ eq
csubL-par-csubL .[] Δ₁ t u (uf v) refl | inj₁ (refl , refl , refl) =
  csubL-par-ssubL Δ₁ t u v refl
csubL-par-csubL .(_ ∷ Γ₀) Δ₁ t u (uf v) refl | inj₂ (Γ₀ , refl , refl) =
  cong uf (csubL-par-csubL Γ₀ Δ₁ t u v refl)
csubL-par-csubL Δ₀ Δ₁ t u (switch v) refl =
  cong switch (csubR-par-csubR Δ₀ Δ₁ t u v refl)

csubR-par-csubR Δ₀ Δ₁ t u ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
csubR-par-csubR Δ₀ Δ₁ {Δ₂} {A} {B = B} t u (⊸l {Γ} {Δ} f s) eq
  with cases++ (Δ₀ ++ A ∷ Δ₁) Γ Δ₂ Δ eq
csubR-par-csubR {Γ} {Λ = Λ} Δ₀ Δ₁ {A = A} {B = B} t u (⊸l {Δ = Δ} f s) refl
  | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Λ ++ Γ₀) Δ A
        | cases++-inj₁ Δ₀ (Δ₁ ++ B ∷ Γ₀) Δ A
        | cases++-inj₁ (Δ₀ ++ Γ ++ Δ₁) Γ₀ Δ B =
    cong (λ x → ⊸l {Δ₀ ++ Γ ++ Δ₁ ++ Λ ++ Γ₀} x s)
      (csubL-par-csubL Δ₀ Δ₁ t u f refl)
csubR-par-csubR Δ₀ Δ₁ {Δ₂} {A} {B = B} t u (⊸l {Γ} f s) eq
  | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
csubR-par-csubR {Γ} {Λ = Λ} Δ₀ ._ {Δ₂} {A} {B = B} t u (⊸l f s) refl
  | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ Λ ++ Δ₂) A
        | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ B ∷ Δ₂) A
        | cases++-inj₂ Γ₀ (Δ₀ ++ Γ ++ Γ₀') Δ₂ B = refl
csubR-par-csubR {Γ₁} {Λ = Λ} ._ Δ₁ {Δ₂} {A} {B = B} t u (⊸l {Γ} f s) refl
  | inj₂ (._ , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ Λ ++ Δ₂) A
        | cases++-inj₂ Γ₀' Γ (Δ₁ ++ B ∷ Δ₂) A
        | cases++-inj₂ (Γ₀' ++ Γ₁ ++ Δ₁) Γ Δ₂ B =
    cong (⊸l f) (csubR-par-csubR Γ₀' Δ₁ t u s refl)

csubL-par-ssubR Δ₀ t u ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
csubL-par-ssubR Δ₀ {Δ₁} t u (⊸l {Γ} {Δ} f s) eq with cases++ Δ₀ Γ Δ₁ Δ eq
csubL-par-ssubR {Γ = Γ} {Λ = Λ} Δ₀ t u (⊸l f s) refl
  | inj₁ (Γ₀ , refl , refl) =
  trans (cong (λ x → ssubR {Γ = Γ ++ Δ₀ ++ Λ ++ Γ₀} x s)
              (sym (csubL-⊸eL2 Δ₀ u t f refl)))
    (csubL-ass-ssubR (Γ ++ Δ₀) u (⊸eL t f) s refl )
csubL-par-ssubR ._ t u (⊸l f s) refl | inj₂ (Γ₀ , refl , refl) =
  csubL-par-ssubR Γ₀ (⊸eL t f) u s refl

csubL-⊸eL2 Δ₀ {Δ₁} t (⊸r u) v refl = csubL-ass-csubL Δ₀ t v u refl refl

csubL-⊸eL Δ₀ {Δ₁} t (⊸r u) v refl = csubL-par-csubL Δ₀ Δ₁ t v u refl

csubL-ass-ssubL Δ₀ t u (⊸r v) refl =
  cong ⊸r (csubL-ass-ssubL Δ₀ t u v refl)
csubL-ass-ssubL Δ₀ t u (switch f) refl =
  csubL-ass-ssubR Δ₀ t u f refl

csubL-par-ssubL Δ₀ t u (⊸r v) refl =
  cong ⊸r (csubL-par-ssubL Δ₀ t u v refl)
csubL-par-ssubL Δ₀ t u (switch f) refl =
  csubL-par-ssubR Δ₀ t u f refl

ssubL-⊸e2 : ∀{S Γ Δ Λ A' A B}
  → (t : S ∣ Γ ⊢L A') (u : just A' ∣ Δ ⊢L A ⊸ B) (v : nothing ∣ Λ ⊢L A)
  → ssubL t (⊸eL u v) ≡ ⊸eL (ssubL t u) v
ssubL-⊸e2 {Δ = Δ} t (⊸r u) v = csubL-par-ssubL Δ t v u refl 

-- A key lemma: substitution commutes with normalization


ssub-nf : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢ A) (u : just A ∣ Δ ⊢ C)
  → ssubL (nf t) (nf u) ≡ nf (ssub t u)
ssub-nf t ax = ssubL-ax2 _
ssub-nf t (⊸i u) = cong ⊸r (ssub-nf t u)
ssub-nf {Γ = Γ} t (⊸e {Γ = Δ} u v) =
  trans (ssubL-⊸e2 (nf t) (nf u) (nf v))
    (cong (λ x → ⊸eL {Γ = Γ ++ Δ} x (nf v)) (ssub-nf t u))

csub-nf : ∀{S Γ Δ} Δ₀ {Δ₁ A C} (t : nothing ∣ Γ ⊢ A) (u : S ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → csubL Δ₀ (nf t) (nf u) eq ≡ nf (csub Δ₀ t u eq)
csub-nf Δ₀ t ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
csub-nf Δ₀ t (uf u) eq with cases∷ Δ₀ eq
csub-nf .[] t (uf u) refl | inj₁ (refl , refl , refl) =
  trans (csubL-uf (nf t) (nf u))
    (ssub-nf t u)
csub-nf .(_ ∷ Γ₀) t (uf u) refl | inj₂ (Γ₀ , refl , refl) =
  trans (csubL-uf2 Γ₀ (nf t) (nf u) refl)
    (cong ufL (csub-nf Γ₀ t u refl))
csub-nf Δ₀ t (⊸i u) refl =
  cong ⊸r (csub-nf Δ₀ t u refl)
csub-nf Δ₀ {Δ₁} t (⊸e {Γ = Γ} {Δ} u u₁) eq with cases++ Δ₀ Γ Δ₁ Δ eq
csub-nf {Γ = Γ} Δ₀ t (⊸e u v) refl | inj₁ (Γ₀ , refl , refl) =
  trans (csubL-⊸eL Δ₀ (nf t) (nf u) (nf v) refl)
    (cong (λ x → ⊸eL {Γ = Δ₀ ++ Γ ++ Γ₀} x (nf v)) (csub-nf Δ₀ t u refl))
csub-nf ._ t (⊸e u v) refl | inj₂ (Γ₀ , refl , refl) =
  trans (csubL-⊸eL2 Γ₀ (nf t) (nf u) (nf v) refl)
    (cong (⊸eL (nf u)) (csub-nf Γ₀ t v refl))

-- nf sends ≑-equivalent terms to the same normal form.

⊸eufL : ∀{Γ Δ A A' B}
  → (t : just A' ∣ Γ ⊢L A ⊸ B) (u : nothing ∣ Δ ⊢L A)
  → ⊸eL (ufL t) u ≡ ufL (⊸eL t u)
⊸eufL (⊸r {Γ = Γ} t) u = csubL-uf2 Γ u t refl

congnf : ∀{S Γ C} {t u : S ∣ Γ ⊢ C} → t ≑ u → nf t ≡ nf u
congnf refl = refl
congnf (~ p) = sym (congnf p)
congnf (p ∙ p₁) = trans (congnf p) (congnf p₁)
congnf (⊸i p) = cong ⊸r (congnf p)
congnf (⊸e p p₁) = cong₂ ⊸eL (congnf p) (congnf p₁)
congnf (beta {Γ = Γ} {t = t} {u}) = csub-nf Γ u t refl
congnf {t = t} eta = etaL (nf t)
congnf (uf p) = cong ufL (congnf p)
congnf (⊸euf {t = t} {u}) = ⊸eufL (nf t) (nf u)
congnf ⊸iuf = refl

-- =======================================================================

-- We show that each term is equivalent to the embedding of its normal
-- form

-- First, some auxiliary equalities about embeddings L2nd and R2nd

R2nd-⊸eR : ∀ {S Γ Δ Λ A B C}
  → (t : S ∣ Γ ⊢ A) (u : A ∣ Δ ⊢R B ⊸ C) (n : nothing ∣ Λ ⊢L B)
  → R2nd t (⊸eR u n) ≡ ⊸e (R2nd t u) (L2nd n)
R2nd-⊸eR t ax n = refl
R2nd-⊸eR t (⊸l u v) n = R2nd-⊸eR (⊸e t (L2nd u)) v n

congR2nd : ∀ {S Γ Δ A B} {t u : S ∣ Γ ⊢ A} → t ≑ u
  → (v : A ∣ Δ ⊢R B) → R2nd t v ≑ R2nd u v
congR2nd eq ax = eq
congR2nd eq (⊸l f v) = congR2nd (⊸e eq refl) v

R2nd-csub : ∀{S Γ  Δ₀ Δ₁ Λ A B C}
  → (t : nothing ∣ Γ ⊢ A) (u : S ∣ Δ₀ ++ A ∷ Δ₁ ⊢ B) (v : B ∣ Λ ⊢R C)
  → R2nd (csub Δ₀ t u refl) v ≑ csub Δ₀ t (R2nd u v) refl
R2nd-csub t u ax = refl
R2nd-csub t u (⊸l f v) with R2nd-csub t (⊸e u (L2nd f)) v
R2nd-csub {Δ₀ = Δ₀} {Δ₁} {A = A} t u (⊸l {Γ} f v) | ih
  rewrite cases++-inj₁ Δ₀ Δ₁ Γ A = ih


-- -- Another key lemma: substitution commutes with embedding.

L2nd-ssubL : ∀{S Γ Δ A C} (t : S ∣ Γ ⊢L A) (u : just A ∣ Δ ⊢L C)
  → L2nd (ssubL t u) ≑ ssub (L2nd t) (L2nd u)
L2nd-ssubR : ∀{S Γ Δ A C}
  → (t : S ∣ Γ ⊢L A) (u : A ∣ Δ ⊢R C)
  → L2nd (ssubR t u) ≑ R2nd (L2nd t) u
R2nd-ssubR : ∀{S Γ Δ Λ A B C}
  → (t : S ∣ Γ ⊢L A) (u : just A ∣ Δ ⊢ B) (v : B ∣ Λ ⊢R C)
  → R2nd (ssub (L2nd t) u) v ≑ ssub (L2nd t) (R2nd u v)
L2nd-csubL : ∀{S Γ Δ} Δ₀ {Δ₁ A C} (t : nothing ∣ Γ ⊢L A) (u : S ∣ Δ ⊢L C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → L2nd (csubL Δ₀ t u eq) ≑ csub Δ₀ (L2nd t) (L2nd u) eq
L2nd-⊸eL : ∀{S Γ Δ A B} (t : S ∣ Γ ⊢L A ⊸ B) (u : nothing ∣ Δ ⊢L A)
  → L2nd (⊸eL t u) ≑ ⊸e (L2nd t) (L2nd u)
R2nd-csubR : ∀{Γ Δ} Δ₀ {Δ₁ Λ A A' B C}
  → (t : just A' ∣ Γ ⊢ B) (u : nothing ∣ Λ ⊢L A) (v : B ∣ Δ ⊢R C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → R2nd t (csubR Δ₀ u v eq)
         ≑ csub (Γ ++ Δ₀) (L2nd u) (R2nd t v) (cong (Γ ++_) eq)

L2nd-ssubL t (⊸r u) = ⊸i (L2nd-ssubL t u)
L2nd-ssubL {C = ` X} t (switch f) =
  L2nd-ssubR t f ∙ R2nd-ssubR t ax f

L2nd-ssubR t ax = refl
L2nd-ssubR t (⊸l f u) =
  L2nd-ssubR (⊸eL t f) u
  ∙ congR2nd (L2nd-⊸eL t f) u

R2nd-ssubR t u ax = refl
R2nd-ssubR t u (⊸l f v) = R2nd-ssubR t (⊸e u (L2nd f)) v

L2nd-csubL Δ₀ t (⊸r u) refl = ⊸i (L2nd-csubL Δ₀ t u refl)
L2nd-csubL Δ₀ t (uf u) eq with cases∷ Δ₀ eq
... | inj₁ (refl , refl , refl) = L2nd-ssubL t u
... | inj₂ (Γ₀ , refl , refl) = uf (L2nd-csubL Γ₀ t u refl)
L2nd-csubL {just A} Δ₀ {C = ` X} t (switch f) refl =
  R2nd-csubR Δ₀ ax t f refl

L2nd-⊸eL {Γ = Γ} (⊸r t) u =
  L2nd-csubL Γ u t refl ∙ ~ beta

R2nd-csubR Δ₀ t u ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
R2nd-csubR Δ₀ {Δ₁} t u (⊸l {Γ} {Δ} f v) eq with cases++ Δ₀ Γ Δ₁ Δ eq
R2nd-csubR {Γ} Δ₀ {A = A} t u (⊸l f v) refl | inj₁ (Γ₀ , refl , refl)
  with R2nd-csub {Δ₀ = Γ ++ Δ₀} (L2nd u) (⊸e t (L2nd f)) v
... | ih rewrite cases++-inj₂ Δ₀ Γ Γ₀ A =
  congR2nd (⊸e refl (L2nd-csubL Δ₀ u f refl)) v ∙ ih
R2nd-csubR ._ t u (⊸l f v) refl | inj₂ (Γ₀ , refl , refl) =
  R2nd-csubR Γ₀ (⊸e t (L2nd f)) u v refl

-- Each term is equivalent to the embedding of its normal form

L2nd-uf : ∀{Γ A C} (t : just A ∣ Γ ⊢L C)
  → L2nd (ufL t) ≑ uf (L2nd t)
L2nd-uf (⊸r t) =
  ⊸i (L2nd-uf t)
  ∙ ⊸iuf
L2nd-uf (switch f) = refl

L2nd-R2L : ∀{S Γ C} (t : S ∣ Γ ⊢R C) → L2nd (R2L t) ≑ R2nd ax t
L2nd-R2L {C = ` X} t = refl
L2nd-R2L {C = C ⊸ D} t =
  ⊸i (L2nd-R2L _
      ∙ ≡-to-≑ (R2nd-⊸eR ax t (ufL axL))
      ∙ ⊸e refl (L2nd-uf axL ∙ uf (L2nd-R2L ax)))
  ∙ ~ eta


L2nd-nf : ∀{S Γ C} (t : S ∣ Γ ⊢ C) → L2nd (nf t) ≑ t
L2nd-nf ax = L2nd-R2L ax
L2nd-nf (uf t) =
  L2nd-uf (nf t) ∙ uf (L2nd-nf t)
L2nd-nf (⊸i t) = ⊸i (L2nd-nf t)
L2nd-nf (⊸e t u) =
  L2nd-⊸eL (nf t) (nf u)
  ∙ ⊸e (L2nd-nf t) (L2nd-nf u)


-- =======================================================================

-- Each normal form is equal to the normalization of its embedding.

nf-L2nd : ∀{S Γ C} (n : S ∣ Γ ⊢L C) → nf (L2nd n) ≡ n
nf-R2nd : ∀{S Γ Δ A B} (n : S ∣ Γ ⊢ A) (u : A ∣ Δ ⊢R B)
  → nf (R2nd n u) ≡ ssubR (nf n) u

nf-L2nd (⊸r n) = cong ⊸r (nf-L2nd n)
nf-L2nd (uf n) =
  trans (ufL-eq _) (cong uf (nf-L2nd n))
nf-L2nd (switch f) =
  trans (nf-R2nd ax f) (ssubR-ax f)

nf-R2nd n ax = refl
nf-R2nd n (⊸l f t) =
  trans (nf-R2nd (⊸e n (L2nd f)) t)
    (cong (λ x → ssubR (⊸eL (nf n) x) t) (nf-L2nd f))

