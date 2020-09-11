{-# OPTIONS --rewriting #-}

module SeqCalc where

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
open import FreeSkewClosed

-- =======================================================================

-- Sequent calculus

-- -- (In addition to the conclusion, sequents have a stoup and a context.)

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C 
  Ir : nothing ∣ [] ⊢ I
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢ A → just B ∣ Δ ⊢ C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢ C

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- -- equality of proofs 

infixl 20 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'
  axI : ax ≗ Il Ir
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗ ⊸r (⊸l (uf ax) ax)
  ⊸ruf : {Γ : Cxt}{A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (uf f) ≗ uf (⊸r f)
  ⊸rIl : {Γ : Cxt}{B C : Fma} {f : nothing ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (Il f) ≗ Il (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl

-- ====================================================================

-- -- equational reasoning sugar for ≗

infix 4 _≗'_
infix 1 proof≗_
infixr 2 _≗〈_〉_
infix 3 _qed≗

data _≗'_ {S  : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≗ g → f ≗' g

proof≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} {f g : S ∣ Γ ⊢ A} → f ≗' g → f ≗ g
proof≗ relto p = p

_≗〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗' h → f ≗' h 
_ ≗〈 p 〉 relto q = relto (p ∙ q)

_qed≗  :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) → f ≗' f
_qed≗ _ = relto refl

-- ====================================================================

-- Il and ⊸r are invertible rules

Il-1 : {Γ : Cxt} → {C : Fma} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (⊸r f) = ⊸r (Il-1 f)
Il-1 (Il f) = f

⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ⊢ A ⊸ B → S ∣ Γ ++ A ∷ [] ⊢ B
⊸r-1 ax = ⊸l (uf ax) ax
⊸r-1 (uf f) = uf (⊸r-1 f)
⊸r-1 (⊸r f) = f
⊸r-1 (Il f) = Il (⊸r-1 f)
⊸r-1 (⊸l f g) = ⊸l f (⊸r-1 g)              

-- uf is invertible (i.e. left-normality holds)

uf-1 : {Γ : Cxt} → {A C : Fma} → 
            nothing ∣ A ∷ Γ ⊢ C  → just A ∣ Γ ⊢ C
uf-1 (uf f) = f
uf-1 (⊸r f) = ⊸r (uf-1 f)            

uf-iso : {Γ : Cxt} → {A C : Fma} 
  → (f : nothing ∣ A ∷ Γ ⊢ C) → uf (uf-1 f) ≗ f
uf-iso (uf f) = refl
uf-iso (⊸r f) = (~ ⊸ruf) ∙ ⊸r (uf-iso f)

Il-iso : {Γ : Cxt} → {C : Fma}
  → (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≗ f
Il-iso ax = ~ axI
Il-iso (⊸r f) = (~ ⊸rIl) ∙ ⊸r (Il-iso f)
Il-iso (Il f) = refl

⊸r-iso : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
  (f : S ∣ Γ ⊢ A ⊸ B) → ⊸r (⊸r-1 f) ≗ f
⊸r-iso ax = ~ ax⊸
⊸r-iso (uf f) = ⊸ruf ∙ uf (⊸r-iso f)
⊸r-iso (⊸r f) = refl
⊸r-iso (Il f) = ⊸rIl ∙ Il (⊸r-iso f)
⊸r-iso (⊸l f f₁) = ⊸r⊸l ∙ ⊸l refl (⊸r-iso f₁)

congIl-1 : {Γ : Cxt} {A : Fma} {f g : just I ∣ Γ ⊢ A}
  → f ≗ g → Il-1 f ≗ Il-1 g
congIl-1 refl = refl
congIl-1 (~ p) = ~ (congIl-1 p)
congIl-1 (p ∙ p₁) = (congIl-1 p) ∙ (congIl-1 p₁)
congIl-1 (⊸r p) = ⊸r (congIl-1 p)
congIl-1 (Il p) = p
congIl-1 axI = refl
congIl-1 ⊸rIl = refl

conguf-1 : {Γ : Cxt} → {A C : Fma} → 
            {f g : nothing ∣ A ∷ Γ ⊢ C}  → f ≗ g → uf-1 f ≗ uf-1 g
conguf-1 refl = refl
conguf-1 (~ p) = ~ (conguf-1 p)
conguf-1 (p ∙ p₁) = (conguf-1 p) ∙ (conguf-1 p₁)
conguf-1 (uf p) = p
conguf-1 (⊸r p) = ⊸r (conguf-1 p)
conguf-1 ⊸ruf = refl

cong⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              {f g : S ∣ Γ ⊢ A ⊸ B} → f ≗ g → ⊸r-1 f ≗ ⊸r-1 g
cong⊸r-1 refl = refl
cong⊸r-1 (~ p) = ~ (cong⊸r-1 p)
cong⊸r-1 (p ∙ p₁) = (cong⊸r-1 p) ∙ (cong⊸r-1 p₁)
cong⊸r-1 (uf p) = uf (cong⊸r-1 p)
cong⊸r-1 (⊸r p) = p
cong⊸r-1 (Il p) = Il (cong⊸r-1 p)
cong⊸r-1 (⊸l p p₁) = ⊸l p (cong⊸r-1 p₁)
cong⊸r-1 ax⊸ = refl
cong⊸r-1 ⊸ruf = refl
cong⊸r-1 ⊸rIl = refl
cong⊸r-1 ⊸r⊸l = refl

-- ====================================================================

-- Admissibility of cut
-- -- (There are two kinds of cut: stoup ccut and context cut.)

mutual 
  scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ ⊢ C  →  S ∣ Γ ++ Δ ⊢ C
  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut Ir g = Il-1 g
  scut (⊸r f) ax = ⊸r f
  scut (⊸r {Γ = Γ} f) (⊸l g g') = scut (ccut Γ g f refl) g'
  scut (⊸r f) (⊸r g) = ⊸r (scut (⊸r f) g)
  scut (Il f) g = Il (scut f g)
  scut (⊸l f f') g = ⊸l f (scut f' g)

  ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C
  ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
  ccut .[] f (uf g) r | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Γ₀) f (uf g) r | inj₂ (Γ₀ , p , refl) = uf (ccut Γ₀ f g p)
  ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut Δ₀ f (⊸r g) refl = ⊸r (ccut Δ₀ f g refl)
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ {Δ'} f (⊸l {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut Δ₀ f (⊸l g g') p | inj₁ (Γ₀ , r , refl) = ⊸l (ccut Δ₀ f g r) g'
  ccut ._ f (⊸l g g') p | inj₂ (Γ₀ , refl , refl) = ⊸l g (ccut Γ₀ f g' refl)

