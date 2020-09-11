{-# OPTIONS --rewriting #-}

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
open import SeqCalc

-- =======================================================================

-- focused sequent calculus

not⊸-isprop : (A : Fma) (p q : not⊸ A) → p ≡ q
not⊸-isprop (` X) tt tt = refl


mutual
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
    uf : {Γ : Cxt} → {A C : Fma} → 
              (p : not⊸ C) →
              (f : just A ∣ Γ ⊢L C) →
              nothing ∣ A ∷ Γ ⊢L C
    switch :  {S : Stp} → 
              {Γ : Cxt} → {C : Fma} →
              (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → S ∣ Γ ⊢L C

  data _∣_⊢R_ : Stp → Cxt → Fma → Set where
    ax : {X : At} → just (` X) ∣ [] ⊢R ` X
    ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) → (g : just B ∣ Δ ⊢L C) →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢R C

-- ====================================================================

-- embedding focused derivations into general derivations

mutual
  embL : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢L A → S ∣ Γ ⊢ A
  embL (⊸r f) = ⊸r (embL f)
  embL (uf p f) = uf (embL f)
  embL (switch q f) = embR f

  embR : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢R A → S ∣ Γ ⊢ A
  embR ax = ax
  embR (⊸l f g) = ⊸l (embL f) (embL g)

-- ====================================================================

-- the focusing function 


-- admissibility of unrestricted uf

uf-focus : {Γ : Cxt} → {A C : Fma} →
          just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
uf-focus (⊸r f) = ⊸r (uf-focus f)
uf-focus (switch p f) = uf p (switch p f)

uf-focus-eq : {Γ : Cxt} → {A C : Fma} →
          (p : not⊸ C) (f : just A ∣ Γ ⊢L C) →
          uf-focus f ≡ uf p f
uf-focus-eq {C = C} p (switch r f) rewrite not⊸-isprop C p r = refl

-- admissibility of unrestricted ⊸l

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (switch p g) = switch p (⊸l f (switch p g))

⊸l-focus-eq : {Γ Δ : Cxt} → {A B C : Fma} →
              (p : not⊸ C) (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C) → 
              ⊸l-focus f g ≡ switch p (⊸l f g)
⊸l-focus-eq {C = C} p f (switch q g) rewrite not⊸-isprop C p q = refl

-- admissibility of unrestricted ax

ax-focus : {A : Fma} → just A ∣ [] ⊢L A
ax-focus {` X} = switch _ ax
ax-focus {A ⊸ B} = ⊸r (⊸l-focus (uf-focus (ax-focus {A})) (ax-focus {B}))

-- the focusing function itself

focus : ∀{S}{Γ}{A} → S ∣ Γ ⊢ A → S ∣ Γ ⊢L A
focus ax = ax-focus
focus (uf f) = uf-focus (focus f)
focus (⊸r f) = ⊸r (focus f)
focus (⊸l f g) = ⊸l-focus (focus f) (focus g)

congfocus : ∀{S}{Γ}{A} {f g : S ∣ Γ ⊢ A} → f ≗ g → focus f ≡ focus g
congfocus refl = refl
congfocus (~ p) = sym (congfocus p)
congfocus (p ∙ p₁) = trans (congfocus p) (congfocus p₁)
congfocus (uf p) = cong uf-focus (congfocus p)
congfocus (⊸r p) = cong ⊸r (congfocus p)
congfocus (⊸l p p₁) = cong₂ ⊸l-focus (congfocus p) (congfocus p₁)
congfocus ax⊸ = refl
congfocus ⊸ruf = refl
congfocus ⊸r⊸l = refl

-- ====================================================================

-- focus after embL is identity

mutual 
  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              (f : S ∣ Γ ⊢L C) → focus (embL f) ≡ f
  focus-embL (⊸r f) = cong ⊸r (focus-embL f)
  focus-embL (uf p f) = trans (cong uf-focus (focus-embL f)) (uf-focus-eq p f)
  focus-embL (switch q f) = focus-embR q f

  focus-embR : {S : Stp} → {Γ : Cxt} → {C : Fma} (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → focus (embR f) ≡ switch q f
  focus-embR tt ax = refl
  focus-embR q (⊸l f g) = trans (cong₂ ⊸l-focus (focus-embL f) (focus-embL g)) (⊸l-focus-eq q f g)


embL-uf-focus : {Γ : Cxt} → {A C : Fma} →
          (f : just A ∣ Γ ⊢L C) →
          embL (uf-focus f) ≗ uf (embL f)
embL-uf-focus (⊸r f) = ⊸r (embL-uf-focus f) ∙ ⊸ruf
embL-uf-focus (switch p f) = refl

embL-⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C) →
              embL (⊸l-focus f g) ≗ ⊸l (embL f) (embL g)
embL-⊸l-focus f (⊸r g) = ⊸r (embL-⊸l-focus f g) ∙ ⊸r⊸l
embL-⊸l-focus f (switch p g) = refl

embL-ax-focus : {C : Fma} → embL ax-focus ≗ ax {C}
embL-ax-focus {` X} = refl
embL-ax-focus {B ⊸ C} =
  proof≗
    ⊸r (embL (⊸l-focus (uf-focus ax-focus) ax-focus))
  ≗〈 ⊸r (embL-⊸l-focus (uf-focus ax-focus) ax-focus) 〉
    ⊸r (⊸l (embL (uf-focus ax-focus)) (embL ax-focus))
  ≗〈 ⊸r (⊸l (embL-uf-focus ax-focus) refl) 〉
    ⊸r (⊸l (uf (embL ax-focus)) (embL ax-focus))
  ≗〈 ⊸r (⊸l (uf embL-ax-focus) embL-ax-focus) 〉
    ⊸r (⊸l (uf ax) ax)
  ≗〈 ~ ax⊸ 〉
    ax
  qed≗

embL-focus : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              (f : S ∣ Γ ⊢ C) → embL (focus f) ≗ f
embL-focus ax = embL-ax-focus
embL-focus (uf f) = embL-uf-focus (focus f) ∙ uf (embL-focus f)
embL-focus (⊸r f) = ⊸r (embL-focus f)
embL-focus (⊸l f g) = embL-⊸l-focus (focus f) (focus g) ∙ ⊸l (embL-focus f) (embL-focus g)


