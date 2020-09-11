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
open import FreeSkewClosed
open import SeqCalc

-- =======================================================================

-- focused sequent calculus

data At⊸ : Set where
  ` : At → At⊸
  _⊸_ : (A B : Fma) → At⊸

`⊸ : At⊸ → Fma
`⊸ (` X) = ` X
`⊸ (A ⊸ B) = A ⊸ B

StpR : Set
StpR = Maybe At⊸

not⊸-isprop : (A : Fma) (p q : not⊸ A) → p ≡ q
not⊸-isprop (` X) tt tt = refl
not⊸-isprop I tt tt = refl

mutual
  data _∣_⊢L_ : Stp → Cxt → Fma → Set where
    ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
    Il : {Γ : Cxt} → {C : Fma} → 
              (p : not⊸ C) →
              (f : nothing ∣ Γ ⊢L C) →
              just I ∣ Γ ⊢L C 
    uf : {Γ : Cxt} → {A C : Fma} → 
              (p : not⊸ C) →
              (f : just A ∣ Γ ⊢L C) →
              nothing ∣ A ∷ Γ ⊢L C
    switch :  {S : StpR} → {T : Stp} → (p : mmap `⊸ S ≡ T) → 
              {Γ : Cxt} → {C : Fma} →
              (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → T ∣ Γ ⊢L C

  data _∣_⊢R_ : StpR → Cxt → Fma → Set where
    ax : {X : At} → just (` X) ∣ [] ⊢R ` X
    Ir : nothing ∣ [] ⊢R I
    ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) → (g : just B ∣ Δ ⊢L C) →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢R C

-- ====================================================================

-- embedding focused derivations into general derivations

mutual
  embL : {S : Stp} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢L A → S ∣ Γ ⊢ A
  embL (⊸r f) = ⊸r (embL f)
  embL (uf p f) = uf (embL f)
  embL (Il p f) = Il (embL f)
  embL (switch {just (` X)} refl q f) = embR f
  embL (switch {just (A ⊸ B)} refl q f) = embR f
  embL (switch {nothing} refl q f) = embR f

  embR : {S : StpR} {Γ : Cxt} {A : Fma} → S ∣ Γ ⊢R A → mmap `⊸ S ∣ Γ ⊢ A
  embR ax = ax
  embR Ir = Ir
  embR (⊸l f g) = ⊸l (embL f) (embL g)

-- ====================================================================

-- the focusing function 

-- admissibility of unrestricted Il

Il-focus : {Γ : Cxt} → {C : Fma} → 
          nothing ∣ Γ ⊢L C → just I ∣ Γ ⊢L C 
Il-focus (uf p f) = Il p (uf p f)
Il-focus (⊸r f) = ⊸r (Il-focus f)
Il-focus (switch p q f) = Il q (switch p q f)

Il-focus-eq : {Γ : Cxt} → {C : Fma} → 
              (p : not⊸ C) (f : nothing ∣ Γ ⊢L C) →
              Il-focus f ≡ Il p f
Il-focus-eq {C = C} p (uf q f) rewrite not⊸-isprop C p q = refl
Il-focus-eq {C = C} p (switch r q f) rewrite not⊸-isprop C p q = refl
              

-- admissibility of unrestricted uf

uf-focus : {Γ : Cxt} → {A C : Fma} →
          just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
uf-focus (Il p f) = uf p (Il p f)
uf-focus (⊸r f) = ⊸r (uf-focus f)
uf-focus (switch p q f) = uf q (switch p q f)

uf-focus-eq : {Γ : Cxt} → {A C : Fma} →
          (p : not⊸ C) (f : just A ∣ Γ ⊢L C) →
          uf-focus f ≡ uf p f
uf-focus-eq {C = C} p (Il q f) rewrite not⊸-isprop C p q = refl
uf-focus-eq {C = C} p (switch r q f) rewrite not⊸-isprop C p q = refl

-- admissibility of unrestricted ⊸l

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (Il p g) = switch refl p (⊸l f (Il p g))
⊸l-focus f (switch p q g) = switch refl q (⊸l f (switch p q g))

⊸l-focus-eq : {Γ Δ : Cxt} → {A B C : Fma} →
              (p : not⊸ C) (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C) → 
              ⊸l-focus f g ≡ switch refl p (⊸l f g)
⊸l-focus-eq {C = C} p f (Il q g) rewrite not⊸-isprop C p q = refl
⊸l-focus-eq {C = C} p f (switch r q g) rewrite not⊸-isprop C p q = refl

-- admissibility of unrestricted ax

ax-focus : {A : Fma} → just A ∣ [] ⊢L A
ax-focus {` X} = switch refl _ ax
ax-focus {I} = Il _ (switch refl _ Ir)
ax-focus {A ⊸ B} = ⊸r (⊸l-focus (uf-focus (ax-focus {A})) (ax-focus {B}))

-- the focusing function itself

focus : ∀{S}{Γ}{A} → S ∣ Γ ⊢ A → S ∣ Γ ⊢L A
focus ax = ax-focus
focus (uf f) = uf-focus (focus f)
focus Ir = switch refl tt Ir
focus (⊸r f) = ⊸r (focus f)
focus (Il f) = Il-focus (focus f)
focus (⊸l f g) = ⊸l-focus (focus f) (focus g)

congfocus : ∀{S}{Γ}{A} {f g : S ∣ Γ ⊢ A} → f ≗ g → focus f ≡ focus g
congfocus refl = refl
congfocus (~ p) = sym (congfocus p)
congfocus (p ∙ p₁) = trans (congfocus p) (congfocus p₁)
congfocus (uf p) = cong uf-focus (congfocus p)
congfocus (⊸r p) = cong ⊸r (congfocus p)
congfocus (Il p) = cong Il-focus (congfocus p)
congfocus (⊸l p p₁) = cong₂ ⊸l-focus (congfocus p) (congfocus p₁)
congfocus axI = refl
congfocus ax⊸ = refl
congfocus ⊸ruf = refl
congfocus ⊸rIl = refl
congfocus ⊸r⊸l = refl

-- ====================================================================

-- focus after embL is identity

mutual 
  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Fma} →
              (f : S ∣ Γ ⊢L C) → focus (embL f) ≡ f
  focus-embL (⊸r f) = cong ⊸r (focus-embL f)
  focus-embL (Il p f) = trans (cong Il-focus (focus-embL f)) (Il-focus-eq p f)
  focus-embL (uf p f) = trans (cong uf-focus (focus-embL f)) (uf-focus-eq p f)
  focus-embL (switch {just (` X)} refl q f) = focus-embR q f
  focus-embL (switch {just (A ⊸ B)} refl q f) = focus-embR q f
  focus-embL (switch {nothing} refl q f) = focus-embR q f

  focus-embR : {S : StpR} → {Γ : Cxt} → {C : Fma} (q : not⊸ C) →
              (f : S ∣ Γ ⊢R C) → focus (embR f) ≡ switch refl q f
  focus-embR tt ax = refl
  focus-embR tt Ir = refl
  focus-embR q (⊸l f g) = trans (cong₂ ⊸l-focus (focus-embL f) (focus-embL g)) (⊸l-focus-eq q f g)


embL-uf-focus : {Γ : Cxt} → {A C : Fma} →
          (f : just A ∣ Γ ⊢L C) →
          embL (uf-focus f) ≗ uf (embL f)
embL-uf-focus (⊸r f) = ⊸r (embL-uf-focus f) ∙ ⊸ruf
embL-uf-focus (Il p f) = refl
embL-uf-focus (switch p q f) = refl

embL-Il-focus : {Γ : Cxt} → {C : Fma} → 
          (f : nothing ∣ Γ ⊢L C) →
          embL (Il-focus f) ≗ Il (embL f)
embL-Il-focus (⊸r f) = ⊸r (embL-Il-focus f) ∙ ⊸rIl
embL-Il-focus (uf p f) = refl
embL-Il-focus (switch p q f) = refl

embL-⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              (f : nothing ∣ Γ ⊢L A) (g : just B ∣ Δ ⊢L C) →
              embL (⊸l-focus f g) ≗ ⊸l (embL f) (embL g)
embL-⊸l-focus f (⊸r g) = ⊸r (embL-⊸l-focus f g) ∙ ⊸r⊸l
embL-⊸l-focus f (Il p g) = refl
embL-⊸l-focus f (switch p q g) = refl

embL-ax-focus : {C : Fma} → embL ax-focus ≗ ax {C}
embL-ax-focus {` X} = refl
embL-ax-focus {I} = ~ axI
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
embL-focus Ir = refl
embL-focus (⊸r f) = ⊸r (embL-focus f)
embL-focus (Il f) = embL-Il-focus (focus f) ∙ Il (embL-focus f)
embL-focus (⊸l f g) = embL-⊸l-focus (focus f) (focus g) ∙ ⊸l (embL-focus f) (embL-focus g)


