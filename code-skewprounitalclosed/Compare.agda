{-# OPTIONS --rewriting #-}

module Compare where

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
open import Sound

-- ==============================================================

-- Connecting focused sequent calculus and βη-long normal forms

-- ==============================================================

-- Focused sequent calculus (with more relaxed ax rule)

data _∣_⊢L_ : Stp → Cxt → Fma → Set
data _∣_⊢R_ : Fma → Cxt → Fma → Set

data _∣_⊢L_ where
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
            (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
  uf : {Γ : Cxt} → {A : Fma} {X : At} → 
            (f : just A ∣ Γ ⊢L ` X) →
            nothing ∣ A ∷ Γ ⊢L ` X
  switch :  {A : Fma} → 
            {Γ : Cxt} → {X : At} →
            (f : A ∣ Γ ⊢R ` X) → just A ∣ Γ ⊢L ` X 

data _∣_⊢R_ where
  ax : {A : Fma} → A ∣ [] ⊢R A
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
            (f : nothing ∣ Γ ⊢L A) → (g : B ∣ Δ ⊢R C) →
            A ⊸ B ∣ Γ ++ Δ ⊢R C

-- βη-long normal forms

data _∣_⊢nf_ : Stp → Cxt → Fma → Set
data _∣_⊢ne_ : Fma → Cxt → Fma → Set

data _∣_⊢nf_ where
  ⊸i : {S : Stp} {Γ : Cxt} {A B : Fma}
    → S ∣ Γ ++ A ∷ [] ⊢nf B → S ∣ Γ ⊢nf A ⊸ B
  uf : {Γ : Cxt} {A : Fma} {X : At}
    → just A ∣ Γ ⊢nf ` X → nothing ∣ A ∷ Γ ⊢nf ` X
  ne` : {A : Fma} {Γ : Cxt} {X : At}
    → A ∣ Γ ⊢ne ` X → just A ∣ Γ ⊢nf ` X

data _∣_⊢ne_ where
  ax : {A : Fma} → A ∣ [] ⊢ne A     
  ⊸e : {S : Fma} {Γ Δ : Cxt} {A B : Fma}
    → S ∣ Γ ⊢ne A ⊸ B → nothing ∣ Δ ⊢nf A
    → S ∣ Γ ++ Δ ⊢ne B

-- Translations between the two calculi


nf2focL : ∀ {S Γ C} → S ∣ Γ ⊢nf C → S ∣ Γ ⊢L C
ne2focR : ∀ {S Γ Δ A B} → S ∣ Γ ⊢ne A → A ∣ Δ ⊢R B
  → S ∣ Γ ++ Δ ⊢R B

nf2focL (⊸i f) = ⊸r (nf2focL f)
nf2focL (uf f) = uf (nf2focL f)
nf2focL (ne` f) = switch (ne2focR f ax)


ne2focR ax u = u
ne2focR (⊸e f t) u = ne2focR f (⊸l (nf2focL t) u)

focL2nf : ∀ {S Γ C} → S ∣ Γ ⊢L C → S ∣ Γ ⊢nf C
focR2ne : ∀ {S Γ Δ A C} → S ∣ Γ ⊢ne A → A ∣ Δ ⊢R C
  → S ∣ Γ ++ Δ ⊢ne C

focL2nf (⊸r f) = ⊸i (focL2nf f)
focL2nf (uf f) = uf (focL2nf f)
focL2nf {just A} (switch f) = ne` (focR2ne ax f)

focR2ne u ax = u
focR2ne u (⊸l f t) = focR2ne (⊸e u (focL2nf f)) t

-- The translations form an isomorphism

focL2nf2focL : ∀ {S Γ C} (f : S ∣ Γ ⊢L C)
  → nf2focL (focL2nf f) ≡ f
focR2nf2focR : ∀ {S Γ Δ A B}
  → (t : S ∣ Γ ⊢ne A) (u : A ∣ Δ ⊢R B) 
  → ne2focR (focR2ne t u) ax ≡ ne2focR t u


focL2nf2focL (⊸r f) = cong ⊸r (focL2nf2focL f)
focL2nf2focL (uf f) = cong uf (focL2nf2focL f)
focL2nf2focL {just A} (switch f) = cong switch (focR2nf2focR ax f)

focR2nf2focR t ax = refl
focR2nf2focR t (⊸l f u) =
  trans (focR2nf2focR (⊸e t (focL2nf f)) u)
    (cong (ne2focR t) (cong₂ ⊸l (focL2nf2focL f) refl))

nf2focL2nf : ∀ {S Γ C} (f : S ∣ Γ ⊢nf C)
  → focL2nf (nf2focL f) ≡ f
ne2focR2ne : ∀ {S Γ Δ A B}
  → (t : S ∣ Γ ⊢ne A) (u : A ∣ Δ ⊢R B) 
  → focR2ne ax (ne2focR t u) ≡ focR2ne t u

nf2focL2nf (⊸i f) = cong ⊸i (nf2focL2nf f)
nf2focL2nf (uf f) = cong uf (nf2focL2nf f)
nf2focL2nf (ne` f) = cong ne` (ne2focR2ne f ax)

ne2focR2ne ax u = refl
ne2focR2ne (⊸e t u) v =
  trans (ne2focR2ne t (⊸l (nf2focL u) v))
    (cong₂ focR2ne (cong (⊸e t) (nf2focL2nf u)) (refl {x = v}))

-- ==================================================================

-- To conclude, we connect the two formulations of focused sequent
-- calculus (with different ax rules)

open import Focusing renaming (_∣_⊢L_ to _∣_⊢L'_
                             ; _∣_⊢R_ to _∣_⊢R'_
                             ; ⊸l-focus to ⊸l-focus')

L2L' : ∀{S Γ A} → S ∣ Γ ⊢L A → S ∣ Γ ⊢L' A
R2L' : ∀{Γ A C} → A ∣ Γ ⊢R C → just A ∣ Γ ⊢L' C

L2L' (⊸r f) = ⊸r (L2L' f)
L2L' (uf f) = uf tt (L2L' f)
L2L' (switch f) = R2L' f

R2L' ax = ax-focus
R2L' (⊸l f g) = ⊸l-focus' (L2L' f) (R2L' g)

L'2L : ∀{S Γ A} → S ∣ Γ ⊢L' A → S ∣ Γ ⊢L A
R'2R : ∀{Γ A C} → just A ∣ Γ ⊢R' C → A ∣ Γ ⊢R C

L'2L (⊸r f) = ⊸r (L'2L f)
L'2L {A = ` X} (uf p f) = uf (L'2L f)
L'2L {just A} {A = ` X} (switch q f) = switch (R'2R f)

R'2R ax = ax
R'2R (⊸l f g) = ⊸l (L'2L f) (R'2R g)

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (switch g) = switch (⊸l f g)

L'2L⊸l-focus : ∀{Γ Δ A B C}
  → (f : nothing ∣ Γ ⊢L' A) (g : just B ∣ Δ ⊢L' C)
  → L'2L (⊸l-focus' f g) ≡ ⊸l-focus (L'2L f) (L'2L g)
L'2L⊸l-focus f (⊸r g) = cong ⊸r (L'2L⊸l-focus f g)
L'2L⊸l-focus {C = ` X} f (switch q g) = refl

L2L'2L : ∀{S Γ A} (f : S ∣ Γ ⊢L A) → L'2L (L2L' f) ≡ f
R2L'2L : ∀{S Γ X} (f : S ∣ Γ ⊢R ` X) → L'2L (R2L' f) ≡ switch f

L2L'2L (⊸r f) = cong ⊸r (L2L'2L f)
L2L'2L (uf f) = cong uf (L2L'2L f)
L2L'2L (switch f) = R2L'2L f

R2L'2L ax = refl
R2L'2L (⊸l f g) =
  trans (L'2L⊸l-focus (L2L' f) (R2L' g))
    (cong₂ ⊸l-focus (L2L'2L f) (R2L'2L g))

L'2L2L' : ∀{S Γ A} (f : S ∣ Γ ⊢L' A) → L2L' (L'2L f) ≡ f
R'2R2R' : ∀{Γ A X} (f : just A ∣ Γ ⊢R' ` X) → R2L' (R'2R f) ≡ switch tt f

L'2L2L' (⊸r f) = cong ⊸r (L'2L2L' f)
L'2L2L' {A = ` X} (uf tt f) = cong (uf tt) (L'2L2L' f)
L'2L2L' {just A} {A = ` X} (switch tt f) = R'2R2R' f

R'2R2R' ax = refl
R'2R2R' (⊸l f g) = cong₂ ⊸l-focus' (L'2L2L' f) (R'2R2R' g)
