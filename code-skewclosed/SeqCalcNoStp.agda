{-# OPTIONS --rewriting #-}

module SeqCalcNoStp where

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

-- Presentation of the calculus w/o stoup

infix 2 _⊢S_

data _⊢S_ : Cxt → Fma → Set where
  ax : {A : Fma} → A ∷ [] ⊢S A
  Ir : [] ⊢S I
  ⊸r : {Γ : Cxt} → {A B : Fma} →
              Γ ++ A ∷ [] ⊢S B → Γ ⊢S A ⊸ B
  Il : {Γ : Cxt} → {C : Fma} → 
              Γ ⊢S C → I ∷ Γ ⊢S C 
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              Γ ⊢S A → B ∷ Δ ⊢S C →
              A ⊸ B ∷ Γ ++ Δ ⊢S C

-- Equality of proofs 

data _≗S_ : {Γ : Cxt}{A : Fma} → Γ ⊢S A → Γ ⊢S A → Set where
  refl : ∀{Γ}{A}{f : Γ ⊢S A} → f ≗S f
  ~_ : ∀{Γ}{A}{f g : Γ ⊢S A} → f ≗S g → g ≗S f
  _∙_ : ∀{Γ}{A}{f g h : Γ ⊢S A} → f ≗S g → g ≗S h → f ≗S h
  ⊸r : ∀{Γ}{A}{C}{f g : Γ ++ A ∷ [] ⊢S C} → f ≗S g → ⊸r f ≗S ⊸r g
  Il : ∀{Γ}{C}{f g : Γ ⊢S C} → f ≗S g → Il f ≗S Il g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : Γ ⊢S A}{f' g' : B ∷ Δ ⊢S C}
    → f ≗S g → f' ≗S g' → ⊸l f f' ≗S ⊸l g g'
  axI : ax {I} ≗S Il Ir
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗S ⊸r (⊸l ax ax)
  ⊸rIl : {Γ : Cxt}{B C : Fma} {f : Γ ++ B ∷ [] ⊢S C}
    → ⊸r (Il f) ≗S Il (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : Γ ⊢S A}{g : B ∷ Δ ++ C ∷ [] ⊢S D}
    → ⊸r (⊸l f g) ≗S ⊸l f (⊸r g)

≡-to-≗S : ∀{Γ}{A}{f f' : Γ ⊢S A} → f ≡ f' → f ≗S f'
≡-to-≗S refl = refl

-- =======================================================================

-- -- equational reasoning sugar for ≗S

infix 4 _≗S'_
infix 1 proof≗S_
infixr 2 _≗S〈_〉_
infix 3 _qed≗S

data _≗S'_ {Γ : Cxt}{A : Fma} (f g : Γ ⊢S A) : Set where
  relto :  f ≗S g → f ≗S' g

proof≗S_ : {Γ : Cxt}{A : Fma} {f g : Γ ⊢S A} → f ≗S' g → f ≗S g
proof≗S relto p = p

_≗S〈_〉_ : {Γ : Cxt}{A : Fma} (f : Γ ⊢S A) {g h : Γ ⊢S A} → f ≗S g → g ≗S' h → f ≗S' h 
_ ≗S〈 p 〉 relto q = relto (p ∙ q)

_qed≗S  :  {Γ : Cxt}{A : Fma} (f : Γ ⊢S A) → f ≗S' f
_qed≗S _ = relto refl

-- ====================================================================

-- Equivalence of the two presentations of the calculus


t : Stp → Fma
t nothing = I
t (just A) = A

Il-1S : {Γ : Cxt} → {C : Fma} → 
              I ∷ Γ ⊢S C → Γ ⊢S C
Il-1S ax = Ir
Il-1S (⊸r f) = ⊸r (Il-1S f)
Il-1S (Il f) = f              

Il-1S-iso : {Γ : Cxt} → {C : Fma} (f : Γ ⊢S C)
  → Il-1S (Il f) ≡ f
Il-1S-iso ax = refl
Il-1S-iso Ir = refl
Il-1S-iso (⊸r f) = refl
Il-1S-iso (Il f) = refl
Il-1S-iso (⊸l f f₁) = refl  

Il? : ∀{S}{Γ}{A} → S ∣ Γ ⊢ A → just (t S) ∣ Γ ⊢ A
Il? {just A} f = f
Il? {nothing} f = Il f

congIl-1S : {Γ : Cxt} → {C : Fma} → 
              {f g : I ∷ Γ ⊢S C} → f ≗S g → Il-1S f ≗S Il-1S g
congIl-1S refl = refl
congIl-1S (~ p) = ~ (congIl-1S p)
congIl-1S (p ∙ p₁) = (congIl-1S p) ∙ (congIl-1S p₁)
congIl-1S (⊸r p) = ⊸r (congIl-1S p)
congIl-1S (Il p) = p
congIl-1S axI = refl
congIl-1S ⊸rIl = refl

add-stp : ∀{Γ}{A} → Γ ⊢S A → nothing ∣ Γ ⊢ A
add-stp ax = uf ax
add-stp Ir = Ir
add-stp (⊸r f) = ⊸r (add-stp f)
add-stp (Il f) = uf (Il (add-stp f))
add-stp (⊸l f g) = uf (⊸l (add-stp f) (uf-1 (add-stp g)))

add-stp-Il-1S : {Γ : Cxt} → {C : Fma} (f : I ∷ Γ ⊢S C) → 
  add-stp (Il-1S f) ≗ Il-1 (uf-1 (add-stp f))
add-stp-Il-1S ax = refl
add-stp-Il-1S (⊸r f) = ⊸r (add-stp-Il-1S f)
add-stp-Il-1S (Il f) = refl

rem-stp : ∀{S}{Γ}{A} → S ∣ Γ ⊢ A → t S ∷ Γ ⊢S A
rem-stp ax = ax
rem-stp (uf f) = Il (rem-stp f)
rem-stp Ir = ax
rem-stp (⊸r f) = ⊸r (rem-stp f)
rem-stp (Il f) = rem-stp f
rem-stp (⊸l f g) = ⊸l (Il-1S (rem-stp f)) (rem-stp g)

rem-stp-uf-1 : ∀{Γ}{A}{C} → (f : nothing ∣ A ∷ Γ ⊢ C) →
  rem-stp (uf-1 f) ≡ Il-1S (rem-stp f)
rem-stp-uf-1 (uf f) = refl
rem-stp-uf-1 (⊸r f) = cong ⊸r (rem-stp-uf-1 f)

iso-stp :  ∀{Γ}{A} (f : Γ ⊢S A) → rem-stp (add-stp f) ≗S Il f
iso-stp ax = refl
iso-stp Ir = axI
iso-stp (⊸r f) = ⊸r (iso-stp f) ∙ ⊸rIl
iso-stp (Il f) = Il (iso-stp f)
iso-stp (⊸l f g) =
  Il (⊸l (congIl-1S (iso-stp f))
    (≡-to-≗S (rem-stp-uf-1 (add-stp g))
     ∙ congIl-1S (iso-stp g)))

iso-stp2 :  ∀{S}{Γ}{A} (f : S ∣ Γ ⊢ A) → add-stp (rem-stp f) ≗ uf (Il? f)
iso-stp2 ax = refl
iso-stp2 (uf f) = uf (Il (iso-stp2 f))
iso-stp2 Ir = uf axI
iso-stp2 {just A} (⊸r f) = (⊸r (iso-stp2 f)) ∙ ⊸ruf
iso-stp2 {nothing} (⊸r f) =
  ⊸r (iso-stp2 f)
  ∙ ⊸ruf
  ∙ uf ⊸rIl
iso-stp2 (Il f) = iso-stp2 f
iso-stp2 (⊸l f g) =
  uf (⊸l
    (add-stp-Il-1S (rem-stp f)
    ∙ congIl-1 (conguf-1 (iso-stp2 f)))
    (conguf-1 (iso-stp2 g)))

str-rem-stp : ∀{Γ}{A} → nothing ∣ Γ ⊢ A → Γ ⊢S A
str-rem-stp f = Il-1S (rem-stp f)

str-iso-stp :  ∀{Γ}{A} (f : Γ ⊢S A)
  → str-rem-stp (add-stp f) ≗S f
str-iso-stp f = congIl-1S (iso-stp f)

str-iso-stp2 :  ∀{Γ}{A} (f : nothing ∣ Γ ⊢ A)
  → add-stp (str-rem-stp f) ≗ f
str-iso-stp2 f =
  add-stp-Il-1S (rem-stp f)
  ∙ congIl-1 (conguf-1 (iso-stp2 f))


{-
-- ====================================================================

-- Admissibility of cut

Il-1s : {Γ : Cxt} → {C : Fma} → 
              I ∷ Γ ⊢S C → Γ ⊢S C
Il-1s ax = Ir
Il-1s (⊸r f) = ⊸r (Il-1s f)
Il-1s (Il f) = f


cut : {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ₁ : Cxt} → {A C : Fma} → 
             Γ ⊢S A  → Δ ⊢S C  → Δ ≡ Δ₀ ++ A ∷ Δ₁ → Δ₀ ++ Γ ++ Δ₁ ⊢ C
cut [] ax g refl = g
cut [] Ir g refl = Il-1s g
cut [] (⊸r f) ax refl = ⊸r f
cut [] (⊸r f) (⊸r g) refl = ⊸r (cut [] (⊸r f) g refl)
cut [] (⊸r {Γ} f) (⊸l g g') refl = cut [] (cut Γ g f refl) g' refl
cut [] (Il f) g refl = Il (cut [] f g refl)
cut [] (⊸l f f') g refl = ⊸l f (cut [] f' g refl)
cut (S ∷ Δ₀) f ax r = ⊥-elim ([]disj∷ Δ₀ (proj₂ (inj∷ r)))
cut (S ∷ Δ₀) f (⊸r g) refl = ⊸r (cut (S ∷ Δ₀) f g refl)
cut (.I ∷ Δ₀) f (Il g) refl = Il (cut Δ₀ f g refl)
cut (S ∷ Δ₀) {Δ₁} f (⊸l {Γ}{Δ} g g') r with cases++ Δ₀ Γ Δ₁ Δ (proj₂ (inj∷ r))
cut (.(_ ⊸ _) ∷ Δ₀) {.(Γ₀ ++ Δ)} f (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = ⊸l (cut Δ₀ f g refl) g'
cut (.(_ ⊸ _) ∷ .(Γ ++ Γ₀)) {Δ₁} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} g g') refl | inj₂ (Γ₀ , refl , refl) = ⊸l g (cut (_ ∷ Γ₀) f g' refl)
-}
