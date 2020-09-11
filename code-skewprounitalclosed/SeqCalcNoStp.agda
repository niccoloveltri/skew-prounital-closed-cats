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
open import FreeSkewProunitalClosed
open import SeqCalc

-- =======================================================================

-- Presentation of the calculus w/o stoup

infix 2 _⊢S_

data _⊢S_ : Cxt → Fma → Set where
  ax : {A : Fma} → A ∷ [] ⊢S A
  ⊸r : {Γ : Cxt} → {A B : Fma} →
              Γ ++ A ∷ [] ⊢S B → Γ ⊢S A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              Γ ⊢S A → B ∷ Δ ⊢S C →
              A ⊸ B ∷ Γ ++ Δ ⊢S C

-- Equality of proofs 

data _≗S_ : {Γ : Cxt}{A : Fma} → Γ ⊢S A → Γ ⊢S A → Set where
  refl : ∀{Γ}{A}{f : Γ ⊢S A} → f ≗S f
  ~_ : ∀{Γ}{A}{f g : Γ ⊢S A} → f ≗S g → g ≗S f
  _∙_ : ∀{Γ}{A}{f g h : Γ ⊢S A} → f ≗S g → g ≗S h → f ≗S h
  ⊸r : ∀{Γ}{A}{C}{f g : Γ ++ A ∷ [] ⊢S C} → f ≗S g → ⊸r f ≗S ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : Γ ⊢S A}{f' g' : B ∷ Δ ⊢S C}
    → f ≗S g → f' ≗S g' → ⊸l f f' ≗S ⊸l g g'
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗S ⊸r (⊸l ax ax)
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


add-stp : ∀{Γ}{A} → Γ ⊢S A → nothing ∣ Γ ⊢ A
add-stp ax = uf ax
add-stp (⊸r f) = ⊸r (add-stp f)
add-stp (⊸l f g) = uf (⊸l (add-stp f) (uf-1 (add-stp g)))

rem-stp : ∀{S}{Γ}{A} → S ∣ Γ ⊢ A → asCxt S Γ ⊢S A
rem-stp ax = ax
rem-stp (uf f) = rem-stp f
rem-stp (⊸r f) = ⊸r (rem-stp f)
rem-stp (⊸l f g) = ⊸l (rem-stp f) (rem-stp g)


rem-stp-uf-1 : ∀{Γ}{A}{C} → (f : nothing ∣ A ∷ Γ ⊢ C) →
  rem-stp (uf-1 f) ≡ rem-stp f
rem-stp-uf-1 (uf f) = refl
rem-stp-uf-1 (⊸r f) = cong ⊸r (rem-stp-uf-1 f)

iso-stp :  ∀{Γ}{A} (f : Γ ⊢S A) → rem-stp (add-stp f) ≗S f
iso-stp ax = refl
iso-stp (⊸r f) = ⊸r (iso-stp f) 
iso-stp (⊸l f g) =
  ⊸l (iso-stp f)
    (≡-to-≗S (rem-stp-uf-1 (add-stp g))
    ∙ iso-stp g)

iso-stp2-j :  ∀{Γ A C} (f : just A ∣ Γ ⊢ C) → add-stp (rem-stp f) ≗ uf f
iso-stp2-n :  ∀{Γ C} (f : nothing ∣ Γ ⊢ C) → add-stp (rem-stp f) ≗ f

iso-stp2-j ax = refl
iso-stp2-j (⊸r f) = ⊸r (iso-stp2-j f) ∙ ⊸ruf
iso-stp2-j (⊸l f g) =
  uf (⊸l (iso-stp2-n f) (conguf-1 (iso-stp2-j g)))

iso-stp2-n (uf f) = iso-stp2-j f
iso-stp2-n (⊸r f) = ⊸r (iso-stp2-n f)

