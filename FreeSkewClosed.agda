{-# OPTIONS --rewriting #-}

module FreeSkewClosed where

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

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Fma → Fma → Set where
  id : {A : Fma} → A ⇒ A
  _∘_ : {A B C : Fma} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊸_ : {A B C D : Fma} → B ⇒ A → C ⇒ D → A ⊸ C ⇒ B ⊸ D
  i : {A : Fma} → I ⊸ A ⇒ A
  j : {A : Fma} → I ⇒ A ⊸ A
  L : {A B C : Fma} → B ⊸ C ⇒ (A ⊸ B) ⊸ (A ⊸ C)

infix 15 _≐_
infixl 20 _∙_
infix 21 ~_

data _≐_ : {A B : Fma} → A ⇒ B → A ⇒ B → Set where
  -- ≐ equivalence and congruence
  refl : {A B : Fma} {f : A ⇒ B} → f ≐ f
  ~_ : {A B : Fma} {f g : A ⇒ B} → f ≐ g → g ≐ f
  _∙_ : {A B : Fma} {f g h : A ⇒ B} → f ≐ g → g ≐ h → f ≐ h
  _∘_ : {A B C : Fma} {f g : B ⇒ C} {h k : A ⇒ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊸_ : {A B C D : Fma} {f g : A ⇒ C} {h k : B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊸ h ≐ g ⊸ k

  -- id, ∘ category
  lid : {A B : Fma} {f : A ⇒ B} → id ∘ f ≐ f
  rid : {A B : Fma} {f : A ⇒ B} → f ≐ f ∘ id
  ass : {A B C D : Fma} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)

  -- ⊸ functorial
  f⊸id : {A B : Fma} → id {A} ⊸ id {B} ≐ id
  f⊸∘ : {A B C D E F : Fma} {f : A ⇒ C} {g : B ⇒ D} {h : C ⇒ E} {k : D ⇒ F} →  
                    (h ∘ f) ⊸ (k ∘ g) ≐ f ⊸ k ∘ h ⊸ g

  -- i , j , L natural
  ni : {A B : Fma} {f : A ⇒ B} → f ∘ i ≐ i ∘ id ⊸ f
  nj : {A B : Fma} {f : A ⇒ B} → f ⊸ id ∘ j ≐ id ⊸ f ∘ j
  nL : {A B C D E F : Fma} {f : A ⇒ D} {g : E ⇒ B} {h : C ⇒ F}
    → (f ⊸ g) ⊸ (id ⊸ h) ∘ L ≐ id ⊸ (f ⊸ id) ∘ L ∘ g ⊸ h

  -- skew closed axioms
  LLL : {A B C D : Fma} → id ⊸ L {A} ∘ L {B}{C}{D} ≐ L ⊸ id ∘ L ∘ L
  ijL : {A C : Fma} → i ∘ j ⊸ id ∘ L ≐ id {A ⊸ C}
  Lj : {A B : Fma} → L ∘ j ≐ j {A ⊸ B}
  iL : {B C : Fma} → id ⊸ i ∘ L {I} {B} {C} ≐ i ⊸ id
  ij : i ∘ j ≐ id

≡-to-≐ : ∀{A}{B}{f g : A ⇒ B} → f ≡ g → f ≐ g
≡-to-≐ refl = refl

-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof≐_
infixr 2 _≐〈_〉_
infix 3 _qed≐

data _≐'_ {A B : Fma} (f g : A ⇒ B) : Set where
  relto :  f ≐ g → f ≐' g

proof≐_ : {A B : Fma} {f g : A ⇒ B} → f ≐' g → f ≐ g
proof≐ relto p = p

_≐〈_〉_ :  {A B : Fma} (f : A ⇒ B) {g h : A ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐〈 p 〉 relto q = relto (p ∙ q)

_qed≐  :  {A B : Fma} (f : A ⇒ B) → f ≐' f
_qed≐ _ = relto refl

