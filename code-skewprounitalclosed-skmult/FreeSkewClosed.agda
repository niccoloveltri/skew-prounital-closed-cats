{-# OPTIONS --rewriting #-}

open import SkMults

module FreeSkewClosed where
--(M : SkMult) where

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

--open SkMult M

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Stp → Fma → Set where
  base : ∀ {T S Γ Δ Y} → T ∣ Γ ⊢b Y
    → S ≡ mmap ` T → Δ ≡ lmap ` Γ
    → S ⇒ [ Δ ∣ ` Y ]
  id : {A : Fma} → just A ⇒ A
  _∘_ : {S : Stp}{B C : Fma} → just B ⇒ C → S ⇒ B → S ⇒ C
  _⊸_ : {A B C D : Fma} → just B ⇒ A → just C ⇒ D → just (A ⊸ C) ⇒ B ⊸ D
  j : {A : Fma} → nothing ⇒ A ⊸ A
  i : {A B : Fma} → nothing ⇒ A → just (A ⊸ B) ⇒ B
  L : {A B C : Fma} → just (B ⊸ C) ⇒ (A ⊸ B) ⊸ (A ⊸ C)

infix 15 _≐_
infixl 20 _∙_
infix 21 ~_

data _≐_ : {S : Stp}{B : Fma} → S ⇒ B → S ⇒ B → Set where
  -- ≐ equivalence and congruence
  refl : ∀{S B} {f : S ⇒ B} → f ≐ f
  ~_ : ∀{S B} {f g : S ⇒ B} → f ≐ g → g ≐ f
  _∙_ : ∀{S B} {f g h : S ⇒ B} → f ≐ g → g ≐ h → f ≐ h
  _∘_ : ∀{S B C} {f g : just B ⇒ C} {h k : S ⇒ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊸_ : ∀{A B C D} {f g : just A ⇒ C} {h k : just B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊸ h ≐ g ⊸ k
 
  -- id, ∘ category
  lid : ∀{S B} {f : S ⇒ B} → id ∘ f ≐ f
  rid : ∀{A B} {f : just A ⇒ B} → f ≐ f ∘ id
  ass : ∀{S B C D} {f : just C ⇒ D} {g : just B ⇒ C} {h : S ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)

  -- ⊸ functorial
  f⊸id : ∀{A B} → id {A} ⊸ id {B} ≐ id
  f⊸∘ : ∀{A B C D E F}
    → {f : just A ⇒ C} {g : just B ⇒ D} {h : just C ⇒ E} {k : just D ⇒ F}
    → (h ∘ f) ⊸ (k ∘ g) ≐ f ⊸ k ∘ h ⊸ g

  -- i congruence
  i : ∀{A B} {f g : nothing ⇒ A} → f ≐ g → i {A}{B} f ≐ i g


  -- i , j , L natural
  ni : ∀{A B C D} {e : nothing ⇒ A} {g : just B ⇒ C} {h : just A ⇒ D}
    → g ∘ i e ∘ h ⊸ id ≐ i (h ∘ e) ∘ id ⊸ g
  nj : ∀{A B} {f : just A ⇒ B} → f ⊸ id ∘ j ≐ id ⊸ f ∘ j
  nL : ∀{A B C D E F} {f : just A ⇒ D} {g : just E ⇒ B} {h : just C ⇒ F}
    → (f ⊸ g) ⊸ (id ⊸ h) ∘ L ≐ id ⊸ (f ⊸ id) ∘ L ∘ g ⊸ h

  -- skew closed axioms
  LLL : ∀{A B C D} → id ⊸ L {A} ∘ L {B}{C}{D} ≐ L ⊸ id ∘ L ∘ L
  ijL : ∀{A C} → i j ∘ L ≐ id {A ⊸ C}
  Lj : ∀{A B} → L ∘ j ≐ j {A ⊸ B}
  iL : ∀{A B C} {e : nothing ⇒ A} → id ⊸ i e ∘ L {A} {B} {C} ≐ i e ⊸ id
  ij : ∀{A} {e : nothing ⇒ A} → i e ∘ j ≐ e

  -- base compatibility
  baseax : ∀ {X} 
    → base (ax-b {X}) refl refl ≐ id
  baseuf : ∀ {Γ X Y} {f : just X ∣ Γ ⊢b Y}
    → base (uf-b f) refl refl ≐ id ⊸ base f refl refl ∘ j



≡-to-≐ : ∀{A}{B}{f g : A ⇒ B} → f ≡ g → f ≐ g
≡-to-≐ refl = refl

-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof≐_
infixr 2 _≐〈_〉_
infix 3 _qed≐

data _≐'_ {S : Stp}{B : Fma} (f g : S ⇒ B) : Set where
  relto :  f ≐ g → f ≐' g

proof≐_ : ∀{S B} {f g : S ⇒ B} → f ≐' g → f ≐ g
proof≐ relto p = p

_≐〈_〉_ :  ∀{S B} (f : S ⇒ B) {g h : S ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐〈 p 〉 relto q = relto (p ∙ q)

_qed≐  :  ∀{S B} (f : S ⇒ B) → f ≐' f
_qed≐ _ = relto refl


ni2 : ∀{A B C} {e : nothing ⇒ A} {g : just B ⇒ C} 
  → g ∘ i e ≐ i e ∘ id ⊸ g
ni2 =
  rid
  ∙ (refl ∘ ~ f⊸id)
  ∙ ni
  ∙ (i lid ∘ refl)

ni1 : ∀{A B C} {e : nothing ⇒ A} {h : just A ⇒ C} 
  → i e ∘ h ⊸ id ≐ i {_}{B} (h ∘ e)
ni1 =
  ~ (ass ∙ lid)
  ∙ ni
  ∙ (refl ∘ f⊸id)
  ∙ ~ rid

swap⊸ : ∀{A B C D} {f : just A ⇒ C}{g : just B ⇒ D}
  → f ⊸ id ∘ id ⊸ g ≐ id ⊸ g ∘ f ⊸ id
swap⊸ {f = f}{g} =
  proof≐
    f ⊸ id ∘ id ⊸ g
  ≐〈 ~ f⊸∘ 〉
    (id ∘ f) ⊸ (id ∘ g)
  ≐〈 (lid ∙ rid) ⊸ (lid ∙ rid) 〉
    (f ∘ id) ⊸ (g ∘ id)
  ≐〈 f⊸∘ 〉
    id ⊸ g ∘ f ⊸ id
  qed≐

id⊸∘ : ∀{A}{B}{C}{D} {f : just A ⇒ B}{g : just B ⇒ C}
  → id {D} ⊸ (g ∘ f) ≐ id ⊸ g ∘ id ⊸ f 
id⊸∘ = (rid ⊸ refl ) ∙ f⊸∘

∘⊸id : ∀{A}{B}{C}{D} {f : just A ⇒ B}{g : just B ⇒ C}
  → (g ∘ f) ⊸ id {D} ≐ f ⊸ id ∘ g ⊸ id
∘⊸id = (refl ⊸ rid) ∙ f⊸∘
