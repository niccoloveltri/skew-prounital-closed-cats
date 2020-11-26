{-# OPTIONS --rewriting #-}

module Combinators where

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
open import CompleteSound

id⊸ : {A C D : Fma} (g : just C ⇒ D) → just (A ⊸ C) ⇒ A ⊸ D
id⊸ g = jY-1 (L ∘ jY g)

_⊸id : {A B C : Fma} (f : just B ⇒ A) → just (A ⊸ C) ⇒ B ⊸ C
f ⊸id = i (id⊸ f ∘ j) ∘ L



data ↦_ : Fma → Set where
  I : {A : Fma} → ↦ A ⊸ A
  b : {A B C : Fma} → ↦ (B ⊸ C) ⊸ ((A ⊸ B) ⊸ (A ⊸ C))
  c : {A B : Fma} → ↦ A → ↦ (A ⊸ B) ⊸ B
  mp : {A B : Fma} → ↦ A ⊸ B → ↦ A → ↦ B

_∘c_ : {A B C : Fma} → ↦ B ⊸ C → ↦ A ⊸ B
  → ↦ A ⊸ C
f ∘c g = mp (mp b f) g

id⊸c : {A C D : Fma} → ↦ C ⊸ D → ↦ (A ⊸ C) ⊸ (A ⊸ D)
id⊸c f = mp b f

_c⊸id : {A B C : Fma} → ↦ B ⊸ A → ↦ (A ⊸ C) ⊸ (B ⊸ C)
f c⊸id = c f ∘c b

_⊸c_ : {A B C D : Fma} → ↦ B ⊸ A → ↦ C ⊸ D
  → ↦ (A ⊸ C) ⊸ (B ⊸ D)
f ⊸c g = id⊸c g ∘c (f c⊸id)

↦2⇒ : ∀{A} → ↦ A → nothing ⇒ A 
↦2⇒ I = j
↦2⇒ b = jY L
↦2⇒ (c f) = jY (i (↦2⇒ f))
↦2⇒ (mp f x) = jY-1 (↦2⇒ f) ∘ ↦2⇒ x

⇒2↦-j : ∀{A B} → just A ⇒ B → ↦ A ⊸ B
⇒2↦-n : ∀{B} → nothing ⇒ B → ↦ B

⇒2↦-j id = I
⇒2↦-j (f ∘ g) = (⇒2↦-j f) ∘c (⇒2↦-j g)
⇒2↦-j (f ⊸ g) = ⇒2↦-j f ⊸c ⇒2↦-j g 
⇒2↦-j (i f) = c (⇒2↦-n f)
⇒2↦-j L = b

⇒2↦-n (f ∘ g) = mp (⇒2↦-j f) (⇒2↦-n g)
⇒2↦-n j = I

infix 15 _≐c_

data _≐c_ : {B : Fma} → ↦ B → ↦ B → Set where
  -- ≐c equivalence and congruence
  refl : ∀{B} {f : ↦ B} → f ≐c f
  ~_ : ∀{B} {f g : ↦ B} → f ≐c g → g ≐c f
  _∙_ : ∀{B} {f g h : ↦ B} → f ≐c g → g ≐c h → f ≐c h
  mp : ∀{B C} {f g : ↦ B ⊸ C} {h k : ↦ B} →
                         f ≐c g → h ≐c k → mp f h ≐c mp g k
 
  -- id, ∘ category
  lid : ∀{B} {f : ↦ B} → mp I f ≐c f
  ass : ∀{B C D} {f : ↦ C ⊸ D} {g : ↦ B ⊸ C} {h : ↦ B}
      → mp (f ∘c g) h ≐c mp f (mp g h)
  -- mp (mp (mp b f) g) h = mp f (mp g h)
  rid : ∀{A B} {f : ↦ A ⊸ B} → f ≐c (f ∘c I)

  -- c congruence
  c : ∀{A B} {f g : ↦ A} → f ≐c g → c {A}{B} f ≐c c g

  -- c , I , b natural
  nc : ∀{A A' B B'} {a : ↦ A} {g : ↦ B ⊸ B'} {h : ↦ A ⊸ A'}
     → (g ∘c (c a ∘c (h c⊸id))) ≐c (c (mp h a) ∘c id⊸c g)
  nI : ∀{A A'} {f : ↦ A ⊸ A'} → (f ∘c I) ≐c (I ∘c f)
  nb : ∀{A A' C C' D D'} {f : ↦ A ⊸ A'} {g : ↦ D' ⊸ D} {h : ↦ C ⊸ C'}
    → (((f ⊸c g) ⊸c id⊸c h) ∘c b) ≐c ((id⊸c (f c⊸id) ∘c b) ∘c (g ⊸c h))

  -- skew closed axioms
  bbb : ∀{A B C D} → (id⊸c (b {A}) ∘c b {B}{C}{D}) ≐c ((b c⊸id) ∘c (b ∘c b))
  cIb : ∀{A C} → c I ∘c b ≐c I {A ⊸ C}
  bI : ∀{A B} → mp b I ≐c I {A ⊸ B}
  cb : ∀{A B C} {a : ↦ A} → ((id⊸c (c a)) ∘c (b {A} {B} {C})) ≐c (c a c⊸id)
  cI : ∀{A} {a : ↦ A} → mp (c a) I ≐c a


≐2≐c-j : ∀{A B} {f g : just A ⇒ B} → f ≐ g → ⇒2↦-j f ≐c ⇒2↦-j g
≐2≐c-n : ∀{B} {f g : nothing ⇒ B} → f ≐ g → ⇒2↦-n f ≐c ⇒2↦-n g

≐2≐c-j refl = refl
≐2≐c-j (~ eq) = ~ (≐2≐c-j eq)
≐2≐c-j (eq ∙ eq₁) = ≐2≐c-j eq ∙ ≐2≐c-j eq₁
≐2≐c-j (eq ∘ eq₁) = mp (mp refl (≐2≐c-j eq)) (≐2≐c-j eq₁)
≐2≐c-j (eq ⊸ eq₁) = mp (mp refl (mp refl (≐2≐c-j eq₁))) (mp (mp refl (c (≐2≐c-j eq))) refl)
≐2≐c-j lid = ~ (rid ∙ nI)
≐2≐c-j rid = rid
≐2≐c-j ass = {!nb!}
≐2≐c-j f⊸id = 
  mp (mp refl bI) refl
  ∙ mp bI refl
  ∙ lid
  ∙ cIb
≐2≐c-j f⊸∘ = {!!}
≐2≐c-j (i eq) = c (≐2≐c-n eq)
≐2≐c-j ni = {!!}
≐2≐c-j nL = {!!}
≐2≐c-j LLL =
  mp (mp refl (mp refl cIb)) refl
  ∙ mp (mp refl (~ rid)) refl
  ∙ bbb
  ∙ ~ (mp (mp refl (mp (mp refl (mp (mp refl bI ∙ bI) refl ∙ lid)) refl)) refl
      ∙ (mp (~ ass ∙ (mp {!!} refl ∙ ass)) refl ∙ ass))
≐2≐c-j ijL = cIb
≐2≐c-j iL =
  mp (mp refl (mp refl cIb)) refl
  ∙ mp (mp refl (~ rid)) refl
  ∙ ~ lid
  ∙ mp (~ bI ∙ mp refl (~ bI)) cb

≐2≐c-n refl = refl
≐2≐c-n (~ eq) = ~ ≐2≐c-n eq
≐2≐c-n (eq ∙ eq₁) = ≐2≐c-n eq ∙ ≐2≐c-n eq₁
≐2≐c-n (eq ∘ eq₁) = {!!}
≐2≐c-n lid = lid
≐2≐c-n ass = ass
≐2≐c-n nj = {!!}
≐2≐c-n Lj = bI
≐2≐c-n ij = cI

≐c2≐ : ∀{B} {f g : ↦ B} → f ≐c g → ↦2⇒ f ≐ ↦2⇒ g


-- -- -- Derivations in the categorical calculus

-- -- infix 15 _⇒_
-- -- infixl 20 _∘_

-- -- data _⇒_ : Stp → Fma → Set where
-- --   id : {A : Fma} → just A ⇒ A
-- --   _∘_ : {S : Stp}{B C : Fma} → just B ⇒ C → S ⇒ B → S ⇒ C
-- --   _⊸_ : {A B C D : Fma} → just B ⇒ A → just C ⇒ D → just (A ⊸ C) ⇒ B ⊸ D
-- --   j : {A : Fma} → nothing ⇒ A ⊸ A
-- --   i : {A B : Fma} → nothing ⇒ A → just (A ⊸ B) ⇒ B
-- --   L : {A B C : Fma} → just (B ⊸ C) ⇒ (A ⊸ B) ⊸ (A ⊸ C)


-- -- -- Equivalence of derivations

-- -- infix 15 _≐_
-- -- infixl 20 _∙_
-- -- infix 21 ~_

-- -- data _≐_ : {S : Stp}{B : Fma} → S ⇒ B → S ⇒ B → Set where
-- --   -- ≐ equivalence and congruence
-- --   refl : ∀{S B} {f : S ⇒ B} → f ≐ f
-- --   ~_ : ∀{S B} {f g : S ⇒ B} → f ≐ g → g ≐ f
-- --   _∙_ : ∀{S B} {f g h : S ⇒ B} → f ≐ g → g ≐ h → f ≐ h
-- --   _∘_ : ∀{S B C} {f g : just B ⇒ C} {h k : S ⇒ B} →
-- --                          f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
-- --   _⊸_ : ∀{A B C D} {f g : just A ⇒ C} {h k : just B ⇒ D} →
-- --                          f ≐ g → h ≐ k → f ⊸ h ≐ g ⊸ k
 
-- --   -- id, ∘ category
-- --   lid : ∀{S B} {f : S ⇒ B} → id ∘ f ≐ f
-- --   rid : ∀{A B} {f : just A ⇒ B} → f ≐ f ∘ id
-- --   ass : ∀{S B C D} {f : just C ⇒ D} {g : just B ⇒ C} {h : S ⇒ B}
-- --        → f ∘ g ∘ h ≐ f ∘ (g ∘ h)

-- --   -- ⊸ functorial
-- --   f⊸id : ∀{A B} → id {A} ⊸ id {B} ≐ id
-- --   f⊸∘ : ∀{A B C D E F}
-- --     → {f : just A ⇒ C} {g : just B ⇒ D} {h : just C ⇒ E} {k : just D ⇒ F}
-- --     → (h ∘ f) ⊸ (k ∘ g) ≐ f ⊸ k ∘ h ⊸ g

-- --   -- i congruence
-- --   i : ∀{A B} {f g : nothing ⇒ A} → f ≐ g → i {A}{B} f ≐ i g


-- --   -- i , j , L natural
-- --   ni : ∀{A B C D} {e : nothing ⇒ A} {g : just B ⇒ C} {h : just A ⇒ D}
-- --     → g ∘ i e ∘ h ⊸ id ≐ i (h ∘ e) ∘ id ⊸ g
-- --   nj : ∀{A B} {f : just A ⇒ B} → f ⊸ id ∘ j ≐ id ⊸ f ∘ j
-- --   nL : ∀{A B C D E F} {f : just A ⇒ D} {g : just E ⇒ B} {h : just C ⇒ F}
-- --     → (f ⊸ g) ⊸ (id ⊸ h) ∘ L ≐ id ⊸ (f ⊸ id) ∘ L ∘ g ⊸ h

-- --   -- skew closed axioms
-- --   LLL : ∀{A B C D} → id ⊸ L {A} ∘ L {B}{C}{D} ≐ L ⊸ id ∘ L ∘ L
-- --   ijL : ∀{A C} → i j ∘ L ≐ id {A ⊸ C}
-- --   Lj : ∀{A B} → L ∘ j ≐ j {A ⊸ B}
-- --   iL : ∀{A B C} {e : nothing ⇒ A} → id ⊸ i e ∘ L {A} {B} {C} ≐ i e ⊸ id
-- --   ij : ∀{A} {e : nothing ⇒ A} → i e ∘ j ≐ e

-- -- ≡-to-≐ : ∀{A}{B}{f g : A ⇒ B} → f ≡ g → f ≐ g
-- -- ≡-to-≐ refl = refl

-- -- -- equational reasoning sugar for ≐

-- -- infix 4 _≐'_
-- -- infix 1 proof≐_
-- -- infixr 2 _≐〈_〉_
-- -- infix 3 _qed≐

-- -- data _≐'_ {S : Stp}{B : Fma} (f g : S ⇒ B) : Set where
-- --   relto :  f ≐ g → f ≐' g

-- -- proof≐_ : ∀{S B} {f g : S ⇒ B} → f ≐' g → f ≐ g
-- -- proof≐ relto p = p

-- -- _≐〈_〉_ :  ∀{S B} (f : S ⇒ B) {g h : S ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
-- -- _ ≐〈 p 〉 relto q = relto (p ∙ q)

-- -- _qed≐  :  ∀{S B} (f : S ⇒ B) → f ≐' f
-- -- _qed≐ _ = relto refl

