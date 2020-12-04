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
open import SoundComplete
open import Sound
open import SeqCalc
open import Complete

-- combinatory logic
data ↦_ : Fma → Set where
  I : {A : Fma} → ↦ A ⊸ A
  b : {A B C : Fma} → ↦ (B ⊸ C) ⊸ ((A ⊸ B) ⊸ (A ⊸ C))
  c : {A B : Fma} → ↦ A → ↦ (A ⊸ B) ⊸ B
  mp : {A B : Fma} → ↦ A ⊸ B → ↦ A → ↦ B

id⊸ : {A C D : Fma} (g : just C ⇒ D) → just (A ⊸ C) ⇒ A ⊸ D
id⊸ g = jY-1 (L ∘ jY g)

_⊸id : {A B C : Fma} (f : just B ⇒ A) → just (A ⊸ C) ⇒ B ⊸ C
f ⊸id = i (id⊸ f ∘ j) ∘ L

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

-- we construct translations between derivation in combinatory logic
-- and derivations in the categorical calculus
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

-- Here is a possible equational theory for the combinatory
-- logic. Surely this is not optimal, but we show that this is at
-- least complete. It should be possible (though tedious) to prove
-- that it is also sound.

infix 15 _≐c_

data _≐c_ : {B : Fma} → ↦ B → ↦ B → Set where
  refl : ∀{B} {f : ↦ B} → f ≐c f
  ~_ : ∀{B} {f g : ↦ B} → f ≐c g → g ≐c f
  _∙_ : ∀{B} {f g h : ↦ B} → f ≐c g → g ≐c h → f ≐c h
  mp : ∀{B C} {f g : ↦ B ⊸ C} {h k : ↦ B} →
                         f ≐c g → h ≐c k → mp f h ≐c mp g k
  lid : ∀{B} {f : ↦ B} → mp I f ≐c f
  lid-j : ∀{A B} {f : ↦ A ⊸ B} → I ∘c f ≐c f
  ass : ∀{B C D} {f : ↦ C ⊸ D} {g : ↦ B ⊸ C} {h : ↦ B}
      → mp (f ∘c g) h ≐c mp f (mp g h)
  ass-j : ∀{A B C D} {f : ↦ C ⊸ D} {g : ↦ B ⊸ C} {h : ↦ A ⊸ B}
      → (f ∘c g) ∘c h ≐c f ∘c (g ∘c h)
  rid : ∀{A B} {f : ↦ A ⊸ B} → f ≐c (f ∘c I)
  f⊸∘ : ∀{A B C D E F}
    → {f : ↦ A ⊸ C}{g : ↦ B ⊸ D}
    → {h : ↦ C ⊸ E}{k : ↦ D ⊸ F}
    → (h ∘c f) ⊸c (k ∘c g) ≐c (f ⊸c k) ∘c (h ⊸c g)
  c : ∀{A B} {f g : ↦ A} → f ≐c g → c {A}{B} f ≐c c g
  nc : ∀{A A' B B'} {a : ↦ A} {g : ↦ B ⊸ B'} {h : ↦ A ⊸ A'}
     → (g ∘c c a) ∘c (h ⊸c I) ≐c c (mp h a) ∘c (I ⊸c g)
  nI : ∀{A A'} {f : ↦ A ⊸ A'} → mp (f ⊸c I) I ≐c mp (I ⊸c f) I
  nb : ∀{A A' C C' D D'} {f : ↦ A ⊸ A'} {g : ↦ D' ⊸ D} {h : ↦ C ⊸ C'}
    → ((f ⊸c g) ⊸c (I ⊸c h)) ∘c b ≐c ((I ⊸c (f ⊸c I)) ∘c b) ∘c (g ⊸c h)
  bbb : ∀{A B C D} → (I ⊸c b {A}) ∘c b {B}{C}{D} ≐c ((b ⊸c I) ∘c b) ∘c b
  cIb : ∀{A C} → c I ∘c b ≐c I {A ⊸ C}
  bI : ∀{A B} → mp b I ≐c I {A ⊸ B}
  cb : ∀{A B C} {a : ↦ A} → ((id⊸c (c a)) ∘c (b {A} {B} {C})) ≐c (c a c⊸id)
  cI : ∀{A} {a : ↦ A} → mp (c a) I ≐c a

≐2≐c-j : ∀{A B} {f g : just A ⇒ B} → f ≐ g → ⇒2↦-j f ≐c ⇒2↦-j g
≐2≐c-n : ∀{B} {f g : nothing ⇒ B} → f ≐ g → ⇒2↦-n f ≐c ⇒2↦-n g

≐2≐c-j refl = refl
≐2≐c-j (~ p) = ~ ≐2≐c-j p
≐2≐c-j (p ∙ p₁) = ≐2≐c-j p ∙ ≐2≐c-j p₁
≐2≐c-j (p ∘ p₁) = mp (mp refl (≐2≐c-j p)) (≐2≐c-j p₁)
≐2≐c-j (p ⊸ p₁) = mp (mp refl (mp refl (≐2≐c-j p₁))) (mp (mp refl (c (≐2≐c-j p))) refl)
≐2≐c-j lid = lid-j
≐2≐c-j rid = rid
≐2≐c-j ass = ass-j
≐2≐c-j f⊸id =
  mp (mp refl bI) refl
  ∙ mp bI refl
  ∙ lid
  ∙ cIb
≐2≐c-j f⊸∘ = f⊸∘
≐2≐c-j (i p) = c (≐2≐c-n p)
≐2≐c-j ni = nc
≐2≐c-j nL = nb
≐2≐c-j LLL = bbb
≐2≐c-j ijL = cIb
≐2≐c-j iL =
  mp (mp refl (mp refl cIb)) refl
  ∙ mp (mp refl (~ rid)) refl
  ∙ ~ lid
  ∙ mp (~ bI ∙ mp refl (~ bI)) cb

≐2≐c-n refl = refl
≐2≐c-n (~ p) = ~ ≐2≐c-n p
≐2≐c-n (p ∙ p₁) = ≐2≐c-n p ∙ ≐2≐c-n p₁
≐2≐c-n (p ∘ p₁) = mp (≐2≐c-j p) (≐2≐c-n p₁)
≐2≐c-n lid = lid
≐2≐c-n ass = ass
≐2≐c-n nj = nI
≐2≐c-n Lj = bI
≐2≐c-n ij = cI


-- congjY-1 : ∀{A}{B} {f g : nothing ⇒ A ⊸ B} → f ≐ g → jY-1 f ≐ jY-1 g
-- congjY-1 p = ≗sound≐ (conguf-1 (cong⊸r-1 (≐cmplt≗ p)))
-- 
-- ≐c2≐ : ∀{B} {f g : ↦ B} → f ≐c g → ↦2⇒ f ≐ ↦2⇒ g
-- ≐c2≐ refl = refl
-- ≐c2≐ (~ p) = ~ ≐c2≐ p
-- ≐c2≐ (p ∙ p₁) = ≐c2≐ p ∙ ≐c2≐ p₁
-- ≐c2≐ (mp p p₁) = congjY-1 (≐c2≐ p) ∘ ≐c2≐ p₁
-- ≐c2≐ lid = lid
-- ≐c2≐ lid-j =
--   congjY-1 (left-normal₂ L ∘ (refl {f = j}))
--            ∙ (i (f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘ f⊸id)
--            ∙ ~ rid
--            ∙ ijL
--            ∘ refl
--   ∙ lid
-- ≐c2≐ (ass {f = f}{g}) =
--   congjY-1 (congjY-1 (left-normal₂ L ∘ refl {f = ↦2⇒ f}) ∘ refl {f = ↦2⇒ g})
--   ∙ {!!}
--   ∘ refl
--   ∙ ass
-- ≐c2≐ ass-j = {!!}
-- ≐c2≐ rid = {!!}
-- ≐c2≐ f⊸∘ = {!!}
-- ≐c2≐ (c p) = i (≐c2≐ p) ⊸ refl ∘ refl
-- ≐c2≐ nc = {!!}
-- ≐c2≐ nI = {!!}
-- ≐c2≐ nb = {!!}
-- ≐c2≐ bbb = {!!}
-- ≐c2≐ cIb = {!!}
-- ≐c2≐ bI = left-normal₂ L ∘ refl ∙ Lj
-- ≐c2≐ (cb {a = g}) =
--   congjY-1 (left-normal₂ L ∘ (left-normal₂ L ∘ refl {f = jY (i (↦2⇒ g))})) ∘ refl
--   ∙ ass
--   ∙ (refl ∘ (refl ⊸ (i (f⊸id ∘ refl ∙ lid) ∘ ~ rid ∙ ijL ∘ refl ⊸ (ass ∙ ((i (soundcmplt (↦2⇒ g)) ∘ (lid ∙ f⊸id)) ∙ ~ rid))) ∘ refl
--             ∙ (refl ⊸ lid ∘ refl)
--             ∙ {!!}))
--   ∙ ~ ass
--   ∙ ~ (congjY-1 (left-normal₂ L ∘ refl {f = jY (i (jY (i (↦2⇒ g))))}) ∘ refl)
-- ≐c2≐ (cI {a = g}) =
--   left-normal₂ (i (↦2⇒ g)) ∘ refl ∙ ij
