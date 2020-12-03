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

-- We have not proved anything about preservation of equations (well,
-- in particular since we haven't equipped the combinatory logic with
-- any equations at all). Surely there is a way to define an
-- equational theory on combinators that matches precisely the
-- equational theory of the categorial calculus, so that the functions
-- ⇒2↦-j and ⇒2↦-n send equivalent derivations to equivalent
-- derivations directly. Subsequently it should then not be hard to
-- prove that the same holds for ↦2⇒.


