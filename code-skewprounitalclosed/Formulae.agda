{-# OPTIONS --rewriting #-}

module Formulae where

open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding (_≗_)

-- =======================================================================

-- generating objects At ("atomic formulae")

postulate At : Set

-- =======================================================================

-- -- Formulae

infixl 25 _⊸_

data Fma : Set where
  ` : At → Fma
  _⊸_ : Fma → Fma → Fma


Stp : Set
Stp = Maybe Fma

Cxt : Set
Cxt = List Fma

not⊸ : Fma → Set
not⊸ (` X) = ⊤
not⊸ (A ⊸ B) = ⊥

asCxt : Stp → Cxt → Cxt
asCxt nothing Γ = Γ
asCxt (just A) Γ = A ∷ Γ

asCxt++ : (S : Stp) (Γ Δ : Cxt)
  → asCxt S (Γ ++ Δ) ≡ asCxt S Γ ++ Δ
asCxt++ nothing Γ Δ = refl
asCxt++ (just _) Γ Δ = refl

{-# REWRITE asCxt++ #-}


