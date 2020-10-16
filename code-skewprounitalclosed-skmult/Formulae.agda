{-# OPTIONS --rewriting #-}

open import SkMults

module Formulae where

open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (_≗_)

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

-- Interpretation of pairs of a list and a formula into formulae

[_∣_] : List Fma → Fma → Fma
[ [] ∣ C ] = C
[ A ∷ Γ ∣ C ] = A ⊸ [ Γ ∣ C ]

