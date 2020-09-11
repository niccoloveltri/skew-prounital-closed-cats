{-# OPTIONS --rewriting #-}

module Formulae where

open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Maybe

-- =======================================================================

-- generating objects At ("atomic formulae")

postulate At : Set

-- =======================================================================

-- -- Formulae

infixl 25 _⊸_

data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊸_ : Fma → Fma → Fma


Stp : Set
Stp = Maybe Fma

Cxt : Set
Cxt = List Fma

not⊸ : Fma → Set
not⊸ (` X) = ⊤
not⊸ I = ⊤
not⊸ (A ⊸ B) = ⊥

