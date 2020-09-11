{-# OPTIONS --rewriting #-}

module Sound where

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

-- ====================================================================

-- interpretation of sequents into morphisms

t : Stp → Fma
t nothing = I
t (just A) = A

[_∣_] : Cxt → Fma → Fma
[ [] ∣ C ] = C
[ A ∷ Γ ∣ C ] = A ⊸ [ Γ ∣ C ]

[_∣_]f : (Γ : Cxt) {B C : Fma} → B ⇒ C → [ Γ ∣ B ] ⇒ [ Γ ∣ C ]
[ [] ∣ g ]f = g
[ A ∷ Γ ∣ g ]f = id ⊸ [ Γ ∣ g ]f

[_∣id]f : ∀ Γ {C} → [ Γ ∣ id {C} ]f ≐ id
[ [] ∣id]f = refl
[ A ∷ Γ ∣id]f = (refl ⊸ [ Γ ∣id]f) ∙ f⊸id

[_∣∘]f : (Γ : Cxt) {B C D : Fma} → {f : B ⇒ C} {g : C ⇒ D} → [ Γ ∣ g ∘ f ]f ≐ [ Γ ∣ g ]f ∘ [ Γ ∣ f ]f
[ [] ∣∘]f = refl
[ A ∷ Γ ∣∘]f = (refl ⊸ [ Γ ∣∘]f) ∙ (rid ⊸ refl) ∙ f⊸∘

[_∣≐]f : (Γ : Cxt) {B C : Fma} → {f g : B ⇒ C} → f ≐ g → [ Γ ∣ f ]f ≐ [ Γ ∣ g ]f
[ [] ∣≐]f p = p
[ A ∷ Γ ∣≐]f p = refl ⊸ [ Γ ∣≐]f p

φ : (Γ Δ : Cxt) (C : Fma) → [ Γ ++ Δ ∣ C ] ≡ [ Γ ∣ [ Δ ∣ C ] ]
φ [] Δ C = refl
φ (A ∷ Γ) Δ C = cong (_⊸_ A) (φ Γ Δ C)

{-# REWRITE φ #-}

L⋆ : (Γ : Cxt) {B C : Fma} → B ⊸ C ⇒ [ Γ ∣ B ] ⊸ [ Γ ∣ C ]
L⋆ [] = id
L⋆ (A ∷ Γ) = L ∘ L⋆ Γ

-- soundness

sound : {S : Stp} → {Γ : Cxt} → {A : Fma} → S ∣ Γ ⊢ A → t S ⇒ [ Γ ∣ A ]
sound ax = id
sound (uf f) = id ⊸ sound f ∘ j
sound Ir = id
sound (⊸r {S}{Γ}{A}{B} f) = sound f
sound (Il f) = sound f
sound (⊸l {Γ} f g) = i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g 

-- sound preserves equality

≗sound≐ : ∀ {S Γ A} {f g : S ∣ Γ ⊢ A}
  → f ≗ g → sound f ≐ sound g
≗sound≐ refl = refl
≗sound≐ (~ p) = ~ (≗sound≐ p)
≗sound≐ (p ∙ p₁) = (≗sound≐ p) ∙ (≗sound≐ p₁)
≗sound≐ (uf p) = refl ⊸ ≗sound≐ p ∘ refl
≗sound≐ (⊸r p) = ≗sound≐ p
≗sound≐ (Il p) = ≗sound≐ p
≗sound≐ (⊸l p p₁) =
  refl ∘ ≗sound≐ p ⊸ refl ∘ refl ∘ refl ⊸ ≗sound≐ p₁
≗sound≐ axI = refl
≗sound≐ ax⊸ =
  (~ ijL)
  ∙ (refl ∘ (~ lid) ⊸ refl ∘ refl)
  ∙ rid
  ∙ (refl ∘ ((~ f⊸id) ∘ refl) ⊸ refl ∘ rid ∘ (~ f⊸id))
≗sound≐ ⊸ruf = refl
≗sound≐ ⊸rIl = refl
≗sound≐ ⊸r⊸l = refl

