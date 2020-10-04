{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import SkMults

module Sound where --(M : SkMult) where

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

infix 20 [_∣_]f

[_∣_]f : ∀ Γ {B C} → just B ⇒ C → just [ Γ ∣ B ] ⇒ [ Γ ∣ C ]
[ [] ∣ g ]f = g
[ A ∷ Γ ∣ g ]f = id ⊸ [ Γ ∣ g ]f

[_∣id]f : ∀ Γ {C} → [ Γ ∣ id {C} ]f ≐ id
[ [] ∣id]f = refl
[ A ∷ Γ ∣id]f = (refl ⊸ [ Γ ∣id]f) ∙ f⊸id

[_∣∘]f : (Γ : Cxt) {B C D : Fma} → {f : just B ⇒ C} {g : just C ⇒ D}
  → [ Γ ∣ g ∘ f ]f ≐ [ Γ ∣ g ]f ∘ [ Γ ∣ f ]f
[ [] ∣∘]f = refl
[ A ∷ Γ ∣∘]f = (refl ⊸ [ Γ ∣∘]f) ∙ (rid ⊸ refl) ∙ f⊸∘

[_∣≐]f : (Γ : Cxt) {B C : Fma} → {f g : just B ⇒ C}
  → f ≐ g → [ Γ ∣ f ]f ≐ [ Γ ∣ g ]f
[ [] ∣≐]f p = p
[ A ∷ Γ ∣≐]f p = refl ⊸ [ Γ ∣≐]f p

φ : (Γ Δ : Cxt) (C : Fma) → [ Γ ++ Δ ∣ C ] ≡ [ Γ ∣ [ Δ ∣ C ] ]
φ [] Δ C = refl
φ (A ∷ Γ) Δ C = cong (_⊸_ A) (φ Γ Δ C)

{-# REWRITE φ #-}

L⋆ : (Γ : Cxt) {B C : Fma} → just (B ⊸ C) ⇒ [ Γ ∣ B ] ⊸ [ Γ ∣ C ]
L⋆ [] = id
L⋆ (A ∷ Γ) = L ∘ L⋆ Γ

nL⋆ : ∀ Γ {A}{B}{C} (g : just B ⇒ C)
  → L⋆ Γ ∘ g ⊸ id {A} ≐ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
nL⋆ [] g = lid ∙ rid
nL⋆ (_ ∷ Γ) g = 
  proof≐
    L ∘ L⋆ Γ ∘ g ⊸ id
  ≐〈 ass 〉
    L ∘ (L⋆ Γ ∘ g ⊸ id)
  ≐〈 refl ∘ nL⋆ Γ g 〉
    L ∘ ([ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ)
  ≐〈 (~ ass) ∙ (~ lid ∘ refl ∘ refl) 〉
    id ∘ L ∘ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
  ≐〈 ~ (refl ⊸ f⊸id ∙ f⊸id) ∘ refl ∘ refl ∘ refl 〉 
    id ⊸ (id ⊸ id) ∘ L ∘ [ Γ ∣ g ]f ⊸ id ∘ L⋆ Γ
  ≐〈 (~ nL) ∘ refl 〉
    id ⊸ [ Γ ∣ g ]f ⊸ (id ⊸ id) ∘ L ∘ L⋆ Γ
  ≐〈 refl ⊸ f⊸id ∘ refl ∘ refl 〉
    id ⊸ [ Γ ∣ g ]f ⊸ id ∘ L ∘ L⋆ Γ
  ≐〈 ass 〉
    id ⊸ [ Γ ∣ g ]f ⊸ id ∘ (L ∘ L⋆ Γ)
  qed≐

nL⋆2 : ∀ Γ {A}{B}{C} (g : just B ⇒ C)
  → L⋆ Γ ∘ id {A} ⊸ g ≐ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
nL⋆2 [] g = lid ∙ rid
nL⋆2 (_ ∷ Γ) g =
  proof≐
    L ∘ L⋆ Γ ∘ id ⊸ g
  ≐〈 ass 〉
    L ∘ (L⋆ Γ ∘ id ⊸ g)
  ≐〈 refl ∘ nL⋆2 Γ g 〉
    L ∘ (id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ)
  ≐〈 (~ ass) ∙ (~ lid ∘ refl ∘ refl) 〉
    id ∘ L ∘ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
  ≐〈 ~ (refl ⊸ f⊸id ∙ f⊸id) ∘ refl ∘ refl ∘ refl 〉
    id ⊸ (id ⊸ id) ∘ L ∘ id ⊸ [ Γ ∣ g ]f ∘ L⋆ Γ
  ≐〈 (~ nL) ∘ refl 〉
    (id ⊸ id) ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ L ∘ L⋆ Γ
  ≐〈 f⊸id ⊸ refl ∘ refl ∘ refl 〉
    id ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ L ∘ L⋆ Γ
  ≐〈 ass 〉
    id ⊸ (id ⊸ [ Γ ∣ g ]f) ∘ (L ∘ L⋆ Γ)
  qed≐


φf : ∀ Γ Δ {A}{B} {g : just A ⇒ B}
  → [ Γ ++ Δ ∣ g ]f ≡ [ Γ ∣ [ Δ ∣ g ]f ]f
φf [] Δ = refl
φf (A ∷ Γ) Δ = cong (_⊸_ id) (φf Γ Δ)

{-# REWRITE φf #-}


L⋆LL⋆ : ∀ Γ Δ Λ {A} {B} {C}
  → L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ) ≐ id ⊸ L⋆ Γ ∘ L {B} ∘ L⋆ Λ {A}{[ Δ ∣ C ]}
L⋆LL⋆ [] Δ Λ = refl
L⋆LL⋆ (B ∷ Γ) Δ Λ = 
  proof≐
    (L ∘ L⋆ Γ) ⊸ id ∘ L ∘ (L ∘ L⋆ (Γ ++ Λ))
  ≐〈 ∘⊸id ∘ refl ∘ refl 〉
    L⋆ Γ ⊸ id ∘ L ⊸ id ∘ L ∘ (L ∘ L⋆ (Γ ++ Λ))
  ≐〈 (~ ass) ∙ ((ass ∘ refl) ∙ ass ∘ refl) 〉
    L⋆ Γ ⊸ id ∘ (L ⊸ id ∘ L ∘ L) ∘ L⋆ (Γ ++ Λ)
  ≐〈 refl ∘ (~ LLL) ∘ refl 〉
    L⋆ Γ ⊸ id ∘ (id ⊸ L ∘ L) ∘ L⋆ (Γ ++ Λ)
  ≐〈 (~ ass) ∘ refl 〉
    L⋆ Γ ⊸ id ∘ id ⊸ L ∘ L ∘ L⋆ (Γ ++ Λ)
  ≐〈 swap⊸ ∘ refl ∘ refl 〉
    id ⊸ L ∘ L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ)
  ≐〈 (ass ∘ refl) ∙ ass 〉
    id ⊸ L ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Λ))
  ≐〈 refl ∘ L⋆LL⋆ Γ Δ Λ 〉
    id ⊸ L ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Λ)
  ≐〈 (~ ass) ∙ (~ ass ∘ refl) 〉
    id ⊸ L ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Λ
  ≐〈 ~( id⊸∘) ∘ refl ∘ refl 〉
    id ⊸ (L ∘ L⋆ Γ) ∘ L ∘ L⋆ Λ
  qed≐

L⋆-j : ∀ Γ {C} → L⋆ Γ ∘ j {C} ≐ j 
L⋆-j [] = lid
L⋆-j (A ∷ Γ) =
  proof≐
    L ∘ L⋆ Γ ∘ j
  ≐〈 ass 〉
    L ∘ (L⋆ Γ ∘ j)
  ≐〈 refl ∘ L⋆-j Γ 〉
    L ∘ j
  ≐〈 Lj 〉
    j
  qed≐

L⋆ass : ∀ Γ Δ {A}{B} → L⋆ (Γ ++ Δ) {A}{B} ≐ L⋆ Γ ∘ L⋆ Δ
L⋆ass [] Δ = ~ lid
L⋆ass (C ∷ Γ) Δ = (refl ∘ L⋆ass Γ Δ) ∙ (~ ass)

-- soundness

sound : {S : Stp} → {Γ : Cxt} → {A : Fma} → S ∣ Γ ⊢ A → S ⇒ [ Γ ∣ A ]
sound (uf f) = id ⊸ sound f ∘ j
sound (⊸r {S}{Γ}{A}{B} f) = sound f
sound (⊸l {Γ} f g) = i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound g
sound (base f eq eq2) = base f eq eq2
sound (⊸c Δ₀ {Γ} f g) = [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound g

-- sound preserves equality

≗sound≐ : ∀ {S Γ A} {f g : S ∣ Γ ⊢ A}
  → f ≗ g → sound f ≐ sound g
≗sound≐ refl = refl
≗sound≐ (~ p) = ~ (≗sound≐ p)
≗sound≐ (p ∙ p₁) = (≗sound≐ p) ∙ (≗sound≐ p₁)
≗sound≐ (uf p) = refl ⊸ ≗sound≐ p ∘ refl
≗sound≐ (⊸r p) = ≗sound≐ p
≗sound≐ (⊸l p p₁) =
  i (≗sound≐ p) ∘ refl ∘ (refl ⊸ ≗sound≐ p₁)
≗sound≐ ⊸ruf = refl
≗sound≐ ⊸r⊸l = refl
≗sound≐ (⊸c Δ₀ p q) =
  [ Δ₀ ∣≐]f (refl ∘ i (≗sound≐ p) ⊸ refl ∘ refl) ∘ ≗sound≐ q
≗sound≐ ⊸r⊸c = refl
≗sound≐ ⊸cuf =
  ~ ass
  ∙ (~ f⊸∘ ∙ lid ⊸ refl ∘ refl)
≗sound≐ (⊸c⊸l {Γ} {Δ} {Γ'} {f = f} {f'} {g}) =
  proof≐
    [ Γ ++ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘
      (i (sound f) ∘ L⋆ Γ ∘ (id ⊸ sound g))
  ≐〈 ~ ass ∙ (~ ass ∘ refl) 〉
--    [ Γ ++ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘ i (sound f)
--        ∘ L⋆ Γ ∘ id ⊸ sound g
--  ≐〈 ~ (≡-to-≐ [ Γ ∣ Δ ∣ass]f ) ∘ refl ∘ refl ∘ refl 〉
    [ Γ ∣ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f ∘
      i (sound f)
        ∘ L⋆ Γ ∘  id ⊸ sound g
  ≐〈 ni2 ∘ refl ∘ refl 〉 
    i (sound f) ∘
      (id ⊸ [ Γ ∣ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f)
        ∘ L⋆ Γ ∘  id ⊸ sound g
  ≐〈 ass ∘ refl 〉 
    i (sound f) ∘
      ((id ⊸ [ Γ ∣ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f)
        ∘ L⋆ Γ) ∘ 
        id ⊸ sound g
  ≐〈 refl ∘ ~ nL⋆2 Γ _ ∘ refl 〉 
    i (sound f) ∘
      (L⋆ Γ ∘ id ⊸ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f) ∘
        id ⊸ sound g
  ≐〈 ~ ass ∘ refl 〉 
    i (sound f) ∘ L⋆ Γ ∘
      (id ⊸ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f) ∘
        id ⊸ sound g
  ≐〈 ass 〉 
    i (sound f) ∘ L⋆ Γ ∘
      ((id ⊸ [ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f) ∘
        (id ⊸ sound g))
  ≐〈 refl ∘ ~ f⊸∘ 〉 
    i (sound f) ∘ L⋆ Γ ∘
      ((id  ∘ id) ⊸
       ([ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘ sound g))
  ≐〈 refl ∘ lid ⊸ refl 〉 
    i (sound f) ∘ L⋆ Γ ∘
      (id ⊸
       ([ Δ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘ sound g))
  qed≐
≗sound≐ (⊸c⊸c {Γ = Γ} {Γ'} {Δ₀} {Δ₁} {A = A} {B} {f = f} {f'} {g}) =
  proof≐
    [ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ∣
      (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f
      ∘ ([ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g)
  ≐〈 ~ ass 〉 
--    [ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f
--      ∘ [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g
--  ≐〈 ≡-to-≐ (sym [ Δ₀ ∣ _ ∷ Γ ++ Δ₁ ∣ass]f) ∘ refl ∘ refl 〉 
    [ Δ₀ ∣ id ⊸  [ Γ ++ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f
      ∘ [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g
  ≐〈 ~ [ Δ₀ ∣∘]f ∙ [ Δ₀ ∣≐]f (~ ass ∙ (~ ass ∘ refl)) ∘ refl 〉 
    [ Δ₀ ∣ id ⊸  [ Γ ++ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f 
      ∘ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g
  ≐〈 [ Δ₀ ∣≐]f (~ swap⊸ ∘ refl ∙ (ass ∙ (refl ∘
       (~ swap⊸ ∙ (refl ∘ refl ⊸ refl)) ∙ ~ ass)) --≡-to-≐ (sym [ Γ ∣ Δ₁ ∣ass]f)
         ∘ refl) ∘ refl 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘
      (id ⊸ [ Γ ∣ [ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f)
        ∘ L⋆ Γ ]f ∘
       sound g
  ≐〈 [ Δ₀ ∣≐]f (ass ∙ (refl ∘ ~ nL⋆2 Γ _)) ∘ refl 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ (L⋆ Γ ∘
      id ⊸ [ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f) ]f ∘
       sound g
  ≐〈 [ Δ₀ ∣≐]f (~ ass) ∘ refl 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ∘
      id ⊸ [ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f ∘
       sound g
  ≐〈 [ Δ₀ ∣∘]f ∘ refl 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘
      [ Δ₀ ∣ id ⊸ [ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ]f ∘
       sound g
--  ≐〈 refl ∘ ≡-to-≐ [ Δ₀ ∣ _ ∷ Δ₁ ∣ass]f ∘ refl 〉 
--    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘
--      [ Δ₀ ++ B ∷ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘
--       sound g
  ≐〈 ass 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘
      ([ Δ₀ ++ B ∷ Δ₁ ∣ (L⋆ Γ' ⊸ id) ∘ (i (sound f') ⊸ id) ∘ L⋆ Γ' ]f ∘
       sound g)
  qed≐
≗sound≐ baseuf = baseuf
≗sound≐ ⊸cuf2 = {!!}
≗sound≐ ⊸c⊸l2 = {!!}
≗sound≐ ⊸c⊸c2 = {!!}




{-
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

-}
