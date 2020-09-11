{-# OPTIONS --rewriting #-}

module SoundComplete where

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
open import Sound
open import Complete
open import MulticatLaws

sound-Il-1 : {Γ : Cxt} → {C : Fma} → 
              (f : just I ∣ Γ ⊢ C) → sound (Il-1 f) ≐ sound f
sound-Il-1 ax = refl
sound-Il-1 (⊸r f) = sound-Il-1 f
sound-Il-1 (Il f) = refl

sem-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           t S ⇒ [ Γ ∣ A ] → A ⇒ [ Δ ∣ C ] → t S ⇒ [ Γ ++ Δ ∣ C ]
sem-scut {Γ = Γ} f g = [ Γ ∣ g ]f ∘ f

sem-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
           I ⇒ [ Γ ∣ A ]  →  t T ⇒ [ Δ ∣ C ] → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                      t T ⇒ [ Δ₀ ++ Γ ++ Δ' ∣ C ]
sem-ccut {Γ = Γ} Δ₀ f g refl = [ Δ₀ ∣ i ∘ f ⊸ id ∘ L⋆ Γ ]f ∘ g 

swap⊸ : ∀{A B C D} {f : A ⇒ C}{g : B ⇒ D}
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

id⊸∘ : ∀{A}{B}{C}{D} {f : A ⇒ B}{g : B ⇒ C}
  → id {D} ⊸ (g ∘ f) ≐ id ⊸ g ∘ id ⊸ f 
id⊸∘ = (rid ⊸ refl ) ∙ f⊸∘

∘⊸id : ∀{A}{B}{C}{D} {f : A ⇒ B}{g : B ⇒ C}
  → (g ∘ f) ⊸ id {D} ≐ f ⊸ id ∘ g ⊸ id
∘⊸id = (refl ⊸ rid) ∙ f⊸∘

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

nL⋆ : ∀ Γ {A}{B}{C} (g : B ⇒ C)
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

nL⋆2 : ∀ Γ {A}{B}{C} (g : B ⇒ C)
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

[_∣_∣ass]f : ∀ Γ Δ {A}{B} {g : A ⇒ B}
  → [ Γ ∣ [ Δ ∣ g ]f ]f ≡ [ Γ ++ Δ ∣ g ]f
[ [] ∣ Δ ∣ass]f = refl
[ A ∷ Γ ∣ Δ ∣ass]f = cong (_⊸_ id) [ Γ ∣ Δ ∣ass]f

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

mutual
  sound-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} →
             (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C) →
             sound (scut f g) ≐ sem-scut {S}{Γ}{Δ} (sound f) (sound g)
  sound-scut ax g = rid
  sound-scut (uf {Γ} f) g =
    proof≐
      id ⊸ sound (scut f g) ∘ j
    ≐〈 refl ⊸ sound-scut f g ∘ refl 〉 
      id ⊸ ([ Γ ∣ sound g ]f ∘ sound f) ∘ j
    ≐〈 id⊸∘ ∘ refl 〉 
      id ⊸ [ Γ ∣ sound g ]f ∘ id ⊸ sound f ∘ j
    ≐〈 ass 〉 
      id ⊸ [ Γ ∣ sound g ]f ∘ (id ⊸ sound f ∘ j)
    qed≐
  sound-scut Ir g = sound-Il-1 g ∙ rid
  sound-scut {Γ = Γ} (⊸r f) ax = (~ lid) ∙ ((~ [ Γ ∣id]f) ∘ refl)
  sound-scut (⊸r f) (⊸r g) = sound-scut (⊸r f) g
  sound-scut {Γ = Γ} (⊸r f) (⊸l {Γ₁} g g') =
    proof≐
      sound (scut (ccut Γ g f refl) g')
    ≐〈 sound-scut (ccut Γ g f refl) g' 〉 
      [ Γ ++ Γ₁ ∣ sound g' ]f ∘ sound (ccut Γ g f refl)
    ≐〈 refl ∘ sound-ccut Γ g f refl 〉 
      [ Γ ++ Γ₁ ∣ sound g' ]f ∘ ([ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f)
    ≐〈 ≡-to-≐ (sym [ Γ ∣ Γ₁ ∣ass]f) ∘ refl 〉 
      [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ ([ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f)
    ≐〈 ~ ass 〉 
      [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ [ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
    ≐〈 (~ [ Γ ∣∘]f) ∘ refl 〉 
      [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ Γ₁) ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f ((~ ass) ∙ ((~ ass) ∘ refl)) ∘ refl 〉 
      [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (ni ∘ refl ∘ refl) ∘ refl 〉 
      [ Γ ∣ i ∘ id ⊸ [ Γ₁ ∣ sound g' ]f ∘ sound g ⊸ id ∘ L⋆ Γ₁ ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (ass ∘ refl) ∘ refl 〉 
      [ Γ ∣ i ∘ (id ⊸ [ Γ₁ ∣ sound g' ]f ∘ sound g ⊸ id) ∘ L⋆ Γ₁ ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (refl ∘ (~ swap⊸) ∘ refl ) ∘ refl 〉 
      [ Γ ∣ i ∘ (sound g ⊸ id ∘ id ⊸ [ Γ₁ ∣ sound g' ]f) ∘ L⋆ Γ₁ ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (((~ ass) ∘ refl) ∙ ass) ∘ refl 〉 
      [ Γ ∣ i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ₁ ∣ sound g' ]f ∘ L⋆ Γ₁) ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (refl ∘ (~ (nL⋆2 Γ₁ (sound g')))) ∘ refl 〉 
      [ Γ ∣ i ∘ sound g ⊸ id ∘ (L⋆ Γ₁ ∘ id ⊸ sound g') ]f ∘ sound f
    ≐〈 [ Γ ∣≐]f (~ ass) ∘ refl 〉 
      [ Γ ∣ i ∘ sound g ⊸ id ∘ L⋆ Γ₁ ∘ id ⊸ sound g' ]f ∘ sound f
    qed≐
  sound-scut (Il f) g = sound-scut f g
  sound-scut (⊸l {Γ} {Δ} f f') g =
    proof≐
      i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound (scut f' g)
    ≐〈 refl ∘ refl ⊸ sound-scut f' g 〉 
      i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ ([ Δ ∣ sound g ]f ∘ sound f')
    ≐〈 refl ∘ id⊸∘ 〉 
      i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ (id ⊸ [ Δ ∣ sound g ]f ∘ id ⊸ sound f')
    ≐〈 (~ ass) ∙ (ass ∘ refl) 〉 
      i ∘ sound f ⊸ id ∘ (L⋆ Γ ∘ id ⊸ [ Δ ∣ sound g ]f) ∘ id ⊸ sound f'
    ≐〈 refl ∘ nL⋆2 Γ [ Δ ∣ sound g ]f ∘ refl 〉 
      i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ∣ [ Δ ∣ sound g ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
    ≐〈 refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Δ ∣ass]f  ∘ refl) ∘ refl 〉 
      i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
    ≐〈 (~ ass) ∙ (ass ∘ refl) ∘ refl 〉 
      i ∘ (sound f ⊸ id ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f) ∘ L⋆ Γ ∘ id ⊸ sound f'
    ≐〈 refl ∘ swap⊸ ∘ refl ∘ refl 〉 
      i ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ sound f ⊸ id) ∘ L⋆ Γ ∘ id ⊸ sound f'
    ≐〈 (~ ass) ∘ refl ∘ refl 〉 
      i ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f'
    ≐〈 (~ ni) ∘ refl ∘ refl ∘ refl 〉 
      [ Γ ++ Δ ∣ sound g ]f ∘ i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f'
    ≐〈 ((ass ∘ refl) ∙ ass ∘ refl) ∙ ass 〉 
      [ Γ ++ Δ ∣ sound g ]f ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound f')
    qed≐
  
  sound-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
               (f : nothing ∣ Γ ⊢ A)  → (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                sound (ccut Δ₀ f g r) ≐ sem-ccut {T}{Γ} Δ₀ (sound f) (sound g) r              
  sound-ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  sound-ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
  sound-ccut {Γ = Γ} .[] f (uf g) refl | inj₁ (refl , refl , refl) =
    proof≐
      sound (scut f g)
    ≐〈 sound-scut f g 〉
      [ Γ ∣ sound g ]f ∘ sound f
    ≐〈 rid 〉 
      [ Γ ∣ sound g ]f ∘ sound f ∘ id
    ≐〈 refl ∘ (~ ij) 〉 
      [ Γ ∣ sound g ]f ∘ sound f ∘ (i ∘ j)
    ≐〈 (~ ass) ∙ (ass ∘ refl) 〉 
      [ Γ ∣ sound g ]f ∘ (sound f ∘ i) ∘ j
    ≐〈 refl ∘ ni ∘ refl 〉 
      [ Γ ∣ sound g ]f ∘ (i ∘ id ⊸ sound f) ∘ j
    ≐〈 ((~ ass) ∘ refl) ∙ ass 〉 
      [ Γ ∣ sound g ]f ∘ i ∘ (id ⊸ sound f ∘ j)
    ≐〈 ni ∘ (~ nj) 〉 
      i ∘ id ⊸ [ Γ ∣ sound g ]f ∘ (sound f ⊸ id ∘ j)
    ≐〈 (~ ass) ∙ (ass ∘ refl) 〉 
      i ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ sound f ⊸ id) ∘ j
    ≐〈 refl ∘ (~ swap⊸) ∘ ~ (L⋆-j Γ) 〉 
      i ∘ (sound f ⊸ id ∘ id ⊸ [ Γ ∣ sound g ]f) ∘ (L⋆ Γ ∘ j)
    ≐〈 (~ ass) ∙ (((~ ass) ∘ refl) ∙ ass ∘ refl) 〉 
      i ∘ sound f ⊸ id ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ L⋆ Γ) ∘ j
    ≐〈 refl ∘ (~ (nL⋆2 Γ (sound g)))  ∘ refl 〉 
      i ∘ sound f ⊸ id ∘ (L⋆ Γ ∘ id ⊸ sound g) ∘ j
    ≐〈 ((~ ass) ∘ refl) ∙ ass 〉 
      i ∘ sound f ⊸ id ∘ L⋆ Γ ∘ (id ⊸ sound g ∘ j)
    qed≐
  sound-ccut {Γ = Γ} .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    proof≐
      id ⊸ sound (ccut Γ₀ f g refl) ∘ j
    ≐〈 refl ⊸ sound-ccut Γ₀ f g refl ∘ refl 〉 
      id ⊸ ([ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ∘ j
    ≐〈 (id⊸∘ ∘ refl) ∙ ass 〉 
      id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (id ⊸ sound g ∘ j)
    qed≐
  sound-ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  sound-ccut Δ₀ f (⊸r g) refl = sound-ccut Δ₀ f g refl
  sound-ccut Δ₀ f (Il g) refl = sound-ccut Δ₀ f g refl
  sound-ccut Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
  sound-ccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A} {C} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
    proof≐
      i ∘ sound (ccut Δ₀ f g refl) ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ sound-ccut Δ₀ f g refl ⊸ refl ∘ refl ∘ refl 〉 
      i ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ ∘⊸id ∘ refl ∘ refl 〉 
      i ∘ (sound g ⊸ id ∘ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id) ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
    ≐〈 (~ ass ∘ refl) ∙ ass ∘ refl 〉 
      i ∘ sound g ⊸ id ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀)) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (refl ∘ L⋆ass Δ₀ (Γ ++ Γ₀)) ∘ refl 〉  
      i ∘ sound g ⊸ id ∘ ([ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Δ₀ ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (~ ass) ∙ (refl ∘ ~ (nL⋆ Δ₀ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ refl)) ∘ refl 〉 
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L⋆ (Γ ++ Γ₀)) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (refl ∘ ∘⊸id ∘ refl) ∘ refl 〉 
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id) ∘ L⋆ (Γ ++ Γ₀)) ∘ id ⊸ sound g'
    ≐〈 refl ∘ ass ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'    
    ≐〈 refl ∘ (refl ∘ lemma) ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (~ ass) ∙ (refl ∘ (~ ass ∘ refl)) ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (refl ∘ ~ id⊸∘ ∘ refl ∘ refl) ∘ refl 〉 
      i ∘ sound g ⊸ id ∘ (L⋆ Δ₀ ∘ id ⊸ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (nL⋆2 Δ₀ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ refl ∘ refl) ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (ass ∙ ass) ∘ refl  〉 
      i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (L⋆ Δ₀ ∘ (L ∘ L⋆ Γ₀))) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (refl ∘ ~ (L⋆ass Δ₀ (A ∷ Γ₀))) ∘ refl 〉 
      i ∘ sound g ⊸ id ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀)) ∘ id ⊸ sound g'
    ≐〈 (~ ass) ∙ (ass ∘ refl) ∘ refl 〉 
      i ∘ (sound g ⊸ id ∘ id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
    ≐〈 refl ∘ swap⊸ ∘ refl ∘ refl 〉 
      i ∘ (id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g ⊸ id) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
    ≐〈 ~ ass ∘ refl ∘ refl 〉 
      i ∘ id ⊸ [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
    ≐〈 ~ ni ∘ refl ∘ refl ∘ refl 〉 
      [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
    ≐〈 ((ass ∘ refl) ∙ ass ∘ refl) ∙ ass 〉 
      [ Δ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g')
    qed≐
    where
      lemma : L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀) ≐ id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
      lemma =
          proof≐
            L⋆ Γ ⊸ id ∘ (i ∘ sound f ⊸ id) ⊸ id ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ ∘⊸id ∘ refl 〉
            L⋆ Γ ⊸ id ∘ (sound f ⊸ id ⊸ id ∘ i ⊸ id) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ (refl ∘ ~ iL)  ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ (sound f ⊸ id ⊸ id ∘ (id ⊸ i ∘ L)) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 (~ ass) ∙ ((~ ass) ∙ (ass ∘ refl)) ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ (sound f ⊸ id ⊸ id ∘ id ⊸ i) ∘ L ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ swap⊸ ∘ refl ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ (id ⊸ i ∘ sound f ⊸ id ⊸ id) ∘ L ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 (~ ass ∘ refl) ∙ ass ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (sound f ⊸ id ⊸ id ∘ L) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ (refl ⊸ (~ f⊸id) ∘ refl) ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (sound f ⊸ id ⊸ (id ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ nL ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L ∘ id ⊸ id) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ (refl ∘ f⊸id) ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L ∘ id) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ ~ rid ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ i ∘ (id ⊸ (sound f ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 (~ ass) ∙ (ass ∘ refl) ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ (id ⊸ i ∘ id ⊸ (sound f ⊸ id)) ∘ L ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 refl ∘ ~ id⊸∘ ∘ refl ∘ refl 〉 
            L⋆ Γ ⊸ id ∘ id ⊸ (i ∘ sound f ⊸ id) ∘ L ∘ L⋆ (Γ ++ Γ₀)
          ≐〈 ((swap⊸ ∘ refl) ∙ ass ∘ refl) ∙ ass 〉 
            id ⊸ (i ∘ sound f ⊸ id) ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Γ₀))
          ≐〈 refl ∘ L⋆LL⋆ Γ Δ Γ₀  〉 
            id ⊸ (i ∘ sound f ⊸ id) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)
          ≐〈 (~ ass) ∙ ((~ ass ∘ refl) ∙ ass) 〉 
            id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ (L ∘ L⋆ Γ₀)
          ≐〈 ~ id⊸∘ ∘ refl 〉 
            id ⊸ (i ∘ sound f ⊸ id ∘ L⋆ Γ) ∘ (L ∘ L⋆ Γ₀)
          ≐〈 (~ ass) ∙ (id⊸∘ ∘ refl ∘ refl) 〉
            id ⊸ (i ∘ sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
          qed≐
  sound-ccut {Γ = Γ'} .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
    proof≐
      i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound (ccut Γ₀ f g' refl)
    ≐〈 refl ∘ refl ⊸ sound-ccut Γ₀ f g' refl 〉
      i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ ([ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g')
    ≐〈 refl ∘ id⊸∘ 〉
      i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ (id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ id ⊸ sound g')
    ≐〈 (~ ass) ∙ (ass ∘ refl) 〉
      i ∘ sound g ⊸ id ∘ (L⋆ Γ ∘ id ⊸ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f) ∘ id ⊸ sound g'
    ≐〈 refl ∘ nL⋆2 Γ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ ∣ [ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
    ≐〈 refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Γ₀ ∣ass]f ∘ refl) ∘ refl 〉
      i ∘ sound g ⊸ id ∘ (id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
    ≐〈  (~ ass) ∙ (ass ∘ refl) ∘ refl 〉
      i ∘ (sound g ⊸ id ∘ id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f) ∘ L⋆ Γ ∘ id ⊸ sound g'
    ≐〈 refl ∘ swap⊸ ∘ refl ∘ refl 〉
      i ∘ (id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g ⊸ id) ∘ L⋆ Γ ∘ id ⊸ sound g'
    ≐〈 ~ ass ∘ refl ∘ refl 〉
      i ∘ id ⊸ [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g'
    ≐〈 ~ ni ∘ refl ∘ refl ∘ refl 〉
      [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g'
    ≐〈 ((ass ∘ refl) ∙ ass ∘ refl) ∙ ass 〉
      [ Γ ++ Γ₀ ∣ i ∘ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ (i ∘ sound g ⊸ id ∘ L⋆ Γ ∘ id ⊸ sound g')
    qed≐

soundcmplt : {A C : Fma} → (f : A ⇒ C) → sound (cmplt f) ≐ f
soundcmplt id = refl
soundcmplt (f ∘ g) =
  proof≐
    sound (scut (cmplt g) (cmplt f))
  ≐〈 sound-scut (cmplt g) (cmplt f) 〉
    sound (cmplt f) ∘ sound (cmplt g)
  ≐〈 soundcmplt f ∘ soundcmplt g 〉
    f ∘ g
  qed≐
soundcmplt (f ⊸ g) = 
  proof≐ 
    i ∘ (id ⊸ sound (cmplt f) ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ sound (cmplt g)
  ≐〈 refl ∘ (refl ⊸ soundcmplt f ∘ refl) ⊸ refl ∘ ~ rid ∘ refl ⊸ soundcmplt g 〉
    i ∘ (id ⊸ f ∘ j) ⊸ id ∘ L ∘ id ⊸ g
  ≐〈 refl ∘ (~ nj) ⊸ rid ∘ refl ∘ refl 〉
    i ∘ (f ⊸ id ∘ j) ⊸ (id ∘ id) ∘ L ∘ id ⊸ g
  ≐〈 refl ∘ f⊸∘ ∘ refl ∘ refl 〉
    i ∘ (j ⊸ id ∘ f ⊸ id ⊸ id) ∘ L ∘ id ⊸ g
  ≐〈 (~ ass ∘ refl) ∙ ass ∘ refl 〉
    i ∘ j ⊸ id ∘ (f ⊸ id ⊸ id ∘ L) ∘ id ⊸ g
  ≐〈 refl ∘ (~ (refl ⊸ f⊸id) ∘ refl) ∘ refl  〉
    i ∘ j ⊸ id ∘ (f ⊸ id ⊸ (id ⊸ id) ∘ L) ∘ id ⊸ g
  ≐〈 refl ∘ nL ∘ refl 〉
    i ∘ j ⊸ id ∘ (id ⊸ (f ⊸ id) ∘ L ∘ id ⊸ id) ∘ id ⊸ g
  ≐〈 refl ∘ (refl ∘ f⊸id) ∘ refl 〉
    i ∘ j ⊸ id ∘ (id ⊸ (f ⊸ id) ∘ L ∘ id) ∘ id ⊸ g
  ≐〈 (~ ass) ∙ ((~ ass) ∙ (ass ∘ refl) ∘ refl) ∘ refl 〉
    i ∘ (j ⊸ id ∘ id ⊸ (f ⊸ id)) ∘ L ∘ id ∘ id ⊸ g
  ≐〈 ~ rid ∘ refl 〉
    i ∘ (j ⊸ id ∘ id ⊸ (f ⊸ id)) ∘ L ∘ id ⊸ g
  ≐〈 refl ∘ ~ f⊸∘ ∘ refl ∘ refl 〉
    i ∘ (id ∘ j) ⊸ (id ∘ f ⊸ id) ∘ L ∘ id ⊸ g
  ≐〈 refl ∘ (lid ∙ rid) ⊸ (lid ∙ rid) ∘ refl ∘ refl 〉 
    i ∘ (j ∘ id) ⊸ (f ⊸ id ∘ id) ∘ L ∘ id ⊸ g
  ≐〈 refl ∘ f⊸∘ ∘ refl ∘ refl  〉
    i ∘ (id ⊸ (f ⊸ id) ∘ j ⊸ id) ∘ L ∘ id ⊸ g
  ≐〈 ~ ass ∘ refl ∘ refl 〉
    i ∘ id ⊸ (f ⊸ id) ∘ j ⊸ id ∘ L ∘ id ⊸ g
  ≐〈 ~ ni ∘ refl ∘ refl ∘ refl 〉
    f ⊸ id ∘ i ∘ j ⊸ id ∘ L ∘ id ⊸ g
  ≐〈 (ass ∘ refl) ∙ ass ∘ refl 〉
    f ⊸ id ∘ (i ∘ j ⊸ id ∘ L) ∘ id ⊸ g
  ≐〈 refl ∘ ijL ∘ refl 〉
    f ⊸ id ∘ id ∘ id ⊸ g
  ≐〈 ~ (rid ∘ refl) 〉
    f ⊸ id ∘ id ⊸ g
  ≐〈 ~ f⊸∘ 〉
    (id ∘ f) ⊸ (id ∘ g)
  ≐〈 lid ⊸ lid 〉
    f ⊸ g
  qed≐
soundcmplt i =
  proof≐
    i ∘ id ⊸ id ∘ id ∘ id ⊸ id
  ≐〈 refl ∘ f⊸id ∘ refl ∘ f⊸id 〉
    i ∘ id ∘ id ∘ id
  ≐〈 ~ (rid ∙ (rid ∙ rid)) 〉
    i
  qed≐
soundcmplt j = (f⊸id ∘ refl) ∙ lid
soundcmplt L =
  proof≐
    i ∘ (id ⊸ (i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ id) ∘ id ⊸ id) ∘ j) ⊸ id ∘ (L ∘ (L ∘ id)) ∘ id ⊸ id
  ≐〈 refl ∘ (refl ⊸ (refl ∘ (f⊸id ∘ refl) ⊸ refl  ∘ ~ rid ∘ f⊸id) ∘ refl) ⊸ refl  ∘ (refl ∘ ~ rid) ∘ f⊸id 〉
    i ∘ (id ⊸ (i ∘ (id ∘ j) ⊸ id ∘ L ∘ id) ∘ j) ⊸ id ∘ (L ∘ L) ∘ id
  ≐〈 ~ rid 〉
    i ∘ (id ⊸ (i ∘ (id ∘ j) ⊸ id ∘ L ∘ id) ∘ j) ⊸ id ∘ (L ∘ L)
  ≐〈 refl ∘ (refl ⊸ (~ rid ∙ (refl ∘ (lid ⊸ refl) ∘ refl)) ∘ refl) ⊸ refl ∘ refl 〉 
    i ∘ (id ⊸ (i ∘ j ⊸ id ∘ L) ∘ j) ⊸ id ∘ (L ∘ L)
  ≐〈 refl ∘ (refl ⊸ ijL ∘ refl) ⊸ refl ∘ refl 〉
    i ∘ (id ⊸ id ∘ j) ⊸ id ∘ (L ∘ L)
  ≐〈 refl ∘ (f⊸id ∘ refl ∙ lid) ⊸ refl ∘ refl 〉
    i ∘ j ⊸ id ∘ (L ∘ L)
  ≐〈 ~ ass 〉
    i ∘ j ⊸ id ∘ L ∘ L
  ≐〈 ijL ∘ refl 〉
    id ∘ L
  ≐〈 lid 〉
    L
  qed≐
