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
open import FreeSkewProunitalClosed
open import SeqCalc
open import Sound
open import Complete
open import MulticatLaws

-- ∀ f. sound (cmplt f) ≐ f


sem-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           S ⇒ [ Γ ∣ A ] → just A ⇒ [ Δ ∣ C ] → S ⇒ [ Γ ++ Δ ∣ C ]
sem-scut {Γ = Γ} f g = [ Γ ∣ g ]f ∘ f

sem-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
           nothing ⇒ [ Γ ∣ A ]  →  T ⇒ [ Δ ∣ C ] → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                      T ⇒ [ Δ₀ ++ Γ ++ Δ' ∣ C ]
sem-ccut {Γ = Γ} Δ₀ f g refl = [ Δ₀ ∣ i f ∘ L⋆ Γ ]f ∘ g 

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

[_∣_∣ass]f : ∀ Γ Δ {A}{B} {g : just A ⇒ B}
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

sound-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} →
             (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C) →
             sound (scut f g) ≐ sem-scut {S}{Γ}{Δ} (sound f) (sound g)
sound-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
               (f : nothing ∣ Γ ⊢ A)  → (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
                sound (ccut Δ₀ f g r) ≐ sem-ccut {T}{Γ} Δ₀ (sound f) (sound g) r              

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
sound-scut {Γ = Γ} (⊸r f) ax = (~ lid) ∙ ((~ [ Γ ∣id]f) ∘ refl)
sound-scut (⊸r f) (⊸r g) = sound-scut (⊸r f) g
sound-scut {Γ = Γ} (⊸r f) (⊸l {Γ₁} g g') =
  proof≐
    sound (scut (ccut Γ g f refl) g')
  ≐〈 sound-scut (ccut Γ g f refl) g' 〉 
    [ Γ ++ Γ₁ ∣ sound g' ]f ∘ sound (ccut Γ g f refl)
  ≐〈 refl ∘ sound-ccut Γ g f refl 〉 
    [ Γ ++ Γ₁ ∣ sound g' ]f ∘ ([ Γ ∣ i (sound g) ∘ L⋆ Γ₁ ]f ∘ sound f)
  ≐〈 ≡-to-≐ (sym [ Γ ∣ Γ₁ ∣ass]f) ∘ refl 〉 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ ([ Γ ∣ i (sound g) ∘ L⋆ Γ₁ ]f ∘ sound f)
  ≐〈 ~ ass 〉 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ]f ∘ [ Γ ∣ i (sound g) ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐〈 (~ [ Γ ∣∘]f) ∘ refl 〉 
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ (i (sound g) ∘ L⋆ Γ₁) ]f ∘ sound f
  ≐〈 [ Γ ∣≐]f (~ ass) ∘ refl 〉
    [ Γ ∣ [ Γ₁ ∣ sound g' ]f ∘ i (sound g) ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐〈 [ Γ ∣≐]f (ni2 ∘ refl) ∘ refl 〉
    [ Γ ∣ i (sound g) ∘ id ⊸ [ Γ₁ ∣ sound g' ]f ∘ L⋆ Γ₁ ]f ∘ sound f
  ≐〈 [ Γ ∣≐]f ass ∘ refl 〉 
    [ Γ ∣ i (sound g) ∘ (id ⊸ [ Γ₁ ∣ sound g' ]f ∘ L⋆ Γ₁) ]f ∘ sound f
  ≐〈 [ Γ ∣≐]f (refl ∘ (~ (nL⋆2 Γ₁ (sound g')))) ∘ refl 〉 
    [ Γ ∣ i (sound g) ∘ (L⋆ Γ₁ ∘ id ⊸ sound g') ]f ∘ sound f
  ≐〈 [ Γ ∣≐]f (~ ass) ∘ refl 〉
    [ Γ ∣ i (sound g) ∘ L⋆ Γ₁ ∘ id ⊸ sound g' ]f ∘ sound f
  qed≐
sound-scut (⊸l {Γ} {Δ} f f') g =
  proof≐
    i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound (scut f' g)
  ≐〈 refl ∘ refl ⊸ sound-scut f' g 〉 
    i (sound f) ∘ L⋆ Γ ∘ id ⊸ ([ Δ ∣ sound g ]f ∘ sound f')
  ≐〈 refl ∘ id⊸∘ 〉 
    i (sound f) ∘ L⋆ Γ ∘ (id ⊸ [ Δ ∣ sound g ]f ∘ id ⊸ sound f')
  ≐〈 (~ ass) ∙ (ass ∘ refl) 〉 
    i (sound f) ∘ (L⋆ Γ ∘ id ⊸ [ Δ ∣ sound g ]f) ∘ id ⊸ sound f'
  ≐〈 refl ∘ nL⋆2 Γ [ Δ ∣ sound g ]f ∘ refl 〉 
    i (sound f) ∘ (id ⊸ [ Γ ∣ [ Δ ∣ sound g ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
  ≐〈 refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Δ ∣ass]f  ∘ refl) ∘ refl 〉 
    i (sound f) ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
  ≐〈 ~ ass ∘ refl 〉
    i (sound f) ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐〈 ~ ni2 ∘ refl ∘ refl 〉
    [ Γ ++ Δ ∣ sound g ]f ∘ i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐〈 ass ∘ refl ∙ ass 〉
    [ Γ ++ Δ ∣ sound g ]f ∘ (i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound f')
  qed≐
  
sound-ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
sound-ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
sound-ccut {Γ = Γ} .[] f (uf g) refl | inj₁ (refl , refl , refl) =
  proof≐
    sound (scut f g)
  ≐〈 sound-scut f g 〉
    [ Γ ∣ sound g ]f ∘ sound f
  ≐〈 refl ∘ ~ ij 〉
    [ Γ ∣ sound g ]f ∘ (i (sound f) ∘ j)
  ≐〈 ~ ass 〉 
    [ Γ ∣ sound g ]f ∘ i (sound f) ∘ j
  ≐〈 ni2 ∘ refl 〉 
    i (sound f) ∘ id ⊸ [ Γ ∣ sound g ]f ∘ j
  ≐〈 refl ∘ ~ (L⋆-j Γ) 〉 
    i (sound f) ∘ id ⊸ [ Γ ∣ sound g ]f ∘ (L⋆ Γ ∘ j)
  ≐〈 ~ ass ∙ (ass ∘ refl) 〉 
    i (sound f) ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ L⋆ Γ) ∘ j
  ≐〈 refl ∘ (~ (nL⋆2 Γ (sound g)))  ∘ refl 〉 
    i (sound f) ∘ (L⋆ Γ ∘ id ⊸ sound g) ∘ j
  ≐〈 ~ ass ∘ refl ∙ ass 〉
    i (sound f) ∘ L⋆ Γ ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut {Γ = Γ} .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    id ⊸ sound (ccut Γ₀ f g refl) ∘ j
  ≐〈 refl ⊸ sound-ccut Γ₀ f g refl ∘ refl 〉 
    id ⊸ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ sound g) ∘ j
  ≐〈 (id⊸∘ ∘ refl) ∙ ass 〉 
    id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut Δ₀ f (⊸r g) refl = sound-ccut Δ₀ f g refl
sound-ccut Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
sound-ccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A} {C} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  proof≐
    i (sound (ccut Δ₀ f g refl)) ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 i (sound-ccut Δ₀ f g refl) ∘ refl ∘ refl 〉 
    i ([ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ sound g) ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ~ ni1 ∘ refl ∘ refl 〉 
    i (sound g) ∘ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ass ∘ refl 〉
    i (sound g) ∘ ([ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ L⋆ass Δ₀ (Γ ++ Γ₀)) ∘ refl 〉  
    i (sound g) ∘ ([ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Δ₀ ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (~ ass ∙ (~ (nL⋆ Δ₀ (i (sound f) ∘ L⋆ Γ)) ∘ refl)) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id ∘ L⋆ (Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ (refl ⊸ rid ∙ f⊸∘) ∘ refl ∙ ass) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ (Γ ++ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ lemma) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (id ⊸ i (sound f) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (~ ass ∙ (~ ass ∙ (refl ∘ (~ f⊸∘ ∙ lid ⊸ refl) ∘ refl) ∘ refl)) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ id ⊸ (i (sound f) ∘ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (nL⋆2 Δ₀ (i (sound f) ∘ L⋆ Γ) ∘ refl ∘ refl) ∘ refl 〉
    i (sound g) ∘ ((id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f) ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (ass ∙ ass) ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (L⋆ Δ₀ ∘ (L ∘ L⋆ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ ~ (L⋆ass Δ₀ (A ∷ Γ₀))) ∘ refl 〉 
    i (sound g) ∘ (id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 ~ ass ∘ refl 〉 
    i (sound g) ∘ id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ~ ni2 ∘ refl ∘ refl 〉
    [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ i (sound g) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ass ∘ refl ∙ ass 〉
    [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (i (sound g) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g')
  qed≐
  where
    lemma : L⋆ Γ ⊸ id ∘ (i (sound f)) ⊸ id ∘ L⋆ (Γ ++ Γ₀) ≐ id ⊸ (i (sound f)) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
    lemma =
        proof≐
          L⋆ Γ ⊸ id ∘ (i (sound f)) ⊸ id ∘ L⋆ (Γ ++ Γ₀)
       ≐〈 refl ∘ ~ iL ∘ refl 〉
          L⋆ Γ ⊸ id ∘ (id ⊸ i (sound f) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
        ≐〈 ~ ass ∘ refl 〉 
          L⋆ Γ ⊸ id ∘ id ⊸ i (sound f) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐〈 ((swap⊸ ∘ refl) ∙ ass ∘ refl) ∙ ass 〉 
          id ⊸ i (sound f) ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Γ₀))
        ≐〈 refl ∘ L⋆LL⋆ Γ Δ Γ₀  〉 
          id ⊸ i (sound f) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)
        ≐〈 ~ ass ∙ (~ ass ∘ refl)  〉 
          id ⊸ i (sound f) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
        qed≐
sound-ccut {Γ = Γ'} .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound (ccut Γ₀ f g' refl)
  ≐〈 refl ∘ refl ⊸ sound-ccut Γ₀ f g' refl 〉
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ sound g')
  ≐〈 refl ∘ id⊸∘ 〉
    i (sound g) ∘ L⋆ Γ ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ id ⊸ sound g')
  ≐〈 (~ ass) ∙ (ass ∘ refl) 〉
    i (sound g) ∘ (L⋆ Γ ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f) ∘ id ⊸ sound g'
  ≐〈 refl ∘ nL⋆2 Γ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Γ ∣ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ⊸ ≡-to-≐ [ Γ ∣ Γ₀ ∣ass]f ∘ refl) ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
  ≐〈 ~ ass ∘ refl 〉
    i (sound g) ∘ id ⊸ [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 ~ ni2 ∘ refl ∘ refl  〉
    [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 (ass ∘ refl) ∙ ass 〉
    [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ (i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g')
  qed≐

soundcmplt : ∀{S C} → (f : S ⇒ C) → sound (cmplt f) ≐ f
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
    i (id ⊸ sound (cmplt f) ∘ j) ∘ (L ∘ id) ∘ id ⊸ sound (cmplt g)
  ≐〈 i (refl ⊸ soundcmplt f ∘ refl) ∘ ~ rid ∘ refl ⊸ soundcmplt g 〉
    i (id ⊸ f ∘ j) ∘ L ∘ id ⊸ g
  ≐〈 i (~ nj) ∘ refl ∘ refl 〉
    i (f ⊸ id ∘ j) ∘ L ∘ id ⊸ g
  ≐〈 ~ ni1 ∘ refl ∘ refl 〉
    i j ∘ ((f ⊸ id) ⊸ id) ∘ L ∘ id ⊸ g
  ≐〈 ass ∘ refl 〉
    i j ∘ ((f ⊸ id) ⊸ id ∘ L) ∘ id ⊸ g
  ≐〈 refl ∘ (refl ⊸ (~ f⊸id) ∘ refl ∙ nL ∙ (refl ∘ f⊸id) ∙ ~ rid) ∘ refl 〉
    i j ∘ (id ⊸ (f ⊸ id) ∘ L) ∘ id ⊸ g
  ≐〈 ~ ass ∘ refl 〉
    i j ∘ (id ⊸ (f ⊸ id)) ∘ L ∘ id ⊸ g
  ≐〈 ~ ni2 ∘ refl ∘ refl 〉
    f ⊸ id ∘ i j ∘ L ∘ id ⊸ g
  ≐〈 ass ∘ refl 〉
    f ⊸ id ∘ (i j ∘ L) ∘ id ⊸ g
  ≐〈 refl ∘ ijL ∘ refl 〉
    f ⊸ id ∘ id ∘ id ⊸ g
  ≐〈 ~ (rid ∘ refl) 〉
    f ⊸ id ∘ id ⊸ g
  ≐〈 ~ f⊸∘ 〉
    (id ∘ f) ⊸ (id ∘ g)
   ≐〈 lid ⊸ lid 〉
    f ⊸ g
  qed≐
soundcmplt (i e) = 
  proof≐
    i (sound (cmplt e)) ∘ id ∘ id ⊸ id
  ≐〈 refl ∘ f⊸id ∙ ~ rid ∙ ~ rid 〉 
    i (sound (cmplt e))
  ≐〈 i (soundcmplt e) 〉 
    i e
  qed≐
soundcmplt j = (f⊸id ∘ refl) ∙ lid
soundcmplt L =
  proof≐
    i (id ⊸ (i (id ⊸ id ∘ j) ∘ (L ∘ id) ∘ id ⊸ id) ∘ j) ∘ (L ∘ (L ∘ id)) ∘ id ⊸ id
  ≐〈 i (refl ⊸ (i (f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘ f⊸id ∙ ~ rid) ∘ refl) ∘ (~ ass ∙ ~ rid) ∘ f⊸id ∙ ~ rid 〉
    i (id ⊸ (i j ∘ L) ∘ j) ∘ (L ∘ L)
  ≐〈 i (refl ⊸ ijL ∘ refl) ∘ refl 〉
    i (id ⊸ id ∘ j) ∘ (L ∘ L)
  ≐〈 i (f⊸id ∘ refl ∙ lid) ∘ refl 〉
    i j ∘ (L ∘ L)
  ≐〈 ~ ass 〉
    i j ∘ L ∘ L
  ≐〈 ijL ∘ refl 〉
    id ∘ L
  ≐〈 lid 〉
    L
  qed≐
