{-# OPTIONS --rewriting #-}

open import SkMults

module SoundComplete where --(M : SkMult) where

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
open import MulticatLaws
open import Complete 
open import Sound

--open SkMult M

sem-scut : {S : Stp} → {Γ Δ : Cxt} → {A C : Fma} → 
           S ⇒ [ Γ ∣ A ] → just A ⇒ [ Δ ∣ C ] → S ⇒ [ Γ ++ Δ ∣ C ]
sem-scut {Γ = Γ} f g = [ Γ ∣ g ]f ∘ f

sem-ccut-n : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma} → 
           nothing ⇒ [ Γ ∣ A ]  →  T ⇒ [ Δ ∣ C ] → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                      T ⇒ [ Δ₀ ++ Γ ++ Δ' ∣ C ]
sem-ccut-n {Γ = Γ} Δ₀ f g refl = [ Δ₀ ∣ i f ∘ L⋆ Γ ]f ∘ g 

sem-ccut-j : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A A' C : Fma} → 
           just A' ⇒ [ Γ ∣ A ]  →  T ⇒ [ Δ ∣ C ] → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                      T ⇒ [ Δ₀ ++ A' ∷ Γ ++ Δ' ∣ C ]
sem-ccut-j {Γ = Γ} Δ₀ f g refl = [ Δ₀ ∣ f ⊸ id ∘ L⋆ Γ ]f ∘ g


sound-ccut-b2-n : ∀ {T Γ Δ₀ Δ₁ X Y}
  → (f : nothing ∣ Γ ⊢ ` X) (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
  → sound (ccut-b2 Δ₀ f g) ≐ [ lmap ` Δ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ base {Δ = lmap ` (Δ₀ ++ X ∷ Δ₁)} g refl refl
sound-ccut-b2-j : ∀ {T Γ Δ₀ Δ₁ A X Y}
  → (f : just A ∣ Γ ⊢ ` X) (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
  → sound (ccut-b2 Δ₀ f g) ≐ [ lmap ` Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ base {Δ = lmap ` (Δ₀ ++ X ∷ Δ₁)} g refl refl

-- sound-ccut-b2-n (base {nothing} f refl refl) g = {!add in ≐!}
-- sound-ccut-b2-n {Δ₀ = Δ₀} (uf f) g =
--   sound-ccut-b2-j f g
--   ∙ ([ lmap ` Δ₀ ∣≐]f
--        (~ (refl ∘ (refl ⊸ f⊸id ∙ f⊸id ∘ refl ∘ refl) ∙ (refl ∘ (lid ∘ refl) ∙ (~ ass ∙ (ijL ∘ refl ∙ lid)))) ∘ refl
--        ∙ (refl ∘ ~ (refl ⊸ (~ f⊸id) ∘ refl ∙ nL) ∘ refl)
--        ∙ (~ ass ∘ refl ∙ ass)
--        ∙ (ni1 ∘ refl))
--     ∘ refl)
-- sound-ccut-b2-n {Δ₀ = Δ₁}{Δ₁ = Δ₃} (⊸c Δ₀ {Γ} {Δ₂} {A} {B} f f₁) g =
--   proof≐
--     [ lmap ` Δ₁ ∣ [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ sound (ccut-b2 Δ₁ f₁ g)
--   ≐〈 refl ∘ sound-ccut-b2-n f₁ g 〉 
--     [ lmap ` Δ₁ ∣ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ]f ∘ ([ lmap ` Δ₁ ∣ i (sound f₁) ∘ L⋆ (Δ₀ ++ B ∷ Δ₂) ]f ∘ _)
--   ≐〈 ~ ass 〉 
--     [ lmap ` Δ₁ ∣ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ]f ∘ [ lmap ` Δ₁ ∣ i (sound f₁) ∘ L⋆ (Δ₀ ++ B ∷ Δ₂) ]f ∘ _
--   ≐〈 ~ [ lmap ` Δ₁ ∣∘]f ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ (i (sound f₁) ∘ L⋆ (Δ₀ ++ B ∷ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ ass) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ i (sound f₁) ∘ L⋆ (Δ₀ ++ B ∷ Δ₂) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (ni2 ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ B ∷ Δ₂) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f ass ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ B ∷ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ L⋆ass Δ₀ (_ ∷ Δ₂) ∙ (~ ass ∙ ~ ass))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Δ₂) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (~ nL⋆2 Δ₀ _ ∘ refl ∘ refl)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ id ⊸ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Δ₂) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (ass ∘ refl ∙ ass)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (id⊸∘ ∙ (id⊸∘ ∘ refl) ∘ refl ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (ass ∘ refl ∙ ass))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ~ L⋆LL⋆ Γ (lmap ` Δ₃) Δ₂))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ ((L⋆ Γ ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₂)))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (~ ass ∙ (~ ass ∙ (~ id⊸∘ ∙ refl ⊸ (~ ∘⊸id) ∘ refl ∙ ~ swap⊸ ∘ refl) ∘ refl)))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ id ⊸ ((i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (rid ∙ (ass ∘ refl ∙ (refl ∘ ~ f⊸id) ∙ ass) ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (id ⊸ ((i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L ∘ id ⊸ id) ∘ L⋆ (Γ ++ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ~ nL ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (((i (sound f) ∘ L⋆ Γ) ⊸ id) ⊸ (id ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (~ ass ∙ ((refl ∘ refl ⊸ f⊸id) ∘ refl) ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ∘⊸id ⊸ refl ∙ ~ ∘⊸id ∘ refl ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ ((L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₂))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (~ ass ∙ (~ ass ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (nL⋆ Δ₀ _ ∘ refl ∘ refl)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ Δ₀ ∘ L ∘ L⋆ (Γ ++ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (ass ∙ (ass ∙ (refl ∘ ~ (L⋆ass Δ₀ (_ ∷ Γ ++ Δ₂)))))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₂)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ ass) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i (sound f₁) ∘ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₂) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (ni1 ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ i ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound f₁) ∘  L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₂) ]f ∘ _
--   qed≐
-- 
-- sound-ccut-b2-j (base {just X} f refl refl) g = {!add in ≐!}
-- sound-ccut-b2-j {Δ₀ = Δ₀} (⊸l {Γ} {Δ} f f₁) g =
--   proof≐
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound (ccut-b2 Δ₀ f₁ g)
--   ≐〈 refl ∘ sound-ccut-b2-j f₁ g 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ ([ lmap ` Δ₀ ∣ (sound f₁ ⊸ id) ∘ L⋆ Δ ]f ∘ _)
--   ≐〈 ~ ass 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ [ lmap ` Δ₀ ∣ (sound f₁ ⊸ id) ∘ L⋆ Δ ]f ∘ _
--   ≐〈 ~ [ lmap ` Δ₀ ∣∘]f ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ∘ (sound f₁ ⊸ id ∘ L⋆ Δ) ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (~ ass) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ∘ sound f₁ ⊸ id ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (ass ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ (L⋆ Γ ∘ sound f₁ ⊸ id) ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (refl ∘ nL⋆ Γ _ ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ ([ Γ ∣ sound f₁ ]f ⊸ id ∘ L⋆ Γ) ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (~ ass ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ [ Γ ∣ sound f₁ ]f ⊸ id ∘ L⋆ Γ ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (ass ∙ (refl ∘ ~ ∘⊸id) ∙ ~ ∘⊸id ∘ refl ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ ([ Γ ∣ sound f₁ ]f ∘ i (sound f) ∘ L⋆ Γ) ⊸ id ∘ L⋆ Γ ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f ((ni2 ∘ refl ∙ (ass ∙ (refl ∘ ~ nL⋆2 Γ _) ∙ ~ ass)) ⊸ refl ∘ refl ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ ((i (sound f) ∘ L⋆ Γ ∘ (id ⊸ sound f₁)) ⊸ id) ∘ L⋆ Γ ∘ L⋆ Δ ]f ∘ _
--   ≐〈 [ lmap ` Δ₀ ∣≐]f (ass ∙ (refl ∘ ~ (L⋆ass Γ Δ))) ∘ refl 〉 
--     [ lmap ` Δ₀ ∣ ((i (sound f) ∘ L⋆ Γ ∘ (id ⊸ sound f₁)) ⊸ id) ∘ L⋆ (Γ ++ Δ) ]f ∘ _
--   qed≐
-- sound-ccut-b2-j {Δ₀ = Δ₁} {Δ₂} (⊸c Δ₀ {Γ} {Δ₃} {A} {B} f f₁) g = 
--   proof≐
--     [ lmap ` Δ₁ ∣ id ⊸ [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ sound (ccut-b2 Δ₁ f₁ g)
--   ≐〈 refl ∘ sound-ccut-b2-j f₁ g 〉 
--     [ lmap ` Δ₁ ∣ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ]f ∘ ([ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ L⋆ (Δ₀ ++ B ∷ Δ₃) ]f ∘ _)
--   ≐〈 ~ ass 〉 
--     [ lmap ` Δ₁ ∣ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ]f ∘ [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ L⋆ (Δ₀ ++ B ∷ Δ₃) ]f ∘ _
--   ≐〈 ~ [ lmap ` Δ₁ ∣∘]f ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ (sound f₁ ⊸ id ∘ L⋆ (Δ₀ ++ B ∷ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ ass) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound f₁ ⊸ id ∘ L⋆ (Δ₀ ++ B ∷ Δ₃) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ swap⊸ ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ B ∷ Δ₃) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f ass ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ B ∷ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ L⋆ass Δ₀ (_ ∷ Δ₃) ∙ (~ ass ∙ ~ ass))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (id ⊸ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Δ₃) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (~ nL⋆2 Δ₀ _ ∘ refl ∘ refl)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ id ⊸ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Δ₃) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (ass ∘ refl ∙ ass)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (id⊸∘ ∙ (id⊸∘ ∘ refl) ∘ refl ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (ass ∘ refl ∙ ass))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ~ L⋆LL⋆ Γ (lmap ` Δ₂) Δ₃))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (id ⊸ (L⋆ Γ ⊸ id) ∘ id ⊸ (i (sound f) ⊸ id) ∘ ((L⋆ Γ ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₃)))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (~ ass ∙ (~ ass ∙ (~ id⊸∘ ∙ refl ⊸ (~ ∘⊸id) ∘ refl ∙ ~ swap⊸ ∘ refl) ∘ refl)))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ id ⊸ ((i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (rid ∙ (ass ∘ refl ∙ (refl ∘ ~ f⊸id) ∙ ass) ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (id ⊸ ((i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L ∘ id ⊸ id) ∘ L⋆ (Γ ++ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ~ nL ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (((i (sound f) ∘ L⋆ Γ) ⊸ id) ⊸ (id ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (~ ass ∙ ((refl ∘ refl ⊸ f⊸id) ∘ refl) ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (refl ∘ (refl ∘ ∘⊸id ⊸ refl ∙ ~ ∘⊸id ∘ refl ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ ((L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₃))) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (~ ass ∙ (~ ass ∘ refl))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (nL⋆ Δ₀ _ ∘ refl ∘ refl)) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ Δ₀ ∘ L ∘ L⋆ (Γ ++ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (refl ∘ (ass ∙ (ass ∙ (refl ∘ ~ (L⋆ass Δ₀ (_ ∷ Γ ++ Δ₃)))))) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₃)) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ ass) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ sound f₁ ⊸ id ∘ [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘  L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₃) ]f ∘ _
--   ≐〈 [ lmap ` Δ₁ ∣≐]f (~ ∘⊸id ∘ refl) ∘ refl 〉 
--     [ lmap ` Δ₁ ∣ ([ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound f₁) ⊸ id ∘ L⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₃) ]f ∘ _
--   qed≐

sound-scut : ∀ {S Γ Δ A C}
  → (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C)
  → sound (scut f g) ≐ sem-scut {S}{Γ}{Δ} (sound f) (sound g)
sound-ccut-n : ∀ {T Γ Δ} Δ₀ {Δ' A C}
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ C) (p : Δ ≡ Δ₀ ++ A ∷ Δ')
  → sound (ccut Δ₀ f g p) ≐ sem-ccut-n {T}{Γ} Δ₀ (sound f) (sound g) p
sound-ccut-j : ∀ {T Γ Δ} Δ₀ {Δ' A A' C}
  → (f : just A' ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ C) (p : Δ ≡ Δ₀ ++ A ∷ Δ')
  → sound (ccut Δ₀ f g p) ≐ sem-ccut-j {T}{Γ} Δ₀ (sound f) (sound g) p

sound-scut (base f refl refl) (base {just X} g refl refl) = {!add in ≐!}
sound-scut (base f refl refl) (⊸r g) = sound-scut (base f refl refl) g
sound-scut (base {Γ = Γ} f refl refl) (⊸c Δ₀ {Γ₁} g g₁) =
  proof≐
    [ lmap ` Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ sound (scut (base f refl refl) g₁)
  ≐〈 refl ∘ sound-scut (base f refl refl) g₁ 〉
    [ lmap ` Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ ([ lmap ` Γ ∣ sound g₁ ]f ∘ base f refl refl)
  ≐〈 ~ ass 〉 
    [ lmap ` Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ [ lmap ` Γ ∣ sound g₁ ]f ∘ base f refl refl
  ≐〈 ~ [ lmap ` Γ ∣∘]f ∘ refl 〉 
    [ lmap ` Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ∘ sound g₁ ]f ∘ base f refl refl
  qed≐
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
sound-scut (⊸r f) (base {nothing} x () x₂)
sound-scut (⊸r f) (base {just x₁} x () x₂)
sound-scut (⊸r f) (⊸r g) = sound-scut (⊸r f) g
sound-scut {Γ = Γ} (⊸r f) (⊸l {Γ₁} g g') =
  proof≐
    sound (scut (ccut Γ g f refl) g')
  ≐〈 sound-scut (ccut Γ g f refl) g' 〉 
    [ Γ ++ Γ₁ ∣ sound g' ]f ∘ sound (ccut Γ g f refl)
  ≐〈 refl ∘ sound-ccut-n Γ g f refl 〉 
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
sound-scut {Γ = Γ} (⊸r f) (⊸c Δ₀ {Γ₁} g g₁) =
  proof≐
    [ Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ sound (scut (⊸r f) g₁)
  ≐〈 refl ∘ sound-scut (⊸r f) g₁ 〉 
    [ Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ ([ Γ ∣ sound g₁ ]f ∘ sound f)
  ≐〈 ~ ass 〉 
    [ Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ]f ∘ [ Γ ∣ sound g₁ ]f ∘ sound f
  ≐〈 ~ [ Γ ∣∘]f ∘ refl 〉 
    [ Γ ∣ [ Δ₀ ∣ (L⋆ Γ₁ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ₁ ]f ∘ sound g₁ ]f ∘ sound f
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
    i (sound f) ∘ (id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ) ∘ id ⊸ sound f'
  ≐〈 ~ ass ∘ refl 〉
    i (sound f) ∘ id ⊸ [ Γ ++ Δ ∣ sound g ]f ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐〈 ~ ni2 ∘ refl ∘ refl 〉
    [ Γ ++ Δ ∣ sound g ]f ∘ i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound f'
  ≐〈 ass ∘ refl ∙ ass 〉
    [ Γ ++ Δ ∣ sound g ]f ∘ (i (sound f) ∘ L⋆ Γ ∘ id ⊸ sound f')
  qed≐
sound-scut (⊸c Δ₀ {Γ}{Δ₁} f f₁) g =
  proof≐
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound (scut f₁ g)
  ≐〈 refl ∘ sound-scut f₁ g 〉 
    [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ ([ Δ₀ ∣ id ⊸ [ Δ₁ ∣ sound g ]f ]f ∘ sound f₁)
  ≐〈 ~ ass 〉 
    ([ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ [ Δ₀ ∣ id ⊸ [ Δ₁ ∣ sound g ]f ]f) ∘ sound f₁
  ≐〈 ~ [ Δ₀ ∣∘]f ∘ refl 〉 
    [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ∘ id ⊸ [ Δ₁ ∣ sound g ]f ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (ass ∙ (refl ∘ nL⋆2 Γ _) ∙ ~ ass) ∘ refl 〉 
    [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ∘ L⋆ Γ ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (ass ∘ refl) ∘ refl 〉 
    [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ (i (sound f) ⊸ id ∘ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f) ∘ L⋆ Γ ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (refl ∘ swap⊸ ∘ refl) ∘ refl 〉 
    [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ (id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ∘ i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (~ ass ∘ refl) ∘ refl 〉 
    [ Δ₀ ∣ L⋆ Γ ⊸ id ∘ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (swap⊸ ∘ refl ∘ refl) ∘ refl 〉 
    [ Δ₀ ∣ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ∘ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣≐]f (ass ∘ refl ∙ ass) ∘ refl 〉 
    [ Δ₀ ∣ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ∘ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ Γ) ]f ∘ sound f₁
  ≐〈 [ Δ₀ ∣∘]f ∘ refl 〉 
    ([ Δ₀ ∣ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ]f ∘ [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f) ∘ sound f₁
  ≐〈 ass 〉 
    [ Δ₀ ∣ id ⊸ [ Γ ∣ [ Δ₁ ∣ sound g ]f ]f ]f ∘ ([ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f ∘ sound f₁)
  qed≐

sound-ccut-n Δ₀ {Δ'} {A} f (base {Γ = Γ} g refl eq) refl with  cases++-lmap ` Δ₀ (A ∷ Δ') Γ eq
sound-ccut-n .(lmap ` Λ₀) {.(lmap ` Λ₁)} {.(` X)} f (base {Γ = .(Λ₀ ++ X ∷ Λ₁)} g refl refl) refl | Λ₀ , X ∷ Λ₁ , refl , refl , refl
  = sound-ccut-b2-n f g
sound-ccut-n Δ₀ f (uf g) r with cases∷ Δ₀ r
sound-ccut-n {Γ = Γ} .[] f (uf g) refl | inj₁ (refl , refl , refl) =
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
sound-ccut-n {Γ = Γ} .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    id ⊸ sound (ccut Γ₀ f g refl) ∘ j
  ≐〈 refl ⊸ sound-ccut-n Γ₀ f g refl ∘ refl 〉 
    id ⊸ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ sound g) ∘ j
  ≐〈 (id⊸∘ ∘ refl) ∙ ass 〉 
    id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut-n Δ₀ f (⊸r g) refl = sound-ccut-n Δ₀ f g refl
sound-ccut-n Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
sound-ccut-n {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
  proof≐
    i (sound (ccut Δ₀ f g refl)) ∘ L⋆ (Δ₀ ++ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 i (sound-ccut-n Δ₀ f g refl) ∘ refl ∘ refl 〉 
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
sound-ccut-n {Γ = Γ'} .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound (ccut Γ₀ f g' refl)
  ≐〈 refl ∘ refl ⊸ sound-ccut-n Γ₀ f g' refl 〉
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ sound g')
  ≐〈 refl ∘ id⊸∘ 〉
    i (sound g) ∘ L⋆ Γ ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ id ⊸ sound g')
  ≐〈 (~ ass) ∙ (ass ∘ refl) 〉
    i (sound g) ∘ (L⋆ Γ ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f) ∘ id ⊸ sound g'
  ≐〈 refl ∘ nL⋆2 Γ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Γ ∣ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'

  ≐〈 ~ ass ∘ refl 〉
    i (sound g) ∘ id ⊸ [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 ~ ni2 ∘ refl ∘ refl  〉
    [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 (ass ∘ refl) ∙ ass 〉
    [ Γ ++ Γ₀ ∣ i (sound f) ∘ L⋆ Γ' ]f ∘ (i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g')
  qed≐
sound-ccut-n Δ₀ {Δ'} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) p with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (_ ∷ Δ') (sym p)
sound-ccut-n .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) p | inj₁ (Γ₀ , refl , r) with cases++ Γ₀ Γ Δ' Δ₂ r
sound-ccut-n {Γ = Γ} .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {.(Δ₀ ++ Δ₂)} {A} f (⊸c Δ₁ {.(Γ₀ ++ A ∷ Δ₀)} {Δ₂} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Δ₀ , refl , refl) =
  proof≐
    [ Δ₁ ∣ L⋆ (Γ₀ ++ Γ ++ Δ₀) ⊸ id ∘ i (sound (ccut Γ₀ f g refl)) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀) ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f lem ∘ refl 〉 
    [ Δ₁ ∣ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)) ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣∘]f ∘ refl 〉 
    [ Δ₁ ∣ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ]f ∘  [ Δ₁ ∣ L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀) ]f ∘ sound g₁
  ≐〈 ass 〉 
    [ Δ₁ ∣ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ]f ∘  ([ Δ₁ ∣ L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀) ]f ∘ sound g₁)
  qed≐
  where
    lem' : _
    lem' =
      proof≐
        i (sound g) ∘ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 refl ∘ L⋆ass Γ₀ (Γ ++ Δ₀) 〉
        i (sound g) ∘ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Γ₀ ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 ~ ass ∙ (ass ∘ refl) 〉
        i (sound g) ∘ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ Γ₀) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 refl ∘ ~ nL⋆ Γ₀ _ ∘ refl 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 ass 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ (refl ∘ ∘⊸id ∙ ~ ass ∘ refl) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ (refl ∘ ~ iL ∘ refl) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ L⋆ Γ ⊸ id ∘ (id ⊸ i (sound f) ∘ L) ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ ((~ ass ∙ (ass ∘ refl)) ∘ refl) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ (L⋆ Γ ⊸ id ∘ id ⊸ i (sound f)) ∘ L ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ (refl ∘ swap⊸ ∘ refl ∘ refl) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ (id ⊸ i (sound f) ∘ L⋆ Γ ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ (~ ass ∘ refl ∙ ass ∘ refl ∙ ass) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ id ⊸ i (sound f) ∘ ((L⋆ Γ ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₀)))
      ≐〈 refl ∘ (refl ∘ L⋆LL⋆ _ [] _) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ id ⊸ i (sound f) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₀))
      ≐〈 refl ∘ (~ ass ∙ (~ ass ∙ (ass ∙ (refl ∘ ~ id⊸∘) ∘ refl) ∘ refl)) 〉
        i (sound g) ∘ (L⋆ Γ₀ ∘ id ⊸ (i (sound f) ∘ L⋆ Γ) ∘ L ∘ L⋆ Δ₀ {_}{_})
      ≐〈 refl ∘ (nL⋆2 Γ₀ _ ∘ refl ∘ refl) 〉
        i (sound g) ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ Γ₀ ∘ L ∘ L⋆ Δ₀)
      ≐〈 refl ∘ (ass ∙ (ass ∙ (refl ∘ ~ (L⋆ass Γ₀ (_ ∷ Δ₀))))) 〉
        i (sound g) ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Γ₀ ++ A ∷ Δ₀))
      ≐〈 ~ ass 〉
        i (sound g) ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 ~ ni2 ∘ refl 〉
        [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ i (sound g) ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      qed≐

    lem : _
    lem =
      proof≐
        L⋆ (Γ₀ ++ Γ ++ Δ₀) ⊸ id ∘ i (sound (ccut Γ₀ f g refl)) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 refl ∘ i (sound-ccut-n Γ₀ f g refl) ⊸ refl ∘ refl 〉
        L⋆ (Γ₀ ++ Γ ++ Δ₀) ⊸ id ∘ i ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ sound g) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 refl ∘ (~ ni1) ⊸ refl ∘ refl 〉
        L⋆ (Γ₀ ++ Γ ++ Δ₀) ⊸ id ∘ (i (sound g) ∘ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 ~ ∘⊸id ∘ refl 〉
        (i (sound g) ∘ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 lem' ⊸ refl ∘ refl 〉
        ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ i (sound g) ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)) ⊸ id ∘ L⋆ (Γ₀ ++ Γ ++ Δ₀)
      ≐〈 ∘⊸id ∙ (refl ∘ ∘⊸id ∙ ~ ass) ∘ L⋆ass Γ₀ (Γ ++ Δ₀) 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Γ₀ ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 ~ ass ∙ (ass ∘ refl) 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ ([ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ Γ₀) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 refl ∘ ~ nL⋆ Γ₀ _ ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ (L⋆ Γ₀ ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 ~ ass ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ (i (sound f) ∘ L⋆ Γ) ⊸ id ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 refl ∘ ∘⊸id ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ (L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 ~ ass ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ L⋆ Γ ⊸ id ∘ i (sound f) ⊸ id ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 refl ∘ ~ iL ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ L⋆ Γ ⊸ id ∘ (id ⊸ i (sound f) ∘ L) ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 ~ ass ∙ (ass ∘ refl) ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ (L⋆ Γ ⊸ id ∘ id ⊸ i (sound f)) ∘ L ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 refl ∘ swap⊸ ∘ refl ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ (id ⊸ i (sound f) ∘ L⋆ Γ ⊸ id) ∘ L ∘ L⋆ (Γ ++ Δ₀)
      ≐〈 (~ ass ∘ refl ∙ ass) ∘ refl ∙ ass 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ id ⊸ i (sound f) ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Δ₀))
      ≐〈 refl ∘ L⋆LL⋆ Γ Δ₂ Δ₀ 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ₀ ∘ id ⊸ i (sound f) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Δ₀)
      ≐〈 ~ ass ∙ (~ ass ∙ (ass ∙ (ass ∙ (refl ∘ (refl ∘ ~ id⊸∘))) ∘ refl) ∘ refl) 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ (L⋆ Γ₀ ∘ id ⊸ (i (sound f) ∘ L⋆ Γ)) ∘ L ∘ L⋆ Δ₀
      ≐〈 refl ∘ nL⋆2 Γ₀ _ ∘ refl ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ Γ₀) ∘ L ∘ L⋆ Δ₀
      ≐〈 ~ ass ∘ refl ∘ refl ∙ ass ∙ ass 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (L⋆ Γ₀ ∘ (L ∘ L⋆ Δ₀))
      ≐〈 refl ∘ ~ (L⋆ass Γ₀ (_ ∷ Δ₀)) 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 ass ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ (i (sound g) ⊸ id ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f) ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 refl ∘ swap⊸ ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ (id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ i (sound g) ⊸ id) ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 ~ ass ∘ refl 〉
        L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 swap⊸ ∘ refl ∘ refl 〉
        id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀)
      ≐〈 ass ∘ refl ∙ ass 〉
        id ⊸ [ Γ₀ ∣ i (sound f) ∘ L⋆ Γ ]f ∘ (L⋆ (Γ₀ ++ A ∷ Δ₀) ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ (Γ₀ ++ A ∷ Δ₀))
      qed≐      
sound-ccut-n {Γ = Γ₁} .(Δ₁ ++ _ ⊸ B ∷ Γ ++ Δ₀) {Δ'} f (⊸c Δ₁ {Γ} {.(Δ₀ ++ _ ∷ Δ')} {B = B} g g₁) refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl) =
  proof≐
    [ Δ₁ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘  sound (ccut (Δ₁ ++ B ∷ Δ₀) f g₁ refl)
  ≐〈 refl ∘ sound-ccut-n (Δ₁ ++ B ∷ Δ₀) f g₁ refl 〉 
    [ Δ₁ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘  ([ Δ₁ ∣ id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ sound g₁)
  ≐〈 ~ ass 〉 
    [ Δ₁ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘  [ Δ₁ ∣ id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ sound g₁
  ≐〈 ~ [ Δ₁ ∣∘]f ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ ∘ id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f ass ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ i (sound g) ⊸ id ∘ (L⋆ Γ ∘ id ⊸ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f) ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (refl ∘ nL⋆2 Γ _) ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ i (sound g) ⊸ id ∘ ((id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f) ∘ L⋆ Γ) ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (~ ass ∙ (ass ∘ refl)) ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ (i (sound g) ⊸ id ∘ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f) ∘ L⋆ Γ ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (refl ∘ swap⊸ ∘ refl) ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ (id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (~ ass ∘ refl) ∘ refl 〉 
    [ Δ₁ ∣ L⋆ Γ ⊸ id ∘ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ i (sound g) ⊸ id ∘ L⋆ Γ ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (swap⊸ ∘ refl ∘ refl) ∘ refl 〉 
    [ Δ₁ ∣ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ L⋆ Γ ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣≐]f (ass ∘ refl ∙ ass) ∘ refl 〉 
    [ Δ₁ ∣ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ∘ (L⋆ Γ ⊸ id ∘ i (sound g) ⊸ id ∘ L⋆ Γ) ]f ∘ sound g₁
  ≐〈 [ Δ₁ ∣∘]f ∘ refl 〉 
    [ Δ₁ ∣ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ]f ∘ [ Δ₁ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g₁
  ≐〈 ass 〉 
    [ Δ₁ ∣ id ⊸ [ Γ ∣ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ]f ]f ∘ ([ Δ₁ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ∘ sound g₁)
  qed≐
sound-ccut-n .Δ₁ {.(Γ ++ Δ₂)} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) refl | inj₂ ([] , refl , refl) = {!!}
sound-ccut-n {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₂)} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  proof≐
    [ Δ₀ ∣  [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ]f ∘ _
  ≐〈 refl ∘ sound-ccut-n Δ₀ f g₁ refl 〉 
    [ Δ₀ ∣  [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ]f ∘ ([ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ∘ sound g₁)
  ≐〈 ~ ass 〉 
    [ Δ₀ ∣  [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ]f ∘ [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ∘ sound g₁
  ≐〈 ~ [ Δ₀ ∣∘]f ∘ refl 〉 
    [ Δ₀ ∣  [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ (i (sound f) ∘ L⋆ Γ₁) ]f ∘ sound g₁
  ≐〈  [ Δ₀ ∣≐]f (~ ass ∙ (ni2 ∘ refl)) ∘ refl 〉 
    [ Δ₀ ∣ i (sound f) ∘ id ⊸ [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ L⋆ Γ₁ ]f ∘ sound g₁
  ≐〈  [ Δ₀ ∣≐]f ass ∘ refl 〉 
    [ Δ₀ ∣ i (sound f) ∘ (id ⊸ [ Γ₁ ∣ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ L⋆ Γ₁) ]f ∘ sound g₁
  ≐〈  [ Δ₀ ∣≐]f (refl ∘ ~ nL⋆2 Γ₁ _) ∘ refl 〉 
    [ Δ₀ ∣ i (sound f) ∘ (L⋆ Γ₁ ∘ id ⊸ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f) ]f ∘ sound g₁
  ≐〈  [ Δ₀ ∣≐]f (~ ass) ∘ refl 〉 
    [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ∘ id ⊸ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ sound g₁
  ≐〈 [ Δ₀ ∣∘]f ∘ refl 〉 
    [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ∘ [ Δ₀ ∣ id ⊸ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ sound g₁
  ≐〈 ass 〉 
    [ Δ₀ ∣ i (sound f) ∘ L⋆ Γ₁ ]f ∘ ([ Δ₀ ∣ id ⊸ [ Γ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound g) ⊸ id) ∘ L⋆ Γ ]f ]f ∘ sound g₁)
  qed≐

sound-ccut-j Δ₀ {Δ'} {A} f (base {Γ = Γ} g refl eq) refl with  cases++-lmap ` Δ₀ (A ∷ Δ') Γ eq
sound-ccut-j .(lmap ` Λ₀) {.(lmap ` Λ₁)} {.(` X)} f (base {Γ = .(Λ₀ ++ X ∷ Λ₁)} g refl refl) refl | Λ₀ , X ∷ Λ₁ , refl , refl , refl
  = sound-ccut-b2-j f g
sound-ccut-j Δ₀ f (uf g) r with cases∷ Δ₀ r
sound-ccut-j {Γ = Γ} .[] f (uf g) refl | inj₁ (refl , refl , refl) =
  proof≐
    id ⊸ sound (scut f g) ∘ j
  ≐〈 refl ⊸ sound-scut f g ∘ refl 〉
    id ⊸ ([ Γ ∣ sound g ]f ∘ sound f) ∘ j 
  ≐〈 id⊸∘ ∘ refl ∙ ass 〉 
    id ⊸ [ Γ ∣ sound g ]f ∘ (id ⊸ sound f ∘ j)
  ≐〈 refl ∘ ~ nj 〉 
    id ⊸ [ Γ ∣ sound g ]f ∘ (sound f ⊸ id ∘ j)
  ≐〈 ~ ass 〉 
    id ⊸ [ Γ ∣ sound g ]f ∘ sound f ⊸ id ∘ j
  ≐〈 ~ swap⊸ ∘ refl 〉 
    sound f ⊸ id ∘ id ⊸ [ Γ ∣ sound g ]f ∘ j
  ≐〈 refl ∘ ~ (L⋆-j Γ) 〉 
    sound f ⊸ id ∘ id ⊸ [ Γ ∣ sound g ]f ∘ (L⋆ Γ ∘ j)
  ≐〈 ~ ass ∙ (ass ∘ refl) 〉 
    sound f ⊸ id ∘ (id ⊸ [ Γ ∣ sound g ]f ∘ L⋆ Γ) ∘ j
  ≐〈 refl ∘ (~ (nL⋆2 Γ (sound g)))  ∘ refl 〉 
    sound f ⊸ id ∘ (L⋆ Γ ∘ id ⊸ sound g) ∘ j
  ≐〈 ~ ass ∘ refl ∙ ass 〉
    sound f ⊸ id ∘ L⋆ Γ ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut-j {Γ = Γ} .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  proof≐
    id ⊸ sound (ccut Γ₀ f g refl) ∘ j
  ≐〈 refl ⊸ sound-ccut-j Γ₀ f g refl ∘ refl 〉 
    id ⊸ ([ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ∘ j
  ≐〈 (id⊸∘ ∘ refl) ∙ ass 〉 
    id ⊸ [ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (id ⊸ sound g ∘ j)
  qed≐
sound-ccut-j Δ₀ f (⊸r g) refl = sound-ccut-j Δ₀ f g refl
sound-ccut-j Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
sound-ccut-j {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} {A} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) = 
  proof≐
    i (sound (ccut Δ₀ f g refl)) ∘ L⋆ (Δ₀ ++ _ ∷ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 i (sound-ccut-j Δ₀ f g refl) ∘ refl ∘ refl 〉 
    i ([ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ sound g) ∘ L⋆ (Δ₀ ++ _ ∷ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ~ ni1 ∘ refl ∘ refl 〉 
    i (sound g) ∘ [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ _ ∷ Γ ++ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ass ∘ refl 〉
    i (sound g) ∘ ([ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ L⋆ (Δ₀ ++ _ ∷ Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ L⋆ass Δ₀ (_ ∷ Γ ++ Γ₀)) ∘ refl 〉  
    i (sound g) ∘ ([ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ⊸ id ∘ (L⋆ Δ₀ ∘ L⋆ (_ ∷ Γ ++ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (~ ass ∙ (~ (nL⋆ Δ₀ (sound f ⊸ id ∘ L⋆ Γ)) ∘ refl)) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (sound f ⊸ id ∘ L⋆ Γ) ⊸ id ∘ L⋆ (_ ∷ Γ ++ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ (refl ⊸ rid ∙ f⊸∘) ∘ refl ∙ ass) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (L⋆ Γ ⊸ id ∘ sound f ⊸ id ⊸ id ∘ L⋆ (_ ∷ Γ ++ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ lemma) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ (id ⊸ (sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (~ ass ∙ (~ ass ∙ (refl ∘ (~ f⊸∘ ∙ lid ⊸ refl) ∘ refl) ∘ refl)) ∘ refl 〉
    i (sound g) ∘ (L⋆ Δ₀ ∘ id ⊸ (sound f ⊸ id ∘ L⋆ Γ) ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (nL⋆2 Δ₀ (sound f ⊸ id ∘ L⋆ Γ) ∘ refl ∘ refl) ∘ refl 〉
    i (sound g) ∘ ((id ⊸ [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f) ∘ L⋆ Δ₀ ∘ L ∘ L⋆ Γ₀) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (ass ∙ ass) ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (L⋆ Δ₀ ∘ (L ∘ L⋆ Γ₀))) ∘ id ⊸ sound g'
  ≐〈 refl ∘ (refl ∘ ~ (L⋆ass Δ₀ (A ∷ Γ₀))) ∘ refl 〉 
    i (sound g) ∘ (id ⊸ [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀)) ∘ id ⊸ sound g'
  ≐〈 ~ ass ∘ refl 〉 
    i (sound g) ∘ id ⊸ [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ~ ni2 ∘ refl ∘ refl 〉
    [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ i (sound g) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g'
  ≐〈 ass ∘ refl ∙ ass 〉
    [ Δ₀ ∣ sound f ⊸ id ∘ L⋆ Γ ]f ∘ (i (sound g) ∘ L⋆ (Δ₀ ++ A ∷ Γ₀) ∘ id ⊸ sound g')
  qed≐
  where
    lemma : L⋆ Γ ⊸ id ∘ (sound f ⊸ id) ⊸ id ∘ (L ∘ L⋆ (Γ ++ Γ₀)) ≐ id ⊸ (sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
    lemma =
        proof≐
          L⋆ Γ ⊸ id ∘ (sound f ⊸ id) ⊸ id ∘ (L ∘ L⋆ (Γ ++ Γ₀))
       ≐〈 ~ ass ∙ (ass ∙ (refl ∘ ((refl ⊸ (~ f⊸id)) ∘ refl ∙ nL ∙ (refl ∘ f⊸id ∙ ~ rid))) ∘ refl) 〉
          L⋆ Γ ⊸ id ∘ (id ⊸ (sound f ⊸ id) ∘ L) ∘ L⋆ (Γ ++ Γ₀)
        ≐〈 ~ ass ∘ refl 〉 
          L⋆ Γ ⊸ id ∘ id ⊸ (sound f ⊸ id) ∘ L ∘ L⋆ (Γ ++ Γ₀)
        ≐〈 ((swap⊸ ∘ refl) ∙ ass ∘ refl) ∙ ass 〉 
          id ⊸ (sound f ⊸ id) ∘ (L⋆ Γ ⊸ id ∘ L ∘ L⋆ (Γ ++ Γ₀))
        ≐〈 refl ∘ L⋆LL⋆ Γ Δ Γ₀  〉 
          id ⊸ (sound f ⊸ id) ∘ (id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀)
        ≐〈 ~ ass ∙ (~ ass ∘ refl)  〉 
          id ⊸ (sound f ⊸ id) ∘ id ⊸ L⋆ Γ ∘ L ∘ L⋆ Γ₀
        qed≐
sound-ccut-j {Γ = Γ'} .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) = 
  proof≐
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound (ccut Γ₀ f g' refl)
  ≐〈 refl ∘ refl ⊸ sound-ccut-j Γ₀ f g' refl 〉
    i (sound g) ∘ L⋆ Γ ∘ id ⊸ ([ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ sound g')
  ≐〈 refl ∘ id⊸∘ 〉
    i (sound g) ∘ L⋆ Γ ∘ (id ⊸ [ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ id ⊸ sound g')
  ≐〈 (~ ass) ∙ (ass ∘ refl) 〉
    i (sound g) ∘ (L⋆ Γ ∘ id ⊸ [ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f) ∘ id ⊸ sound g'
  ≐〈 refl ∘ nL⋆2 Γ [ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ refl 〉
    i (sound g) ∘ (id ⊸ [ Γ ∣ [ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ]f ∘ L⋆ Γ) ∘ id ⊸ sound g'
  ≐〈 ~ ass ∘ refl 〉
    i (sound g) ∘ id ⊸ [ Γ ++ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 ~ ni2 ∘ refl ∘ refl  〉
    [ Γ ++ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g'
  ≐〈 (ass ∘ refl) ∙ ass 〉
    [ Γ ++ Γ₀ ∣ sound f ⊸ id ∘ L⋆ Γ' ]f ∘ (i (sound g) ∘ L⋆ Γ ∘ id ⊸ sound g')
  qed≐
sound-ccut-j Δ₀ f (⊸c Δ₁ g g₁) p = {!!}



-- sound-⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → (f : S ∣ Γ ++ Δ ⊢ C)
--   → sound (⊸r⋆ Δ f) ≡ sound f
-- sound-⊸r⋆ [] f = refl
-- sound-⊸r⋆ {Γ = Γ} (_ ∷ Δ) f = sound-⊸r⋆ {Γ = Γ ++ _ ∷ []} Δ f 

-- sound-ax : ∀{A} → sound (ax {A}) ≐ id
-- sound-ax {` X} = baseax
-- sound-ax {A ⊸ B} =
--   i (refl ⊸ sound-ax ∙ f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘ (refl ⊸ sound-ax ∙ f⊸id)
--   ∙ (~ rid ∙ ijL)

-- soundcmplt : ∀{S C} → (f : S ⇒ C) → sound (cmplt f) ≐ f
-- soundcmplt (base {Δ = Δ} f eq eq2) =
--   ≡-to-≐ (sound-⊸r⋆ Δ (base f eq eq2))
-- soundcmplt id = sound-ax
-- soundcmplt (f ∘ g) =
--   proof≐
--     sound (scut (cmplt g) (cmplt f))
--   ≐〈 sound-scut (cmplt g) (cmplt f) 〉
--     sound (cmplt f) ∘ sound (cmplt g)
--   ≐〈 soundcmplt f ∘ soundcmplt g 〉
--     f ∘ g
--   qed≐
-- soundcmplt (f ⊸ g) = 
--   proof≐ 
--     i (id ⊸ sound (cmplt f) ∘ j) ∘ (L ∘ id) ∘ id ⊸ sound (cmplt g)
--   ≐〈 i (refl ⊸ soundcmplt f ∘ refl) ∘ ~ rid ∘ refl ⊸ soundcmplt g 〉
--     i (id ⊸ f ∘ j) ∘ L ∘ id ⊸ g
--   ≐〈 i (~ nj) ∘ refl ∘ refl 〉
--     i (f ⊸ id ∘ j) ∘ L ∘ id ⊸ g
--   ≐〈 ~ ni1 ∘ refl ∘ refl 〉
--     i j ∘ ((f ⊸ id) ⊸ id) ∘ L ∘ id ⊸ g
--   ≐〈 ass ∘ refl 〉
--     i j ∘ ((f ⊸ id) ⊸ id ∘ L) ∘ id ⊸ g
--   ≐〈 refl ∘ (refl ⊸ (~ f⊸id) ∘ refl ∙ nL ∙ (refl ∘ f⊸id) ∙ ~ rid) ∘ refl 〉
--     i j ∘ (id ⊸ (f ⊸ id) ∘ L) ∘ id ⊸ g
--   ≐〈 ~ ass ∘ refl 〉
--     i j ∘ (id ⊸ (f ⊸ id)) ∘ L ∘ id ⊸ g
--   ≐〈 ~ ni2 ∘ refl ∘ refl 〉
--     f ⊸ id ∘ i j ∘ L ∘ id ⊸ g
--   ≐〈 ass ∘ refl 〉
--     f ⊸ id ∘ (i j ∘ L) ∘ id ⊸ g
--   ≐〈 refl ∘ ijL ∘ refl 〉
--     f ⊸ id ∘ id ∘ id ⊸ g
--   ≐〈 ~ (rid ∘ refl) 〉
--     f ⊸ id ∘ id ⊸ g
--   ≐〈 ~ f⊸∘ 〉
--     (id ∘ f) ⊸ (id ∘ g)
--    ≐〈 lid ⊸ lid 〉
--     f ⊸ g
--   qed≐
-- soundcmplt (i e) =
--   proof≐
--     i (sound (cmplt e)) ∘ id ∘ id ⊸ sound ax
--   ≐〈 refl ∘ (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid ∙ ~ rid 〉 
--     i (sound (cmplt e))
--   ≐〈 i (soundcmplt e) 〉 
--     i e
--   qed≐
-- soundcmplt j = (refl ⊸ sound-ax ∙ f⊸id ∘ refl) ∙ lid
-- soundcmplt L = 
--   proof≐
--     i (id ⊸ (i (id ⊸ sound ax ∘ j) ∘ (L ∘ id) ∘ id ⊸ sound ax) ∘ j) ∘ (L ∘ (L ∘ id)) ∘ id ⊸ sound ax
--   ≐〈 i (refl ⊸ (i (refl ⊸ sound-ax ∙ f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘
--        (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid) ∘ refl) ∘ (~ ass ∙ ~ rid) ∘ (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid 〉
--     i (id ⊸ (i j ∘ L) ∘ j) ∘ (L ∘ L)
--   ≐〈 i (refl ⊸ ijL ∘ refl) ∘ refl 〉
--     i (id ⊸ id ∘ j) ∘ (L ∘ L)
--   ≐〈 i (f⊸id ∘ refl ∙ lid) ∘ refl 〉
--     i j ∘ (L ∘ L)
--   ≐〈 ~ ass 〉
--     i j ∘ L ∘ L
--   ≐〈 ijL ∘ refl 〉
--     id ∘ L
--   ≐〈 lid 〉
--     L
--   qed≐


