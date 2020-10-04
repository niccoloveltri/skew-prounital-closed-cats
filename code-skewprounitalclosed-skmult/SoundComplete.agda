{-# OPTIONS --rewriting --allow-unsolved-metas #-}

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

sound-scut : ∀ {S Γ Δ A C}
  → (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C)
  → sound (scut f g) ≐ sem-scut {S}{Γ}{Δ} (sound f) (sound g)
sound-ccut-n : ∀ {T Γ Δ} Δ₀ {Δ' A C}
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ C) (p : Δ ≡ Δ₀ ++ A ∷ Δ')
  → sound (ccut Δ₀ f g p) ≐ sem-ccut-n {T}{Γ} Δ₀ (sound f) (sound g) p
sound-ccut-j : ∀ {T Γ Δ} Δ₀ {Δ' A A' C}
  → (f : just A' ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ C) (p : Δ ≡ Δ₀ ++ A ∷ Δ')
  → sound (ccut Δ₀ f g p) ≐ sem-ccut-j {T}{Γ} Δ₀ (sound f) (sound g) p

sound-scut f g = {!!}

sound-ccut-n Δ₀ f g p = {!!}

sound-ccut-j Δ₀ f g p = {!!}

sound-⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → (f : S ∣ Γ ++ Δ ⊢ C)
  → sound (⊸r⋆ Δ f) ≡ sound f
sound-⊸r⋆ [] f = refl
sound-⊸r⋆ {Γ = Γ} (_ ∷ Δ) f = sound-⊸r⋆ {Γ = Γ ++ _ ∷ []} Δ f 

sound-ax : ∀{A} → sound (ax {A}) ≐ id
sound-ax {` X} = baseax
sound-ax {A ⊸ B} =
  i (refl ⊸ sound-ax ∙ f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘ (refl ⊸ sound-ax ∙ f⊸id)
  ∙ (~ rid ∙ ijL)

soundcmplt : ∀{S C} → (f : S ⇒ C) → sound (cmplt f) ≐ f
soundcmplt (base {Δ = Δ} f eq eq2) =
  ≡-to-≐ (sound-⊸r⋆ Δ (base f eq eq2))
soundcmplt id = sound-ax
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
    i (sound (cmplt e)) ∘ id ∘ id ⊸ sound ax
  ≐〈 refl ∘ (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid ∙ ~ rid 〉 
    i (sound (cmplt e))
  ≐〈 i (soundcmplt e) 〉 
    i e
  qed≐
soundcmplt j = (refl ⊸ sound-ax ∙ f⊸id ∘ refl) ∙ lid
soundcmplt L = 
  proof≐
    i (id ⊸ (i (id ⊸ sound ax ∘ j) ∘ (L ∘ id) ∘ id ⊸ sound ax) ∘ j) ∘ (L ∘ (L ∘ id)) ∘ id ⊸ sound ax
  ≐〈 i (refl ⊸ (i (refl ⊸ sound-ax ∙ f⊸id ∘ refl ∙ lid) ∘ ~ rid ∘
       (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid) ∘ refl) ∘ (~ ass ∙ ~ rid) ∘ (refl ⊸ sound-ax ∙ f⊸id) ∙ ~ rid 〉
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


