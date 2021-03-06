{-# OPTIONS --rewriting #-}

open import SkMults

module CompleteSound where 

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
open import MulticatLaws
open import Complete
open import Sound
open import CutsCong

-- ∀ f. cmplt (sound f) ≗ ⊸r⋆ f


-- ====================================================================

ccut⊸r-1 : {S T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A B C : Fma} 
  → (f : S ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ B ⊸ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (⊸r-1 g) (cong₂ _++_ eq (refl {x = B ∷ []}))
    ≡ ⊸r-1 {Γ = Δ₀ ++ asCxt S Γ ++ Δ'} (ccut Δ₀ f g eq)
ccut⊸r-1 Δ₀ f (uf g) eq with cases∷ Δ₀ eq
ccut⊸r-1 {nothing} .[] f (uf g) refl | inj₁ (refl , refl , refl) = scut⊸r-1 f g
ccut⊸r-1 {just x} .[] f (uf g) refl | inj₁ (refl , refl , refl) = cong uf (scut⊸r-1 f g)
ccut⊸r-1 .(_ ∷ Γ') f (uf g) refl | inj₂ (Γ' , refl , refl) =
  cong uf (ccut⊸r-1  Γ' f g refl)
ccut⊸r-1 Δ₀ f (⊸r g) refl = refl
ccut⊸r-1 Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
ccut⊸r-1 Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ B ∷ []) A = refl
ccut⊸r-1 .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ' ++ B ∷ []) A =
    cong (⊸l g) (ccut⊸r-1 Γ₀ f g₁ refl)
ccut⊸r-1 Δ₀ {Δ'} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) eq with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A ∷ Δ') (sym eq)
ccut⊸r-1 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
ccut⊸r-1 .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ₀) {.(Γ₀' ++ Δ₂)} {A} {B} f (⊸c Δ₁ {.(Γ₀ ++ A ∷ Γ₀')} {Δ₂} {A₁} {B₁} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₁ Γ₀ (A ∷ Γ₀' ++ Δ₂ ++ B ∷ []) (A₁ ⊸ B₁) | cases++-inj₁ Γ₀ Γ₀' (Δ₂ ++ B ∷ []) A = refl    
ccut⊸r-1 .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Γ₀') {Δ'} {A} {B} f (⊸c Δ₁ {Γ} {.(Γ₀' ++ A ∷ Δ')} {A₁} {B₁} g g₁) refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ ++ Γ₀') (A ∷ Δ' ++ B ∷ []) (A₁ ⊸ B₁) | cases++-inj₂ Γ₀' Γ (Δ' ++ B ∷ []) A =
    cong (⊸c Δ₁ g) (ccut⊸r-1 (Δ₁ ++ B₁ ∷ Γ₀') f g₁ refl)    
ccut⊸r-1 _ {.(Γ ++ Δ₂)} {.(A ⊸ B₁)} {B} (uf f) (⊸c Δ₁ {Γ} {Δ₂} {A} {B₁} g g₁) refl | inj₂ ([] , refl , refl) with ccut⊸r-1 Δ₁ f (⊸c Δ₁ g g₁) refl
... | ih rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) = ih
ccut⊸r-1 _ {.(Γ ++ Δ₂)} {.(A ⊸ B₁)} {B} (⊸r {Γ = Γ₁} f) (⊸c Δ₁ {Γ} {Δ₂} {A} {B₁} g g₁) refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) = ccut⊸r-1 Δ₁ (ccut Γ₁ g f refl) g₁ refl
ccut⊸r-1 _ {.(Γ ++ Δ₂)} {.(A ⊸ B₁)} {B} (⊸l f f₁) (⊸c Δ₁ {Γ} {Δ₂} {A} {B₁} g g₁) refl | inj₂ ([] , refl , refl) with ccut⊸r-1 Δ₁ f₁ (⊸c Δ₁ g g₁) refl
... | ih rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) = cong (⊸c Δ₁ f) ih
ccut⊸r-1 {S} _ {.(Γ ++ Δ₂)} {.(A ⊸ B₁)} {B} (⊸c Δ₀ f f₁) (⊸c Δ₁ {Γ} {Δ₂} {A} {B₁} g g₁) refl | inj₂ ([] , refl , refl) with ccut⊸r-1 Δ₁ f₁ (⊸c Δ₁ g g₁) refl
... | ih rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) = cong (⊸c (Δ₁ ++ asCxt S Δ₀) f) ih
ccut⊸r-1 {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ A ⊸ B₁ ∷ Γ ++ Δ₂)} {.x} {B} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} {A} {B₁} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl)
  rewrite cases++-inj₂ (x ∷ Γ₀) Δ₀ (Γ ++ Δ₂ ++ B ∷ []) (A ⊸ B₁) = cong (⊸c (Δ₀ ++ asCxt S Γ₁ ++ Γ₀) g) (ccut⊸r-1 Δ₀ f g₁ refl)    

cmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → cmplt (sound f) ≗ ⊸r⋆ Γ f
cmpltsound (base f eq eq2) = refl
cmpltsound (uf f) = 
  proof≗
    ⊸r (uf (scut (scut ax ax) (cmplt (sound f))))
  ≗〈 ⊸r (uf (cong-scut1 (scut-unit _) ∙ scut-unit _ ∙ cmpltsound f)) 〉
    ⊸r (uf (⊸r⋆ _ f))
  ≗〈 ⊸r (~ (⊸r⋆uf _ _)) 〉
    ⊸r (⊸r⋆ _ (uf f))
  qed≗
cmpltsound {Γ = Γ} (⊸r {A = A} {B} f) =
  cmpltsound f ∙ ⊸r⋆ass Γ (A ∷ []) f
cmpltsound (⊸l {Γ = Γ}{Δ}{A}{B}{C} f g) = 
  proof≗
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (cong-scut2 (cmplt (L⋆ Γ)) (⊸l (cmpltsound f) refl)) 〉
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))
  ≗〈 cong-scut1 {h = (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))} (⊸r (⊸l refl (cmpltsound g))) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (cong-scut1 (cmplt-L⋆ Γ)) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) ax)
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut-unit2 (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)
  ≗〈 cong-scut2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (ccut⊸r⋆ [] Γ (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl refl) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax))
  ≗〈 scut⊸r⋆ Γ (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax) 〉
    ⊸r⋆ Γ (⊸l (scut (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax) (scut (⊸r⋆ Δ g) ax))
  ≗〈 cong⊸r⋆ Γ (⊸l (scut-unit2 (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax))) (scut-unit2 (⊸r⋆ Δ g))) 〉
    ⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (⊸l (scut⊸r⋆⊸r⋆-1 Γ f) refl) 〉
    ⊸r⋆ Γ (⊸l f (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (~ (⊸r⋆⊸l Δ f g)) 〉
    ⊸r⋆ Γ (⊸r⋆ Δ (⊸l f g))
  ≗〈 ~ (⊸r⋆ass Γ Δ (⊸l f g)) 〉
    ⊸r⋆ (Γ ++ Δ) (⊸l f g)
  qed≗
cmpltsound (⊸c Δ₀ {Γ} {Δ₁} {A} {B} f g) =
  proof≗
    scut (cmplt (sound g)) (cmplt [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f)
  ≗〈 cong-scut1 {h = cmplt [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f} (cmpltsound g)  〉
    scut (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g) (cmplt [ Δ₀ ∣ (L⋆ Γ ⊸ id) ∘ (i (sound f) ⊸ id) ∘ L⋆ Γ ]f)
  ≗〈 cong-scut2 (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g) [ Δ₀ ∣cmplt]f 〉
    scut (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g) (⊸r⋆ Δ₀ (⊸l⋆ Δ₀ {[]}
      (scut (cmplt (L⋆ Γ)) (⊸r (⊸l (uf (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))) (scut ax ax))))))
  ≗〈 cong-scut2 (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g)
      (cong⊸r⋆ Δ₀ (cong⊸l⋆ Δ₀ (cong-scut2 (cmplt (L⋆ Γ))
        (⊸r (⊸l refl (scut-unit _)))))) 〉
    scut (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g) (⊸r⋆ Δ₀ (⊸l⋆ Δ₀ {[]}
      (scut (cmplt (L⋆ Γ)) (⊸r (⊸l (uf (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))) ax)))))
  ≗〈 scut⊸r⋆ Δ₀ (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g) _ 〉
    ⊸r⋆ Δ₀ (scut (⊸r⋆ (Δ₀ ++ B ∷ Δ₁) g)
      (⊸l⋆ Δ₀ {[]} (scut (cmplt (L⋆ Γ)) (⊸r (⊸l (uf (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))) ax)))))
  ≗〈 cong⊸r⋆ Δ₀ (cong-scut1 (⊸r⋆ass Δ₀ (B ∷ Δ₁) g)) 〉
    ⊸r⋆ Δ₀ (scut  (⊸r⋆ Δ₀ (⊸r (⊸r⋆ Δ₁ g)))
      (⊸l⋆ Δ₀ {[]} (scut (cmplt (L⋆ Γ)) (⊸r (⊸l (uf (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))) ax)))))
  ≗〈 cong⊸r⋆ Δ₀ (scut⊸r⋆⊸l⋆ Δ₀) 〉
    ⊸r⋆ {_}{[]} Δ₀
      (scut {Δ = []} (⊸r (⊸r⋆ Δ₁ g)) (scut (cmplt (L⋆ Γ)) (⊸r (⊸l (uf (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))) ax))))
  ≗〈 cong⊸r⋆ Δ₀ (cong-scut2 (⊸r (⊸r⋆ Δ₁ g)) (cong-scut (cmplt-L⋆ Γ)
             (⊸r (⊸l (uf (cong-scut (cmplt-L⋆ Γ) (⊸l (cmpltsound f) refl))) refl))))  〉
    ⊸r⋆ Δ₀ (⊸r
      (scut (⊸r (⊸r⋆ Δ₁ g))
        (scut (ccut [] (uf (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)  ax))
          (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) ax)))
   ≗〈 cong⊸r⋆ Δ₀ (⊸r (cong-scut2 (⊸r (⊸r⋆ Δ₁ g)) (scut-unit2 _ ∙
      cong-ccut1 [] (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl (scut-unit2 _)))) 〉
    ⊸r⋆ Δ₀ (⊸r
      (scut (⊸r (⊸r⋆ Δ₁ g))
        (ccut [] (uf (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl))
          (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)))
   ≗〈 cong⊸r⋆ Δ₀ (⊸r (cong-scut2 (⊸r (⊸r⋆ Δ₁ g))
              (ccut⊸r⋆ [] Γ (uf (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl))
                (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl refl ))) 〉
    ⊸r⋆ Δ₀ (⊸r (scut (⊸r (⊸r⋆ Δ₁ g)) (⊸r⋆ Γ (⊸l (uf
      (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) (⊸r⋆-1 Γ ax))) ax))))
   ≗〈 cong⊸r⋆ Δ₀ (⊸r (scut⊸r⋆ Γ (⊸r (⊸r⋆ Δ₁ g)) _)) 〉
     ⊸r⋆ Δ₀ (⊸r (⊸r⋆ Γ
       (scut (ccut Δ₀ (uf (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) (⊸r⋆-1 Γ ax)))
                      (⊸r⋆ {_}{Δ₀ ++ _ ∷ []} Δ₁ g) refl) ax)))
   ≗〈 cong⊸r⋆ Δ₀ (⊸r (cong⊸r⋆ Γ (scut-unit2 _))) 〉
    ⊸r⋆ Δ₀ (⊸r (⊸r⋆ Γ
       (ccut Δ₀ (uf (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) (⊸r⋆-1 Γ ax)))
                (⊸r⋆ {_}{Δ₀ ++ _ ∷ []} Δ₁ g) refl)))
   ≗〈 cong⊸r⋆ Δ₀ (⊸r (cong⊸r⋆ Γ (ccut⊸r⋆ Δ₀ Δ₁ _ _ refl refl))) 〉
    ⊸r⋆ Δ₀ (⊸r (⊸r⋆ Γ (⊸r⋆ Δ₁
         (ccut Δ₀ (uf (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) (⊸r⋆-1 Γ ax))) g refl))))
   ≗〈 ~ (⊸r⋆ass Δ₀ (A ⊸ B ∷ Γ ++ Δ₁) _ ∙ cong⊸r⋆ Δ₀ (⊸r (⊸r⋆ass Γ Δ₁ _ ∙
        cong⊸r⋆ Γ (cong⊸r⋆ Δ₁ (cong-ccut1 Δ₀ g refl (uf (~ (cong-scut1
          (ccut⊸r⋆ [] Γ (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl refl)))))))) ) 〉
    ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁)
         (ccut Δ₀ (uf (scut (⊸r⋆ Γ (ccut [] (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl)) (⊸r⋆-1 Γ ax))) g refl)
   ≗〈 cong⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (cong-ccut1 Δ₀ g refl
        (uf (≡-to-≗ (scut⊸r⋆-1 Γ (⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax)) _)))) 〉
    ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁)
         (ccut Δ₀ (uf (⊸r⋆-1 Γ (scut (⊸r⋆ Γ (ccut [] (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl)) ax))) g refl)
   ≗〈 cong⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (cong-ccut1 Δ₀ g refl (uf (cong⊸r⋆-1 Γ (scut-unit2 _)))) 〉
    ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁)
         (ccut Δ₀ (uf (⊸r⋆-1 Γ (⊸r⋆ Γ (ccut [] (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl)))) g refl)
   ≗〈 cong⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (cong-ccut1 Δ₀ g refl (uf (≡-to-≗ (⊸r⋆-iso2 Γ _)))) 〉
    ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁)
         (ccut Δ₀ (uf (ccut [] (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl)) g refl)
   ≗〈 refl 〉
     ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (ccut Δ₀ (uf (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax)) g refl)
   ≗〈 cong⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (cong-ccut1 Δ₀ g refl (uf (⊸l (scut⊸r⋆⊸r⋆-1 Γ f) refl))) 〉
     ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (ccut Δ₀ (uf (⊸l f ax)) g refl)
   ≗〈 cong⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (⊸c-alt Δ₀ f g refl) 〉
    ⊸r⋆ (Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁) (⊸c Δ₀ f g)
  qed≗


-- ====================================================================

-- Strong completeness and full adequacy 

strcmplt :  {S : Stp} → {Γ : Cxt} → {A : Fma} → S ⇒ [ Γ ∣ A ] → S ∣ Γ ⊢ A
strcmplt {Γ = Γ} f = ⊸r⋆-1 Γ (cmplt f)

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → strcmplt (sound f) ≗ f
strcmpltsound {S} {Γ} f = 
  proof≗
    ⊸r⋆-1 Γ (cmplt (sound f))
  ≗〈 cong⊸r⋆-1 Γ (cmpltsound f) 〉
    ⊸r⋆-1 Γ (⊸r⋆ Γ f)
  ≗〈 ≡-to-≗ (⊸r⋆-iso2 Γ f) 〉
    f
  qed≗ 

open import SoundComplete

sound-⊸r-1 : {S : Stp} {Γ : Cxt} {A B : Fma} → (f : S ∣ Γ ⊢ A ⊸ B)
  → sound (⊸r-1 f) ≐ sound f
sound-⊸r-1 (uf f) = refl ⊸ sound-⊸r-1 f ∘ refl
sound-⊸r-1 (⊸r f) = refl
sound-⊸r-1 (⊸l f g) = refl ∘ refl ⊸ sound-⊸r-1 g
sound-⊸r-1 (⊸c Δ₀ f g) = refl ∘ sound-⊸r-1 g

sound-⊸r⋆-1 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → (f : S ∣ Γ ⊢ [ Δ ∣ C ])
  → sound (⊸r⋆-1 Δ f) ≐ sound f
sound-⊸r⋆-1 [] f = refl
sound-⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f =
  sound-⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (⊸r-1 f)
  ∙ sound-⊸r-1 f

soundstrcmplt : ∀ {S Γ C} (f : S ⇒ [ Γ ∣ C ])
  → sound (strcmplt {S}{Γ} f) ≐ f
soundstrcmplt {S}{Γ} f =
  sound-⊸r⋆-1 Γ (cmplt f) ∙ soundcmplt f


