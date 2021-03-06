{-# OPTIONS --rewriting #-}

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
open import FreeSkewProunitalClosed
open import Formulae
open import SeqCalc
open import Sound
open import Complete
open import MulticatLaws

-- ====================================================================

-- ∀ f. cmplt (sound f) ≗ ⊸r⋆ f

⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → S ∣ Γ ++ Δ ⊢ C → S ∣ Γ ⊢ [ Δ ∣ C ]
⊸r⋆ [] f = f
⊸r⋆ (A ∷ Δ) f = ⊸r (⊸r⋆ Δ f)

⊸r⋆-1 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → S ∣ Γ ⊢ [ Δ ∣ C ] → S ∣ Γ ++ Δ ⊢ C 
⊸r⋆-1 [] f = f
⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f = ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (⊸r-1 f)

⊸r⋆-iso : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : S ∣ Γ ⊢ [ Δ ∣ C ]) → ⊸r⋆ Δ (⊸r⋆-1 Δ f) ≗ f
⊸r⋆-iso [] f = refl
⊸r⋆-iso (A ∷ Δ) f = ⊸r (⊸r⋆-iso Δ (⊸r-1 f)) ∙ ⊸r-iso f

⊸r⋆-iso2 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} (f : S ∣ Γ ++ Δ ⊢ C) → ⊸r⋆-1 Δ (⊸r⋆ Δ f) ≡ f
⊸r⋆-iso2 [] f = refl
⊸r⋆-iso2 {Γ = Γ} (A ∷ Δ) f = ⊸r⋆-iso2 {Γ = Γ ++ A ∷ []} Δ f

⊸r⋆ass : {S : Stp} {Γ : Cxt} (Δ Λ : Cxt) {C : Fma} → (f : S ∣ Γ ++ Δ ++ Λ ⊢ C)
  → ⊸r⋆ {S}{Γ} (Δ ++ Λ) f ≗ ⊸r⋆ Δ (⊸r⋆ Λ f)
⊸r⋆ass [] Λ f = refl
⊸r⋆ass (x ∷ Δ) Λ f = ⊸r (⊸r⋆ass Δ Λ f)

⊸r⋆uf : {Γ : Cxt} (Δ : Cxt) {A C : Fma} (f : just A ∣ Γ ++ Δ ⊢ C)
  → ⊸r⋆ Δ (uf f) ≗ uf (⊸r⋆ Δ f)
⊸r⋆uf [] f = refl
⊸r⋆uf {Γ} (B ∷ Δ) f =
  proof≗
    ⊸r (⊸r⋆ Δ (uf f))
  ≗〈 ⊸r (⊸r⋆uf {Γ ++ B ∷ []} Δ f) 〉
    ⊸r (uf _)
  ≗〈 ⊸ruf 〉
    uf (⊸r (⊸r⋆ Δ f))
  qed≗

⊸r⋆⊸l : {Γ Γ' : Cxt} (Δ : Cxt) {A B C : Fma} (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Γ' ++ Δ ⊢ C)
  → ⊸r⋆ {Γ = Γ ++ Γ'} Δ (⊸l f g) ≗ ⊸l f (⊸r⋆ {Γ = Γ'} Δ g)
⊸r⋆⊸l [] f g = refl
⊸r⋆⊸l {Γ}{Γ'} (A ∷ Δ) f g =
  proof≗
    ⊸r _
  ≗〈 ⊸r (⊸r⋆⊸l {Γ}{Γ' ++ A ∷ []} Δ f g) 〉
    ⊸r _
  ≗〈 ⊸r⊸l 〉
    ⊸l f (⊸r (⊸r⋆ Δ g))
  qed≗

⊸r⋆-1⊸l : {Γ Γ' : Cxt} (Δ : Cxt) {A B C : Fma} (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Γ' ⊢ [ Δ ∣ C ])
  → ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (⊸l f g) ≗ ⊸l f (⊸r⋆-1 {Γ = Γ'} Δ g)
⊸r⋆-1⊸l [] f g = refl
⊸r⋆-1⊸l (D ∷ Δ) f g = ⊸r⋆-1⊸l Δ f (⊸r-1 g)

scut⊸r⊸r⋆ : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A B D : Fma}
  → (f : S ∣ Γ ++ A ∷ [] ⊢ B)
  → (g : just (A ⊸ B) ∣ Γ' ++ Δ ⊢ D)
  → scut (⊸r f) (⊸r⋆ Δ g) ≡ ⊸r⋆ Δ (scut (⊸r f) g)
scut⊸r⊸r⋆ [] f g = refl
scut⊸r⊸r⋆ {Γ' = Γ'} (A' ∷ Δ) f g = cong ⊸r (scut⊸r⊸r⋆ {Γ' = Γ' ++ A' ∷ []} Δ f g)


scut⊸r-1 : {S : Stp} {Γ Δ : Cxt} {B C D : Fma}
  → (f : S ∣ Γ ⊢ B)
  → (g : just B ∣ Δ ⊢ C ⊸ D)
  → scut f (⊸r-1 g) ≡ ⊸r-1 {Γ = Γ ++ Δ} (scut f g)
scut⊸r-1 ax g = refl
scut⊸r-1 (uf f) g = cong uf (scut⊸r-1 f g)
scut⊸r-1 {Γ = Γ} (⊸r f) ax = trans (scut-ax (ccut Γ (uf ax) f refl)) (ccut-ax Γ f refl)
scut⊸r-1 (⊸r f) (⊸r g) = refl
scut⊸r-1 {Γ = Γ} (⊸r f) (⊸l g g') = scut⊸r-1 (ccut Γ g f refl) g'
scut⊸r-1 (⊸l f f') g = cong (⊸l f) (scut⊸r-1 f' g)

ccut⊸r-1 : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A B C : Fma} 
  → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ B ⊸ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (⊸r-1 g) (cong₂ _++_ eq (refl {x = B ∷ []}))
    ≡ ⊸r-1 {Γ = Δ₀ ++ Γ ++ Δ'} (ccut Δ₀ f g eq)
ccut⊸r-1 Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut⊸r-1 Δ₀ f (uf g) eq with cases∷ Δ₀ eq
ccut⊸r-1 .[] f (uf g) refl | inj₁ (refl , refl , refl) = scut⊸r-1 f g
ccut⊸r-1 .(_ ∷ Γ') f (uf g) refl | inj₂ (Γ' , refl , refl) =
  cong uf (ccut⊸r-1  Γ' f g refl)
ccut⊸r-1 Δ₀ f (⊸r g) refl = refl
ccut⊸r-1 Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
ccut⊸r-1 Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀) (Γ₀ ++ Δ ++ B ∷ []) (Δ ++ B ∷ []) refl
ccut⊸r-1 Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ ++ B ∷ []} q
ccut⊸r-1 Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl = refl
ccut⊸r-1 Δ₀ {.(Γ₀ ++ Δ)} {A} {B} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥2 Δ₀ {Γ₀ ++ Γ₀'} q)
ccut⊸r-1 .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) Γ (Δ' ++ B ∷ []) (Γ₀ ++ A ∷ Δ' ++ B ∷ []) refl
ccut⊸r-1 .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥4 Γ {Γ₀'}{Γ₀} p)
ccut⊸r-1 .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with ++canc {xs = Γ₀}{Γ₀'} Γ q
ccut⊸r-1 .(Γ ++ Γ₀) {Δ'} {A} {B} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) | refl =
  cong (⊸l g) (ccut⊸r-1 Γ₀ f g₁ refl)

scut⊸r⊸r⋆-1 : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A B D : Fma}
  → (f : S ∣ Γ ++ A ∷ [] ⊢ B)
  → (g : just (A ⊸ B) ∣ Γ' ⊢ [ Δ ∣ D ])
  → scut (⊸r f) (⊸r⋆-1 Δ g) ≡ ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (scut (⊸r f) g)
scut⊸r⊸r⋆-1 [] f g = refl
scut⊸r⊸r⋆-1 {Γ = Γ}{Γ'} (A' ∷ Δ) f g =
  trans (scut⊸r⊸r⋆-1 {Γ' = Γ' ++ A' ∷ []} Δ f (⊸r-1 g))
        (cong (⊸r⋆-1 {Γ = Γ ++ Γ' ++ A' ∷ []} Δ) (scut⊸r-1 (⊸r f) g))


cong⊸r⋆ : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ++ Δ ⊢ C} → f ≗ g → ⊸r⋆ Δ f ≗ ⊸r⋆ Δ g
cong⊸r⋆ [] p = p
cong⊸r⋆ (_ ∷ Δ) p = ⊸r (cong⊸r⋆ Δ p)

cong⊸r⋆-1 : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ⊢ [ Δ ∣ C ]} → f ≗ g → ⊸r⋆-1 Δ f ≗ ⊸r⋆-1 Δ g
cong⊸r⋆-1 [] p = p
cong⊸r⋆-1 {Γ = Γ} (A ∷ Δ) p = cong⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (cong⊸r-1 p)

scut⊸r⋆⊸r⋆-1 : ∀{S}{Γ} Δ {C}(f : S ∣ Γ ++ Δ ⊢ C)
  → scut (⊸r⋆ Δ f) (⊸r⋆-1 Δ ax) ≡ f
scut⊸r⋆⊸r⋆-1 [] f = scut-ax f
scut⊸r⋆⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f =
  begin
    scut (⊸r⋆ (A ∷ Δ) f) (⊸r⋆-1 (A ∷ Δ) ax)
  ≡⟨ scut⊸r⊸r⋆-1 Δ _ _ ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (scut (⊸r (⊸r⋆ Δ f)) (⊸r-1 ax))
  ≡⟨ cong (⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ) (scut-ax (ccut Γ (uf ax) (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl)) ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (ccut Γ (uf ax) (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl)
  ≡⟨ cong (⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ) (ccut-ax Γ (⊸r⋆ {Γ = Γ ++ A ∷ []} Δ f) refl) ⟩
    ⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (subst-cxt refl (⊸r⋆ Δ f))
  ≡⟨ ⊸r⋆-iso2 {Γ = Γ ++ A ∷ []} Δ f ⟩
    f
  ∎

ccut⊸r⋆ : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             (f : nothing ∣ Γ ⊢ A)  (g : T ∣ Δ ++ Λ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') (s : Δ ++ Λ ≡ Δ₀ ++ A ∷ Δ' ++ Λ) →  
                                        ccut Δ₀ f (⊸r⋆ Λ g) r ≗ ⊸r⋆ Λ (ccut Δ₀ {Δ' ++ Λ} f g s)
ccut⊸r⋆ Δ₀ [] f g refl refl = refl
ccut⊸r⋆ Δ₀ (A ∷ Λ) {Δ'} {B} f g refl refl = ⊸r (ccut⊸r⋆ {Δ = Δ₀ ++ B ∷ Δ' ++ A ∷ []} Δ₀ Λ f g refl refl )

cmplt-L⋆ : (Δ : Cxt) {A C : Fma}
  → cmplt (L⋆ Δ {A}{C}) ≗ ⊸r {Γ = []} (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax))
cmplt-L⋆ [] = ax⊸
cmplt-L⋆ (B ∷ Δ) =
  proof≗
    scut (cmplt (L⋆ Δ)) (⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax)))
  ≗〈 scut≗ (cmplt-L⋆ Δ) (⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax))) 〉 
    ⊸r (⊸r (scut (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl) ax))  
  ≗〈 ⊸r (⊸r (≡-to-≗ (scut-ax (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl)))) 〉 
    ⊸r (⊸r (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl))  
  ≗〈 ⊸r (⊸r (ccut⊸r⋆ [] Δ  (uf (⊸l (uf ax) ax)) (⊸l (uf (⊸r⋆-1 Δ ax)) ax) refl refl)) 〉 
    ⊸r (⊸r (⊸r⋆ Δ (⊸l (uf (⊸l (uf ax) (⊸r⋆-1 Δ ax))) ax)))
  ≗〈 ⊸r (⊸r (cong⊸r⋆ Δ (⊸l (uf (~ (⊸r⋆-1⊸l Δ (uf ax) ax))) refl))) 〉 
    ⊸r (⊸r (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ (⊸l (uf ax) ax))) ax)))
  qed≗

-- ====================================================================

-- the function cmplt ∘ sound is ≗-related to ⊸r⋆

cmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → cmplt (sound f) ≗ ⊸r⋆ Γ f
cmpltsound ax = refl
cmpltsound (uf f) =
  proof≗
    ⊸r (uf (cmplt (sound f)))
  ≗〈 ⊸r (uf (cmpltsound f)) 〉
    ⊸r (uf (⊸r⋆ _ f))
  ≗〈 ⊸r (~ (⊸r⋆uf _ _)) 〉
    ⊸r (⊸r⋆ _ (uf f))
  qed≗
cmpltsound {Γ = Γ} (⊸r {A = A} {B} f) =
  cmpltsound f ∙ ⊸r⋆ass Γ (A ∷ []) f
cmpltsound (⊸l {Γ = Γ}{Δ}{A}{B}{C} f g) = 
  proof≗
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (cmplt (sound f)) ax))
  ≗〈 scut≗2 (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut≗2 (cmplt (L⋆ Γ)) (⊸l (cmpltsound f) refl)) 〉
    scut (⊸r (⊸l (uf ax) (cmplt (sound g)))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))
  ≗〈 scut≗ (⊸r (⊸l refl (cmpltsound g))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))  〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut (cmplt (L⋆ Γ)) (⊸l (⊸r⋆ Γ f) ax))
  ≗〈 scut≗2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut≗ (cmplt-L⋆ Γ) (⊸l (⊸r⋆ Γ f) ax)) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (scut (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl) ax)
  ≗〈 scut≗2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (≡-to-≗ (scut-ax (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl))) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (ccut [] (⊸r⋆ Γ f) (⊸r⋆ Γ (⊸l (uf (⊸r⋆-1 Γ ax)) ax)) refl)
  ≗〈 scut≗2 (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (ccut⊸r⋆ [] Γ (⊸r⋆ Γ f) (⊸l (uf (⊸r⋆-1 Γ ax)) ax) refl refl) 〉
    scut (⊸r (⊸l (uf ax) (⊸r⋆ Δ g))) (⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax))
  ≗〈 ≡-to-≗ (scut⊸r⊸r⋆ Γ (⊸l (uf ax) (⊸r⋆ Δ g)) (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax)) 〉
    ⊸r⋆ Γ (⊸l (scut (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) ax) (scut (⊸r⋆ Δ g) ax))
  ≗〈 cong⊸r⋆ Γ (⊸l (≡-to-≗ (scut-ax (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)))) (≡-to-≗ (scut-ax (⊸r⋆ Δ g)))) 〉
    ⊸r⋆ Γ (⊸l (scut (⊸r⋆ Γ f) (⊸r⋆-1 Γ ax)) (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (⊸l (≡-to-≗ (scut⊸r⋆⊸r⋆-1 Γ f)) refl) 〉
    ⊸r⋆ Γ (⊸l f (⊸r⋆ Δ g))
  ≗〈 cong⊸r⋆ Γ (~ (⊸r⋆⊸l Δ f g)) 〉
    ⊸r⋆ Γ (⊸r⋆ Δ (⊸l f g))
  ≗〈 ~ (⊸r⋆ass Γ Δ (⊸l f g)) 〉
    ⊸r⋆ (Γ ++ Δ) (⊸l f g)
  qed≗

-- ====================================================================

-- Strong completeness and full adequacy 

strcmplt :  {S : Stp} → {Γ : Cxt} → {A : Fma} → S ⇒ [ Γ ∣ A ] → S ∣ Γ ⊢ A
strcmplt {Γ = Γ} f = ⊸r⋆-1 Γ (cmplt f)

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Fma} → (f : S ∣ Γ ⊢ C) → strcmplt (sound f) ≗ f
strcmpltsound {just A} {Γ} f =
  proof≗
    ⊸r⋆-1 Γ (cmplt (sound f))
  ≗〈 cong⊸r⋆-1 Γ (cmpltsound f) 〉
    ⊸r⋆-1 Γ (⊸r⋆ Γ f)
  ≗〈 ≡-to-≗ (⊸r⋆-iso2 Γ f) 〉
    f
  qed≗ 
strcmpltsound {nothing} {Γ} f = 
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
sound-⊸r-1 ax =
  proof≐
    i (id ⊸ id ∘ j) ∘ (L ∘ id) ∘ id ⊸ id
  ≐〈 i (f⊸id ∘ refl) ∘ ~ rid ∘ f⊸id  〉
    i (id ∘ j) ∘ L ∘ id
  ≐〈 ~ rid ∙ (i lid ∘ refl) 〉
    i j ∘ L
  ≐〈 ijL 〉
    id
  qed≐
sound-⊸r-1 (uf f) = refl ⊸ sound-⊸r-1 f ∘ refl
sound-⊸r-1 (⊸r f) = refl
sound-⊸r-1 (⊸l f g) = refl ∘ refl ⊸ sound-⊸r-1 g

sound-⊸r⋆-1 : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → (f : S ∣ Γ ⊢ [ Δ ∣ C ])
  → sound (⊸r⋆-1 Δ f) ≐ sound f
sound-⊸r⋆-1 [] f = refl
sound-⊸r⋆-1 {Γ = Γ} (A ∷ Δ) f =
  sound-⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (⊸r-1 f)
  ∙ sound-⊸r-1 f

soundstrcmplt : ∀ {S Γ C} (f : S ⇒ [ Γ ∣ C ])
  → sound (strcmplt {S}{Γ} f) ≐ f
soundstrcmplt {just A}{Γ} f =
  sound-⊸r⋆-1 Γ (cmplt f) ∙ soundcmplt f
soundstrcmplt {nothing}{Γ} f =
  sound-⊸r⋆-1 Γ (cmplt f)
  ∙ soundcmplt f

-- ==================================================================

-- Since the rule uf is invertible, then the free skew closed category
-- is left-normal

jY-1 : ∀{A}{B} → nothing ⇒ A ⊸ B → just A ⇒ B
jY-1 f = sound (uf-1 (⊸r-1 (cmplt f)))

jY : ∀{A}{B} → just A ⇒ B → nothing ⇒ A ⊸ B
jY f = f ⊸ id ∘ j

left-normal₁ : ∀{A}{B} (f : nothing ⇒ A ⊸ B) → jY (jY-1 f) ≐ f
left-normal₁ {A}{B} f = 
  proof≐
    sound (uf-1 (⊸r-1 (cmplt f))) ⊸ id ∘ j
  ≐〈 ~ (soundcmplt _) 〉
    sound (cmplt (sound (uf-1 (⊸r-1 (cmplt f))) ⊸ id ∘ j))
  ≐〈 refl 〉
    sound {_}{[]} (⊸r (uf (scut (scut (cmplt (sound (uf-1 (⊸r-1 (cmplt f))))) ax) ax)))
  ≐〈 ≗sound≐ {_}{[]} (⊸r (uf (≡-to-≗ (trans (scut-ax _) (scut-ax (cmplt (sound (uf-1 (⊸r-1 (cmplt f)))))))))) 〉
    sound {_}{[]} (⊸r (uf (cmplt (sound (uf-1 (⊸r-1 (cmplt f)))))))
  ≐〈 ≗sound≐ {_}{[]} (⊸r (uf (cmpltsound (uf-1 (⊸r-1 (cmplt f)))))) 〉
    sound {_}{[]} (⊸r (uf (uf-1 (⊸r-1 (cmplt f)))))
  ≐〈 ≗sound≐ {_}{[]} (⊸r (uf-iso (⊸r-1 (cmplt f)))) 〉
    sound {_}{[]} (⊸r (⊸r-1 (cmplt f)))
  ≐〈 ≗sound≐ (⊸r-iso (cmplt f)) 〉
    sound (cmplt f)
  ≐〈 soundcmplt f 〉
    f
  qed≐

left-normal₂ : ∀{A}{B} (f : just A ⇒ B) → jY-1 (jY f) ≐ f
left-normal₂ f =
  ≗sound≐ (≡-to-≗ (trans (scut-ax (scut (cmplt f) ax)) (scut-ax (cmplt f))))
  ∙ soundcmplt f

