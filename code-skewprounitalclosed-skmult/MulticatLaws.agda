{-# OPTIONS --rewriting  #-}

open import SkMults

module MulticatLaws where --(M : SkMult) where

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
open import CutsCong

scut-par-ccut-b2 : ∀{S T Γ₁ Γ₂ Δ₀ Δ' X Y Z}
      → (f₁ : T ∣ Γ₁ ⊢b X)(f₂ : S ∣ Γ₂ ⊢ ` Y)(g : just X ∣ Δ₀ ++ Y ∷ Δ' ⊢b Z)
      → scut (base f₁ refl refl) (ccut-b2 Δ₀ f₂ g)
             ≡ ccut-b2 (Γ₁ ++ Δ₀) f₂ (scut-b f₁ g)
scut-par-ccut-b2 f₁ (base x refl refl) g =
  cong (λ x → base x refl refl) {!!}
scut-par-ccut-b2 f₁ (uf f₂) g = scut-par-ccut-b2 f₁ f₂ g
scut-par-ccut-b2 {Γ₁ = Γ₁} {Δ₀ = Δ₀} f₁ (⊸l f₂ f₃) g =
  cong (⊸c (lmap ` Γ₁ ++ lmap ` Δ₀) f₂) (scut-par-ccut-b2 f₁ f₃ g)
scut-par-ccut-b2 {S} {Γ₁ = Γ₁} {Δ₀ = Δ₁} f₁ (⊸c Δ₀ f₂ f₃) g =
  cong (⊸c (lmap ` Γ₁ ++ lmap ` Δ₁ ++ asCxt S Δ₀) f₂) (scut-par-ccut-b2 f₁ f₃ g)

ccut-par-ccut-b2 : ∀{S₁ S₂ T Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ X Y Z}
      → (f₁ : S₁ ∣ Γ₁ ⊢ ` X)(f₂ : S₂ ∣ Γ₂ ⊢ ` Y)(g : T ∣ Δ₀ ++ X ∷ Δ₁ ++ Y ∷ Δ₂ ⊢b Z)
      → ccut (lmap ` Δ₀) f₁ (ccut-b2 (Δ₀ ++ X ∷ Δ₁) f₂ g) refl
             ≗ ccut (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ (ccut-b2 Δ₀ f₁ g) refl
ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (base {T} {Γ = Γ} x₁ refl refl) (base {T₁} {Γ = Γ₁} x refl refl) g
  rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ asCxt T₁ Γ₁ ++ Δ₂) | cases++-lmap-refl ` (Δ₀ ++ asCxt T Γ ++ Δ₁) (Y ∷ Δ₂) =
    ≡-to-≗ (cong (λ x → base x refl refl) {!!})
ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} (uf f₁) (base {T} {Γ = Γ} x refl refl) g with ccut-par-ccut-b2 f₁ (base x refl refl) g
... | ih
  rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ asCxt T Γ ++ Δ₂) = ih
ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (⊸l {Γ₁} {Δ} {A} {B} f₁ f₂) (base {T} {Γ = Γ} x refl refl) g with ccut-par-ccut-b2 f₂ (base x refl refl) g
... | ih
  rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ asCxt T Γ ++ Δ₂) | cases++-inj₁ (lmap ` Δ₀) (Γ₁ ++ Δ ++ lmap ` Δ₁) (` Y ∷ lmap ` Δ₂) (A ⊸ B) | cases++-inj₂ (Δ ++ lmap ` Δ₁) Γ₁ (lmap ` Δ₂) (` Y)
    = ⊸c (lmap ` Δ₀) refl ih  
ccut-par-ccut-b2 {S₁} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {X} {Y} (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₁ f₂) (base {T} {Γ = Γ₁} x refl refl) g with ccut-par-ccut-b2 f₂ (base x refl refl) g
... | ih
  rewrite cases++-lmap-refl ` Δ₁ (X ∷ Δ₂ ++ asCxt T Γ₁ ++ Δ₃) | cases++-inj₁ (lmap ` Δ₁ ++ asCxt S₁ Δ₀) (Γ ++ Δ₄ ++ lmap ` Δ₂) (` Y ∷ lmap ` Δ₃) (A ⊸ B) | cases++-inj₂ (Δ₄ ++ lmap ` Δ₂) Γ (lmap ` Δ₃) (` Y) = ⊸c (lmap ` Δ₁ ++ asCxt S₁ Δ₀) refl ih
ccut-par-ccut-b2 {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁} f₁ (uf f₂) g =
  ccut-par-ccut-b2 f₁ f₂ g
  ∙ ≡-to-≗ (sym (ccut-uf (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ (ccut-b2 Δ₀ f₁ g) refl))
ccut-par-ccut-b2 {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁}{Δ₂}  {X = X} f₁ (⊸l {Γ} {Δ} {A} {B} f₂ f₃) g
  rewrite cases++-inj₂ (` X ∷ lmap ` Δ₁) (lmap ` Δ₀) (Γ ++ Δ ++ lmap ` Δ₂) (A ⊸ B) =
    ⊸c (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) refl (ccut-par-ccut-b2 f₁ f₃ g)
    ∙ ~ ccut⊸l (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ f₃ (ccut-b2 Δ₀ f₁ g) refl
ccut-par-ccut-b2 {S₁} {S₂} {Γ₁ = Γ₁} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {X} f₁ (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₂ f₃) g
  rewrite cases++-inj₂ (` X ∷ lmap ` Δ₂ ++ asCxt S₂ Δ₀) (lmap ` Δ₁) (Γ ++ Δ₄ ++ lmap ` Δ₃) (A ⊸ B) =
    ⊸c (lmap ` Δ₁ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₂ ++ asCxt S₂ Δ₀) refl (ccut-par-ccut-b2 f₁ f₃ g)
    ∙ ~ (ccut⊸c (lmap ` Δ₁ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₂) Δ₀ f₂ f₃ (ccut-b2 Δ₁ f₁ g) refl)

scut-par-ccut : {S T : Stp}{Γ₁ Γ₂ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt}{A₁ A₂ C : Fma}
      → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : S ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
      → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
      → scut f₁ (ccut Δ₀ f₂ g r)
             ≗ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)

ccut-par-ccut : ∀{S₁ S₂ T Γ₁ Γ₂} Δ₀ {Δ Δ₁ Δ₂ A₁ A₂ C}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A₁)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
      → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
      → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl
             ≗ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl

scut-par-pr-ccut : ∀ {S T Γ Γ₁ Γ'} Δ₀ {Δ₁ A A' B C}
    → (f' : S ∣ Γ' ⊢ A') (f : T ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : just A' ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    → scut f' (pr-ccut Δ₀ f g h) ≗ pr-ccut (Γ' ++ Δ₀) f g (scut f' h)
scut-ass-scut : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut f (scut g h) ≗ scut (scut f g) h    
ccut-ass-scut : ∀ {S T Γ Δ} Δ₀ {Δ' Δ'' A B C}
  → (f : S ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''}))
    ≗ scut (ccut Δ₀ f g r) h
ccut-ass-ccut-s : ∀ {S T Γ Δ} Δ₀ {Δ' Γ' A B C}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
  → ccut Δ₀ f (ccut Δ₀ g h r) refl ≗ ccut Δ₀ (scut f g) h r
ccut-ass-ccut : ∀ {S₁ S₂ T Γ Δ} Γ₀ Δ₀ {Δ' Γ' A B C}
  → (f : S₁ ∣ Γ ⊢ A)(g : S₂ ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
  → ccut (Δ₀ ++ asCxt S₂ Γ₀) f (ccut Δ₀ g h r) refl
         ≗ ccut Δ₀ (ccut Γ₀ f g refl) h r

-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (base f₁ refl refl) f₂ (base {just X} {Γ = Γ} g refl eq) refl with cases++-lmap ` Δ₀ (A₂ ∷ Δ') Γ eq
-- scut-par-ccut .(lmap ` Λ₁) {.(lmap ` Λ₂)} {A₂ = .(` Y)} (base {Γ = Γ} f₁ refl refl) f₂ (base {just X} {Γ = .(Λ₁ ++ Y ∷ Λ₂)} g refl refl) refl | Λ₁ , Y ∷ Λ₂ , refl , refl , refl
--   rewrite cases++-lmap-refl ` (Γ ++ Λ₁) (Y ∷ Λ₂) = scut-par-ccut-b2 f₁ f₂ g
-- scut-par-ccut Δ₀ (base f₁ refl refl) f₂ (⊸r g) refl = ⊸r (scut-par-ccut Δ₀ (base f₁ refl refl) f₂ g refl)
-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (base f₁ refl refl) f₂ (⊸c Δ₁ {Γ} {Δ₂} g g₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A₂ ∷ Δ') (sym r)
-- scut-par-ccut .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A₂ = A₂} (base f₁ refl refl) f₂ (⊸c Δ₁ {Γ} {Δ₂} g g₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
-- scut-par-ccut .(Δ₁ ++ A ⊸ B ∷ Γ₀) {.(Δ₀ ++ Δ₂)} {A₂ = A₂} (base {Γ = Γ} f₁ refl refl) f₂ (⊸c Δ₁ {.(Γ₀ ++ A₂ ∷ Δ₀)} {Δ₂} {A} {B} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ (lmap ` Γ ++ Δ₁) Γ₀ (A₂ ∷ Δ₀ ++ Δ₂) (A ⊸ B) | cases++-inj₁ Γ₀ Δ₀ Δ₂ A₂ = refl
-- scut-par-ccut .(Δ₁ ++ A ⊸ B ∷ Γ ++ Δ₀) {Δ'} {A₂ = A₂} (base {Γ = Γ₁} f₁ refl refl) f₂ (⊸c Δ₁ {Γ} {.(Δ₀ ++ A₂ ∷ Δ')} {A} {B} g g₁) refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ (lmap ` Γ₁ ++ Δ₁) (Γ ++ Δ₀) (A₂ ∷ Δ') (A ⊸ B) | cases++-inj₂ Δ₀ Γ Δ' A₂ =
--     ⊸c (lmap ` Γ₁ ++ Δ₁) refl (scut-par-ccut (Δ₁ ++ B ∷ Δ₀) (base f₁ refl refl) f₂ g₁ refl)
-- scut-par-ccut _ {.(Γ ++ Δ₂)} {A₂ = .(A ⊸ B)} (base {Γ = Γ₁} f₁ refl refl) f₂ (⊸c Δ₁ {Γ} {Δ₂} {A} {B} g g₁) refl | inj₂ ([] , refl , refl) 
--   rewrite cases++-inj₂ [] (lmap ` Γ₁ ++ Δ₁) (Γ ++ Δ₂) (A ⊸ B) = scut-par-pr-ccut Δ₁ (base f₁ refl refl) f₂ g g₁
-- scut-par-ccut {S} {Γ₂ = Γ₂} Δ₀ {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Δ₂)} {A₂ = .x} (base {Γ = Γ₁} f₁ refl refl) f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} {A} {B} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) 
--   rewrite cases++-inj₂ ( x ∷ Γ₀) (lmap ` Γ₁ ++ Δ₀) (Γ ++ Δ₂) (A ⊸ B)
--     = ⊸c (lmap ` Γ₁ ++ Δ₀ ++ asCxt S Γ₂ ++ Γ₀) refl (scut-par-ccut Δ₀ (base f₁ refl refl) f₂ g₁ refl)
-- scut-par-ccut Δ₀ (uf f₁) f₂ g refl = uf (scut-par-ccut Δ₀ f₁ f₂ g refl)
-- scut-par-ccut Δ₀ (⊸r f₁) f₂ (base {nothing} x () x₂) r
-- scut-par-ccut Δ₀ (⊸r f₁) f₂ (base {just x₁} x () x₂) r
-- scut-par-ccut Δ₀ (⊸r f₁) f₂ (⊸r g) refl = ⊸r (scut-par-ccut Δ₀ (⊸r f₁) f₂ g refl)
-- scut-par-ccut Δ₀ {Δ'} (⊸r f₁) f₂ (⊸l {Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
-- scut-par-ccut {Γ₁ = Γ₁} Δ₀ {.(Γ₀ ++ Δ)} (⊸r f₁) f₂ (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) =
--   cong-scut1 (~ ccut-ass-ccut Δ₀ Γ₁ f₂ g f₁ refl)
--   ∙ ~ (ccut-ass-scut (Γ₁ ++ Δ₀) f₂ (ccut Γ₁ g f₁ refl) g₁ refl)
-- scut-par-ccut {Γ₁ = Γ₁} .(Γ ++ Γ₀) {Δ'} (⊸r f₁) f₂ (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) =
--   scut-par-ccut Γ₀ (ccut Γ₁ g f₁ refl) f₂ g₁ refl
-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (⊸r f₁) f₂ (⊸c Δ₁ {Γ} {Δ₂} g g₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A₂ ∷ Δ') (sym r)
-- scut-par-ccut .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A₂ = A₂} (⊸r f₁) f₂ (⊸c Δ₁ {Γ} {Δ₂} g g₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
-- scut-par-ccut {Γ₁ = Γ₁} .(Δ₁ ++ A ⊸ B ∷ Γ₀) {.(Γ₀' ++ Δ₂)} {A₂ = A₂} (⊸r f₁) f₂ (⊸c Δ₁ {.(Γ₀ ++ A₂ ∷ Γ₀')} {Δ₂} {A} {B} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Γ₁ ++ Δ₁) Γ₀ (A₂ ∷ Γ₀' ++ Δ₂) (A ⊸ B) | cases++-inj₁ Γ₀ Γ₀' Δ₂ A₂ = refl
-- scut-par-ccut {Γ₁ = Γ₁} .(Δ₁ ++ A ⊸ B ∷ Γ ++ Γ₀') {Δ'} {A₂ = A₂} (⊸r f₁) f₂ (⊸c Δ₁ {Γ} {.(Γ₀' ++ A₂ ∷ Δ')} {A} {B} g g₁) refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Γ₁ ++ Δ₁) (Γ ++ Γ₀') (A₂ ∷ Δ') (A ⊸ B) | cases++-inj₂ Γ₀' Γ Δ' A₂ = ⊸c (Γ₁ ++ Δ₁) refl (scut-par-ccut (Δ₁ ++ B ∷ Γ₀') (⊸r f₁) f₂ g₁ refl)
-- scut-par-ccut {Γ₁ = Γ₁} _ {.(Γ ++ Δ₂)} {A₂ = .(A ⊸ B)} (⊸r f₁) f₂ (⊸c Δ₁ {Γ} {Δ₂} {A} {B} g g₁) refl | inj₂ ([] , refl , refl) 
--   rewrite cases++-inj₂ [] (Γ₁ ++ Δ₁) (Γ ++ Δ₂) (A ⊸ B) = scut-par-pr-ccut Δ₁ (⊸r f₁) f₂ g g₁
-- scut-par-ccut {S} {Γ₁ = Γ₁} {Γ₂} Δ₀ {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Δ₂)} {A₂ = .x} (⊸r f₁) f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} {A} {B} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) 
--   rewrite cases++-inj₂ ( x ∷ Γ₀) (Γ₁ ++ Δ₀) (Γ ++ Δ₂) (A ⊸ B) = ⊸c (Γ₁ ++ Δ₀ ++ asCxt S Γ₂ ++ Γ₀) refl (scut-par-ccut Δ₀ (⊸r f₁) f₂ g₁ refl)
-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (⊸l {Γ} {Δ} f₁ f₃) f₂ g refl
--   rewrite cases++-inj₂ (Δ ++ Δ₀) Γ Δ' A₂ = ⊸l refl (scut-par-ccut Δ₀ f₃ f₂ g refl)
-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (⊸c Δ₁ {Γ} {Δ₂} {A} {B} f₁ f₃) f₂ g refl
--   rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂ ++ Δ₀) (A₂ ∷ Δ') (A ⊸ B) | cases++-inj₂ (Δ₂ ++ Δ₀) Γ Δ' A₂
--     = ⊸c Δ₁ refl (scut-par-ccut Δ₀ f₃ f₂ g refl)

ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (base {Γ = Γ} x refl x₂) refl with cases++-lmap ` (Δ₀ ++ A₁ ∷ Δ₁) (A₂ ∷ Δ₂) Γ x₂
ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {.(lmap ` Λ₂)} {A₁} {.(` x₁)} f₁ f₂ (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl x₂) refl | Λ₁ , x₁ ∷ Λ₂ , p , refl , refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Λ₁ p
ccut-par-ccut .(lmap ` Λ₃) {Δ₁ = .(lmap ` Λ₄)} {.(lmap ` Λ₂)} {.(` x₃)} {.(` x₁)} f₁ f₂ (base {_} {_} {.((Λ₃ ++ x₃ ∷ Λ₄) ++ x₁ ∷ Λ₂)} x refl refl) refl | .(Λ₃ ++ x₃ ∷ Λ₄) , x₁ ∷ Λ₂ , refl , refl , refl | Λ₃ , x₃ ∷ Λ₄ , refl , refl , refl
  rewrite cases++-lmap-refl ` Λ₃ (x₃ ∷ Λ₄ ++ x₁ ∷ Λ₂) = ccut-par-ccut-b2 f₁ f₂ x
ccut-par-ccut Δ₀ f₁ f₂ (uf g) r with cases∷ Δ₀ r
ccut-par-ccut {nothing} .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = scut-par-ccut Δ₁ f₁ f₂ g refl
ccut-par-ccut {just x} .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = uf (scut-par-ccut Δ₁ f₁ f₂ g refl)
ccut-par-ccut .(_ ∷ Γ₀) f₁ f₂ (uf g) refl | inj₂ (Γ₀ , refl , refl) = uf (ccut-par-ccut Γ₀ f₁ f₂ g refl)
ccut-par-ccut Δ₀ f₁ f₂ (⊸r g) refl = ⊸r (ccut-par-ccut Δ₀ f₁ f₂ g refl)
ccut-par-ccut Δ₀ f₁ f₂ (⊸l g g₁) r = {!!}
ccut-par-ccut Δ₀ f₁ f₂ (⊸c Δ₁ g g₁) r = {!!}

scut-par-pr-ccut Δ₀ f' f g h = {!!}

scut-ass-scut f g h = {!!}

ccut-ass-scut Δ₀ f g h r = {!!}

ccut-ass-ccut-s Δ₀ f g h r = {!!}

ccut-ass-ccut Γ₀ Δ₀ f g h r = {!!}


-- {-
-- scut-ax : {S : Stp} {Γ : Cxt} {A : Fma}
--   → (f : S ∣ Γ ⊢ A)
--   → scut f ax ≡ f
-- scut-ax ax = refl
-- scut-ax (uf f) = cong uf (scut-ax f)
-- scut-ax Ir = refl
-- scut-ax (⊸r f) = refl
-- scut-ax (Il f) = cong Il (scut-ax f)
-- scut-ax (⊸l f g) = cong (⊸l f) (scut-ax g)

-- ccut-ax : ∀ {T Δ} Δ₀ {Δ' A C}
--   → (g : T ∣ Δ ⊢ C)
--   → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
--   → ccut Δ₀ (uf ax) g r ≡ subst-cxt r g
-- ccut-ax Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ax Δ₀ (uf g) r with cases∷ Δ₀ r
-- ccut-ax .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
-- ccut-ax .(_ ∷ Γ₀) (uf g) refl | inj₂ (Γ₀ , refl , refl) =
--   cong uf (ccut-ax Γ₀ g refl)
-- ccut-ax Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ax Δ₀ (⊸r g) refl = cong ⊸r (ccut-ax Δ₀ g refl)
-- ccut-ax Δ₀ (Il g) refl = cong Il (ccut-ax Δ₀ g refl)
-- ccut-ax Δ₀ {Δ'} (⊸l {Γ}{Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-ax Δ₀ (⊸l g g₁) refl | inj₁ (Γ₀ , refl , refl) =
--   cong (λ a → ⊸l {Δ₀ ++ _ ∷ Γ₀} a g₁) (ccut-ax Δ₀ g refl)
-- ccut-ax ._ (⊸l g g₁) refl | inj₂ (Γ₀ , refl , refl) =
--   cong (⊸l g) (ccut-ax Γ₀ g₁ refl)             

-- scut-Il-1 : {Γ Δ : Cxt}{A C : Fma}
--   → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
--   → scut (Il-1 f) g ≡ Il-1 (scut f g)
-- ccut-Il-1 : ∀ {Γ Δ} Δ₀ {Δ' A C}
--  → (f : nothing ∣ Γ ⊢ A) (g : just I ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ')
--  → ccut Δ₀ f (Il-1 g) r ≡ Il-1 (ccut Δ₀ f g r)

-- scut-Il-1 ax g = refl
-- scut-Il-1 (⊸r f) ax = refl
-- scut-Il-1 (⊸r f) (⊸r g) = cong ⊸r (scut-Il-1 (⊸r f) g)
-- scut-Il-1 {Γ} (⊸r f) (⊸l g g') =
--   trans (cong₂ scut (ccut-Il-1 Γ g f refl) refl)
--     (scut-Il-1 (ccut Γ g f refl) g')
-- scut-Il-1 (Il f) g = refl

-- ccut-Il-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-Il-1 Δ₀ f (⊸r g) refl = cong ⊸r (ccut-Il-1 Δ₀ f g refl)
-- ccut-Il-1 Δ₀ f (Il g) r = refl

-- scut-ccut-par : ∀ {T Γ₁ Γ₂ Δ} Δ₀ {Δ' A₁ A₂ C}
--   → (f₁ : T ∣ Γ₁ ⊢ A₁) (f₂ : nothing ∣ Γ₂ ⊢ A₂) (g : just A₁ ∣ Δ ⊢ C)
--   → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
--   → scut f₁ (ccut Δ₀ f₂ g r)
--          ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
-- ccut-ccut-par : ∀ {T Γ₁ Γ₂} Δ₀ {Δ Δ₁ Δ₂ A₁ A₂ C}
--   → (f₁ : nothing ∣ Γ₁ ⊢ A₁) (f₂ : nothing ∣ Γ₂ ⊢ A₂) (g : T ∣ Δ ⊢ C)
--   → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
--   → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl
--          ≡ ccut (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl   
-- scut-scut-ass : ∀ {S Γ Δ Λ A B C}
--   → (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ B) (h : just B ∣ Λ ⊢ C)
--   → scut (scut f g) h ≡ scut f (scut g h)
-- ccut-scut-ass : ∀ {T Γ Δ} Δ₀ {Δ' Δ'' A B C}
--   → (f : nothing ∣ Γ ⊢ A) (g : T ∣ Δ ⊢ B) (h : just B ∣ Δ'' ⊢ C)
--   → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
--   → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''}))
--          ≡ scut (ccut Δ₀ f g r) h    
-- ccut-ccut-ass : ∀ {T Γ Δ} Γ₀ Δ₀ {Δ' Γ' A B C}
--   → (f : nothing ∣ Γ ⊢ A) (g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢ B) (h : T ∣ Δ ⊢ C)
--   → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
--   → ccut (Δ₀ ++ Γ₀) f (ccut Δ₀ g h r) refl
--          ≡ ccut Δ₀ (ccut Γ₀ f g refl) h r

-- scut-ccut-par Δ₀ ax f₂ g refl = refl
-- scut-ccut-par Δ₀ (uf f₁) f₂ g refl = cong uf (scut-ccut-par Δ₀ f₁ f₂ g refl)
-- scut-ccut-par Δ₀ Ir f₂ g refl = sym (ccut-Il-1 Δ₀ f₂ g refl)
-- scut-ccut-par Δ₀ (⊸r f₁) f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- scut-ccut-par Δ₀ (⊸r f₁) f₂ (⊸r g) refl = cong ⊸r (scut-ccut-par Δ₀ (⊸r f₁) f₂ g refl)
-- scut-ccut-par Δ₀ {Δ'} (⊸r f₁) f₂ (⊸l {Γ}{Δ} g₁ g₂) r with cases++ Δ₀ Γ Δ' Δ r
-- scut-ccut-par {Γ₁ = Γ₁} Δ₀ (⊸r f₁) f₂ (⊸l {Δ = Δ} g₁ g₂) refl | inj₁ (Γ₀ , refl , refl) =
--   begin
--     scut (ccut Γ₁ (ccut Δ₀ f₂ g₁ refl) f₁ refl) g₂
--   ≡⟨ sym (ccut-scut-ass Γ₁ (ccut Δ₀ f₂ g₁ refl) f₁ g₂ refl) ⟩
--     ccut Γ₁ (ccut Δ₀ f₂ g₁ refl) (scut f₁ g₂) refl
--   ≡⟨ sym (ccut-ccut-ass Δ₀ Γ₁ f₂ g₁ (scut f₁ g₂) refl) ⟩
--     ccut (Γ₁ ++ Δ₀) f₂ (ccut Γ₁ g₁ (scut f₁ g₂) refl) refl
--   ≡⟨ cong (λ a → ccut (Γ₁ ++ Δ₀) f₂ a refl) (ccut-scut-ass Γ₁ g₁ f₁ g₂ refl) ⟩
--     ccut (Γ₁ ++ Δ₀) f₂ (scut (ccut Γ₁ g₁ f₁ refl) g₂) refl
--   ∎
-- scut-ccut-par {Γ₁ = Γ₁} ._ (⊸r f₁) f₂ (⊸l g₁ g₂) refl | inj₂ (Γ₀ , refl , refl) =
--   scut-ccut-par Γ₀ (ccut Γ₁ g₁ f₁ refl) f₂ g₂ refl
-- scut-ccut-par Δ₀ (Il f₁) f₂ g r = cong Il (scut-ccut-par Δ₀ f₁ f₂ g r)
-- scut-ccut-par Δ₀ {Δ'} {A₂ = A₂} (⊸l {Γ}{Δ} f₁ f₁') f₂ g refl
--   rewrite cases++-inj₂ (Δ ++ Δ₀) Γ Δ' A₂ =
--     cong (⊸l f₁) (scut-ccut-par Δ₀ f₁' f₂ g refl)


-- ccut-ccut-par Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ccut-par Δ₀ f₁ f₂ (uf g) r with cases∷ Δ₀ r
-- ccut-ccut-par .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = scut-ccut-par Δ₁ f₁ f₂ g refl
-- ccut-ccut-par ._ f₁ f₂ (uf g) refl | inj₂ (Γ₀ , refl , refl) = cong uf (ccut-ccut-par Γ₀ f₁ f₂ g refl)
-- ccut-ccut-par Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ccut-par Δ₀ f₁ f₂ (⊸r g) refl = cong ⊸r (ccut-ccut-par Δ₀ f₁ f₂ g refl)
-- ccut-ccut-par Δ₀ f₁ f₂ (Il g) r = cong Il (ccut-ccut-par Δ₀ f₁ f₂ g r)
-- ccut-ccut-par Δ₀ {Δ₁ = Δ₁}{Δ₂} f₁ f₂ (⊸l {Γ}{Δ} g g') r with cases++ Δ₀ Γ (Δ₁ ++ _ ∷ Δ₂) Δ r
-- ccut-ccut-par Δ₀ {Δ₁ = Δ₁} {Δ₂} f₁ f₂ (⊸l {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , q) with cases++ Δ₁ Γ₀ Δ₂ Δ (sym q)
-- ccut-ccut-par {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} {A₂} f₁ f₂ (⊸l {Δ = Δ} g g') refl | inj₁ (._ , refl , refl) | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ (Δ₀ ++ A₁ ∷ Δ₁) Γ₀ Δ A₂ | cases++-inj₁ (Δ₀ ++ Γ₁ ++ Δ₁) Γ₀ Δ A₂ | cases++-inj₁ Δ₀ (Δ₁ ++ Γ₂ ++ Γ₀) Δ A₁ =
--     cong (λ a → ⊸l {Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀} a g') (ccut-ccut-par Δ₀ f₁ f₂ g refl) 
-- ccut-ccut-par {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₂ = Δ₂} {A₁} {A₂} f₁ f₂ (⊸l g g') refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₂ Γ₀' (Δ₀ ++ A₁ ∷ Γ₀) Δ₂ A₂ | cases++-inj₂ Γ₀' (Δ₀ ++ Γ₁ ++ Γ₀) Δ₂ A₂ | cases++-inj₁ Δ₀ Γ₀ (Γ₀' ++ Γ₂ ++ Δ₂) A₁ = refl
-- ccut-ccut-par {Γ₁ = Γ₁} {Γ₂} ._ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊸l {Γ} g g') refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (Γ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ A₂ | cases++-inj₂ (Γ₀ ++ Γ₁ ++ Δ₁) Γ Δ₂ A₂ | cases++-inj₂ Γ₀ Γ (Δ₁ ++ Γ₂ ++ Δ₂) A₁ =
--     cong (⊸l {Γ} g) (ccut-ccut-par Γ₀ f₁ f₂ g' refl)

-- scut-scut-ass ax g h = refl
-- scut-scut-ass (uf f) g h = cong uf (scut-scut-ass f g h)
-- scut-scut-ass Ir g h = scut-Il-1 g h
-- scut-scut-ass (⊸r f) ax h = refl
-- scut-scut-ass (⊸r f) (⊸r g) ax = refl
-- scut-scut-ass (⊸r f) (⊸r g) (⊸r h) = cong ⊸r (scut-scut-ass (⊸r f) (⊸r g) h)
-- scut-scut-ass {Γ = Γ} {Δ = Δ} (⊸r f) (⊸r g) (⊸l h h') =
--   begin
--     scut (ccut (Γ ++ Δ) h (scut (⊸r f) g) refl) h'
--   ≡⟨ sym (ccut-scut-ass (Γ ++ Δ) h (scut (⊸r f) g) h' refl) ⟩
--     ccut (Γ ++ Δ) h (scut (scut (⊸r f) g) h') refl
--   ≡⟨ cong (λ a → ccut (Γ ++ Δ) h a refl) (scut-scut-ass (⊸r f) g h') ⟩
--     ccut (Γ ++ Δ) h (scut (⊸r f) (scut g h')) refl
--   ≡⟨ sym (scut-ccut-par Δ (⊸r f) h (scut g h') refl) ⟩
--     scut (⊸r f) (ccut Δ h (scut g h') refl)
--   ≡⟨ cong (scut (⊸r f)) (ccut-scut-ass Δ h g h' refl) ⟩
--     scut (⊸r f) (scut (ccut Δ h g refl) h')
--   ∎
-- scut-scut-ass {Γ = Γ} (⊸r f) (⊸l g g') h = scut-scut-ass (ccut Γ g f refl) g' h
-- scut-scut-ass (Il f) g h = cong Il (scut-scut-ass f g h)
-- scut-scut-ass (⊸l f f') g h = cong (⊸l f) (scut-scut-ass f' g h)  

-- ccut-scut-ass Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-scut-ass Δ₀ f (uf g) h r with cases∷ Δ₀ r
-- ccut-scut-ass .[] f (uf g) h refl | inj₁ (refl , refl , refl) =
--   sym (scut-scut-ass f g h)
-- ccut-scut-ass .(_ ∷ Γ₀) f (uf g) h refl | inj₂ (Γ₀ , refl , refl) =
--   cong uf (ccut-scut-ass Γ₀ f g h refl)
-- ccut-scut-ass Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-scut-ass Δ₀ f (⊸r g) ax refl = refl
-- ccut-scut-ass Δ₀ {Δ'} {A = A} f (⊸r g) (⊸r h) refl =
--   cong ⊸r (ccut-scut-ass Δ₀ f (⊸r {Γ = Δ₀ ++ A ∷ Δ'} g) h refl)
-- ccut-scut-ass {Γ = Γ} Δ₀ {Δ'} {A = A} f (⊸r g) (⊸l h h') refl =
--   begin
--     ccut Δ₀ f (scut (ccut (Δ₀ ++ A ∷ Δ') h g refl) h') refl
--   ≡⟨ ccut-scut-ass Δ₀ f (ccut (Δ₀ ++ A ∷ Δ') h g refl) h' refl ⟩ 
--     scut (ccut Δ₀ f (ccut (Δ₀ ++ A ∷ Δ') h g refl) refl) h'
--   ≡⟨ cong₂ scut (ccut-ccut-par Δ₀ f h g refl) refl ⟩
--     scut (ccut (Δ₀ ++ Γ ++ Δ') h (ccut Δ₀ f g refl) refl) h'
--   ∎ 
-- ccut-scut-ass Δ₀ f (Il g) h refl = cong Il (ccut-scut-ass Δ₀ f g h refl)
-- ccut-scut-ass Δ₀ {Δ'} f (⊸l {Γ}{Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-scut-ass Δ₀ {._}{Δ'} {A = A} f (⊸l {Δ = Δ} g g') h refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ Δ') A = refl
-- ccut-scut-ass ._ {Δ'}{Δ''} {A} f (⊸l {Γ} g g') h refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ Γ₀ Γ (Δ' ++ Δ'') A =
--     cong (⊸l g) (ccut-scut-ass Γ₀ f g' h refl)

-- ccut-ccut-ass Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ccut-ass Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
-- ccut-ccut-ass Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccut-scut-ass Γ₀ f g h refl
-- ccut-ccut-ass Γ₀ .(_ ∷ Δ₀) f g (uf h) r | inj₂ (Δ₀ , refl , refl) = cong uf (ccut-ccut-ass Γ₀ Δ₀ f g h refl )
-- ccut-ccut-ass Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut-ccut-ass Γ₀ Δ₀ f g (⊸r h) refl = cong ⊸r (ccut-ccut-ass Γ₀ Δ₀ f g h refl)
-- ccut-ccut-ass Γ₀ Δ₀ f g (Il h) r = cong Il (ccut-ccut-ass Γ₀ Δ₀ f g h r)
-- ccut-ccut-ass Γ₀ Δ₀ {Δ'} f g (⊸l {Γ}{Δ} h h') r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-ccut-ass {Γ = Γ} Γ₀ Δ₀ {Γ' = Γ'}{A} f g (⊸l {Δ = Δ} h h') refl | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Δ₀ ++ Γ₀) (Γ' ++ Γ₀') Δ A =
--     cong (λ a → ⊸l {Δ₀ ++ Γ₀ ++ Γ ++ Γ' ++ Γ₀'} a h') (ccut-ccut-ass Γ₀ Δ₀ f g h refl) 
-- ccut-ccut-ass Γ₀ ._ {Δ'}{Γ'}{A} f g (⊸l {Γ} h h') r | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₂ (Γ₀' ++ Γ₀) Γ (Γ' ++ Δ') A =
--     cong (⊸l h) (ccut-ccut-ass Γ₀ Γ₀' f g h' refl)


-- -- ====================================================================

-- -- Interaction between scut and ⊸r

-- scut⊸ruf : {Γ Δ : Cxt} → {A B C D : Fma}
--   → (f : just A ∣ Γ ++ B ∷ [] ⊢ C) (g : just (B ⊸ C) ∣ Δ ⊢ D)
--   → scut (⊸r (uf f)) g ≗ uf (scut (⊸r f) g)
-- scut⊸ruf f ax = ⊸ruf
-- scut⊸ruf {Γ}{Δ} f (⊸r g) =
--   proof≗
--     ⊸r (scut (⊸r (uf f)) g)
--   ≗〈 ⊸r (scut⊸ruf f g) 〉
--     ⊸r {Γ = _ ∷ Γ ++ Δ} (uf (scut (⊸r f) g))
--   ≗〈 ⊸ruf 〉
--     uf (⊸r {Γ = Γ ++ Δ} (scut (⊸r f) g))
--   qed≗
-- scut⊸ruf f (⊸l g g₁) = refl

-- scut⊸rIl : {Γ Δ : Cxt} → {B C D : Fma}
--   → (f : nothing ∣ Γ ++ B ∷ [] ⊢ C) (g : just (B ⊸ C) ∣ Δ ⊢ D)
--   → scut (⊸r (Il f)) g ≗ Il (scut (⊸r f) g)
-- scut⊸rIl f ax = ⊸rIl
-- scut⊸rIl {Γ}{Δ} f (⊸r g) = 
--   proof≗
--     scut (⊸r (Il f)) (⊸r g)
--   ≗〈 ⊸r (scut⊸rIl f g) 〉
--     ⊸r {Γ = Γ ++ Δ} (Il (scut (⊸r f) g))
--   ≗〈 ⊸rIl 〉
--     Il (⊸r {Γ = Γ ++ Δ} (scut (⊸r f) g))
--   qed≗
-- scut⊸rIl f (⊸l g g₁) = refl

-- scut⊸r⊸l : {Γ Δ Λ : Cxt} → {A B C D E : Fma}
--   → (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Δ ++ C ∷ [] ⊢ D) (h : just (C ⊸ D) ∣ Λ ⊢ E)
--   → scut (⊸r {Γ = Γ ++ Δ} (⊸l f g)) h ≗ ⊸l f (scut (⊸r g) h)
-- scut⊸r⊸l f g ax = ⊸r⊸l
-- scut⊸r⊸l {Γ}{Δ}{Λ} f g (⊸r h) =
--   proof≗
--     ⊸r {Γ = Γ ++ Δ ++ Λ} (scut (⊸r {Γ = Γ ++ Δ} (⊸l f g)) h) 
--   ≗〈 ⊸r (scut⊸r⊸l f g h) 〉
--     ⊸r {Γ = Γ ++ Δ ++ Λ} (⊸l f (scut (⊸r g) h))
--   ≗〈 ⊸r⊸l {Γ = Γ}{Δ ++ Λ} 〉
--     ⊸l f (scut (⊸r g) (⊸r h))
--   qed≗
-- scut⊸r⊸l {Γ}{Δ}{C = C} f g (⊸l h h')
--   rewrite cases++-inj₂ Δ Γ [] C = refl

-- scutax⊸ :  {Γ : Cxt} {A B C : Fma}
--   → (f : just (A ⊸ B) ∣ Γ ⊢ C)
--   → f ≗ scut (⊸r (⊸l (uf ax) ax)) f
-- scutax⊸ ax = ax⊸
-- scutax⊸ (⊸r f) = ⊸r (scutax⊸ f)
-- scutax⊸ (⊸l f g) = ⊸l (~ (≡-to-≗ (scut-ax f))) refl

-- scut⊸r : ∀ {S Γ Δ A B C}
--   → (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ++ B ∷ [] ⊢ C)
--   → scut f (⊸r g) ≗ ⊸r (scut f g)
-- scut⊸r ax g = refl
-- scut⊸r (uf f) g =
--   proof≗
--     uf (scut f (⊸r g))
--   ≗〈 uf (scut⊸r f g) 〉
--     uf (⊸r _)
--   ≗〈 ~ ⊸ruf 〉
--     ⊸r (uf (scut f g))
--   qed≗
-- scut⊸r Ir g = refl
-- scut⊸r (⊸r f) g = refl
-- scut⊸r (Il f) g =
--   proof≗
--     Il (scut f (⊸r g))
--   ≗〈 Il (scut⊸r f g) 〉
--     Il (⊸r _)
--   ≗〈 ~ ⊸rIl 〉
--     ⊸r (Il _)
--   qed≗
-- scut⊸r (⊸l f f₁) g = 
--   proof≗
--     ⊸l f (scut f₁ (⊸r g))
--   ≗〈 ⊸l refl (scut⊸r f₁ g) 〉
--     ⊸l f (⊸r _)
--   ≗〈 ~ ⊸r⊸l 〉
--     ⊸r _
--   qed≗


-- -- ====================================================================

-- --  Cut rules preserve equivalence of derivations

-- scut≗ : ∀ {S Γ Δ' A C}
--   → {f g : S ∣ Γ ⊢ A} → f ≗ g → (h : just A ∣ Δ' ⊢ C)
--   → scut f h ≗ scut g h
-- scut≗2 : ∀ {S Γ Δ' A C}
--   → (h : S ∣ Γ ⊢ A) {f g : just A ∣ Δ' ⊢ C} → f ≗ g
--   → scut h f ≗ scut h g
-- ccut≗ : ∀ {T Γ Δ} Δ₀ {Δ' A C}
--   → {f f' : nothing ∣ Γ ⊢ A} → f ≗ f' → (g : T ∣ Δ ⊢ C)
--   → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
--   → ccut Δ₀ f g r ≗ ccut Δ₀ f' g r
-- ccut≗2 : ∀ {T Γ Δ} Δ₀ {Δ' A C}
--   → (f : nothing ∣ Γ ⊢ A) {g g' : T ∣ Δ ⊢ C} → g ≗ g'
--   → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
--   → ccut Δ₀ f g r ≗ ccut Δ₀ f g' r

-- scut≗ refl h = refl
-- scut≗ (~ p) h = ~ (scut≗ p h)
-- scut≗ (p ∙ p₁) h = (scut≗ p h) ∙ (scut≗ p₁ h)
-- scut≗ (uf p) h = uf (scut≗ p h)
-- scut≗ (⊸r p) ax = ⊸r p
-- scut≗ (⊸r p) (⊸r h) = ⊸r (scut≗ (⊸r p) h)
-- scut≗ {Γ = Γ} (⊸r p) (⊸l h h') = scut≗ (ccut≗2 Γ h p refl) h'
-- scut≗ (Il p) h = Il (scut≗ p h)
-- scut≗ (⊸l p q) h = ⊸l p (scut≗ q h)
-- scut≗ axI h = ~ (Il-iso h)
-- scut≗ ax⊸ h = scutax⊸ h
-- scut≗ ⊸ruf h = scut⊸ruf _ h
-- scut≗ ⊸rIl h = scut⊸rIl _ h
-- scut≗ ⊸r⊸l h = scut⊸r⊸l _ _ h

-- scut≗2 ax p = p
-- scut≗2 (uf h) p = uf (scut≗2 h p)
-- scut≗2 Ir p = congIl-1 p
-- scut≗2 (⊸r h) refl = refl
-- scut≗2 (⊸r h) (~ p) = ~ (scut≗2 (⊸r h) p)
-- scut≗2 (⊸r h) (p ∙ p₁) = (scut≗2 (⊸r h) p) ∙ (scut≗2 (⊸r h) p₁)
-- scut≗2 (⊸r h) (⊸r p) = ⊸r (scut≗2 (⊸r h) p)
-- scut≗2 {Γ = Γ} (⊸r h) (⊸l {f = f}{g}{f'}{g'} p q) =
--   scut≗ (ccut≗ Γ p h refl) f'
--   ∙ scut≗2 (ccut Γ g h refl) q
-- scut≗2 {Γ = Γ} (⊸r h) ax⊸ = ≡-to-≗ 
--   (begin
--     ⊸r h
--    ≡⟨ cong ⊸r (sym (scut-ax h)) ⟩
--     ⊸r (scut h ax)
--    ≡⟨ cong ⊸r (cong (λ a → scut a ax) (sym (ccut-ax Γ h refl))) ⟩
--     ⊸r (scut (ccut Γ (uf ax) h refl) ax)
--    ∎)
-- scut≗2 {Γ = Γ} (⊸r h) (⊸r⊸l {f = f} {g}) = ~ (scut⊸r (ccut Γ f h refl) g)
-- scut≗2 (Il h) p = Il (scut≗2 h p)
-- scut≗2 (⊸l h h') p = ⊸l refl (scut≗2 h' p)

-- ccut≗ Δ₀ p ax r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut≗ Δ₀ p (uf g) r with cases∷ Δ₀ r
-- ccut≗ .[] p (uf g) r | inj₁ (refl , refl , refl) = scut≗ p g
-- ccut≗ .(_ ∷ Γ₀) p (uf g) r | inj₂ (Γ₀ , refl , refl) = uf (ccut≗ Γ₀ p g refl)
-- ccut≗ Δ₀ p Ir r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut≗ Δ₀ p (⊸r g) refl = ⊸r (ccut≗ Δ₀ p g refl)
-- ccut≗ Δ₀ p (Il g) refl = Il (ccut≗ Δ₀ p g refl)
-- ccut≗ Δ₀ {Δ'} p (⊸l {Γ}{Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut≗ Δ₀ p (⊸l g g₁) r | inj₁ (Γ₀ , refl , refl) = ⊸l (ccut≗ Δ₀ p g refl) refl
-- ccut≗ ._ p (⊸l g g₁) r | inj₂ (Γ₀ , refl , refl) = ⊸l refl (ccut≗ Γ₀ p g₁ refl)

-- ccut≗2 Δ₀ f refl r = refl
-- ccut≗2 Δ₀ f (~ p) r = ~ (ccut≗2 Δ₀ f p r)
-- ccut≗2 Δ₀ f (p ∙ p₁) r = (ccut≗2 Δ₀ f p r) ∙ (ccut≗2 Δ₀ f p₁ r)
-- ccut≗2 Δ₀ f (uf p) r with cases∷ Δ₀ r
-- ccut≗2 .[] f (uf p) r | inj₁ (refl , refl , refl) = scut≗2 f p
-- ccut≗2 .(_ ∷ Γ₀) f (uf p) r | inj₂ (Γ₀ , refl , refl) = uf (ccut≗2 Γ₀ f p refl)
-- ccut≗2 Δ₀ f (⊸r p) refl = ⊸r (ccut≗2 Δ₀ f p refl)
-- ccut≗2 Δ₀ f (Il p) refl = Il (ccut≗2 Δ₀ f p refl)
-- ccut≗2 Δ₀ {Δ'} f (⊸l {Γ}{Δ} p p₁) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut≗2 Δ₀ f (⊸l p p₁) r | inj₁ (Γ₀ , refl , refl) = ⊸l (ccut≗2 Δ₀ f p refl) p₁
-- ccut≗2 ._ f (⊸l p p₁) r | inj₂ (Γ₀ , refl , refl) = ⊸l p (ccut≗2 Γ₀ f p₁ refl)
-- ccut≗2 Δ₀ f axI r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut≗2 Δ₀ f ax⊸ r = ⊥-elim ([]disj∷ Δ₀ r)
-- ccut≗2 Δ₀ f ⊸ruf r with cases∷ Δ₀ r
-- ccut≗2 .[] f (⊸ruf {f = f₁}) refl | inj₁ (refl , refl , refl) = ~ (scut⊸r f f₁)
-- ccut≗2 _ f ⊸ruf refl | inj₂ (Γ₀ , refl , refl) = ⊸ruf
-- ccut≗2 Δ₀ f ⊸rIl refl = ⊸rIl
-- ccut≗2 Δ₀ {Δ'} f (⊸r⊸l {Γ}{Δ}) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut≗2 Δ₀ {._} {A} f (⊸r⊸l {Δ = Δ} {C = C}) refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ C ∷ []) A = ⊸r⊸l
-- ccut≗2 {Γ = Γ₁} ._ {Δ'} {A} f (⊸r⊸l {Γ} {C = C}) refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ Γ₀ Γ (Δ' ++ C ∷ []) A = ⊸r⊸l {Γ} {Γ₀ ++ Γ₁ ++ Δ'}
-- -}
