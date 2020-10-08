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
-- scut-par-ccut-b2 f₁ (base {nothing} x refl refl) g =
--   cong (λ x → base x refl refl) (scut-ccut-par-b _ f₁ x g)
-- scut-par-ccut-b2 f₁ (base {just x₁} x refl refl) g = 
--   cong (λ x → base x refl refl) (scut-ccut-par-b _ f₁ (uf-b x) g)
-- scut-par-ccut-b2 f₁ (uf f₂) g = scut-par-ccut-b2 f₁ f₂ g
-- scut-par-ccut-b2 {Γ₁ = Γ₁} {Δ₀ = Δ₀} f₁ (⊸l f₂ f₃) g =
--   cong (⊸c (lmap ` Γ₁ ++ lmap ` Δ₀) f₂) (scut-par-ccut-b2 f₁ f₃ g)
-- scut-par-ccut-b2 {S} {Γ₁ = Γ₁} {Δ₀ = Δ₁} f₁ (⊸c Δ₀ f₂ f₃) g =
--   cong (⊸c (lmap ` Γ₁ ++ lmap ` Δ₁ ++ asCxt S Δ₀) f₂) (scut-par-ccut-b2 f₁ f₃ g)

ccut-par-ccut-b2 : ∀{S₁ S₂ T Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ X Y Z}
      → (f₁ : S₁ ∣ Γ₁ ⊢ ` X)(f₂ : S₂ ∣ Γ₂ ⊢ ` Y)(g : T ∣ Δ₀ ++ X ∷ Δ₁ ++ Y ∷ Δ₂ ⊢b Z)
      → ccut (lmap ` Δ₀) f₁ (ccut-b2 (Δ₀ ++ X ∷ Δ₁) f₂ g) refl
             ≗ ccut (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ (ccut-b2 Δ₀ f₁ g) refl
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (base {nothing} {Γ = Γ} x₁ refl refl) (base {nothing} {Γ = Γ₁} x refl refl) g 
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ Γ₁ ++ Δ₂) | cases++-lmap-refl ` (Δ₀ ++ Γ ++ Δ₁) (Y ∷ Δ₂) =
--     ≡-to-≗ (cong (λ x → base x refl refl) (ccut-ccut-par-b Δ₀ x₁ x g))
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (base {nothing} {Γ = Γ} x₁ refl refl) (base {just x₂} {Γ = Γ₁} x refl refl) g 
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ x₂ ∷ Γ₁ ++ Δ₂) | cases++-lmap-refl ` (Δ₀ ++ Γ ++ Δ₁) (Y ∷ Δ₂) =
--     ≡-to-≗ (cong (λ x → base x refl refl) (ccut-ccut-par-b Δ₀ x₁ (uf-b x) g))
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (base {just x₂} {Γ = Γ} x₁ refl refl) (base {nothing} {Γ = Γ₁} x refl refl) g 
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ Γ₁ ++ Δ₂) | cases++-lmap-refl ` (Δ₀ ++ x₂ ∷ Γ ++ Δ₁) (Y ∷ Δ₂) =
--     ≡-to-≗ (cong (λ x → base x refl refl) (ccut-ccut-par-b Δ₀ (uf-b x₁) x g))
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (base {just x₂} {Γ = Γ} x₁ refl refl) (base {just x₃} {Γ = Γ₁} x refl refl) g 
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ x₃ ∷ Γ₁ ++ Δ₂) | cases++-lmap-refl ` (Δ₀ ++ x₂ ∷ Γ ++ Δ₁) (Y ∷ Δ₂) =
--     ≡-to-≗ (cong (λ x → base x refl refl) (ccut-ccut-par-b Δ₀ (uf-b x₁) (uf-b x) g))
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} (uf f₁) (base {T} {Γ = Γ} x refl refl) g with ccut-par-ccut-b2 f₁ (base x refl refl) g
-- ... | ih
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ asCxt T Γ ++ Δ₂) = ih
-- ccut-par-ccut-b2 {Δ₀ = Δ₀} {Δ₁} {Δ₂} {X} {Y} (⊸l {Γ₁} {Δ} {A} {B} f₁ f₂) (base {T} {Γ = Γ} x refl refl) g with ccut-par-ccut-b2 f₂ (base x refl refl) g
-- ... | ih
--   rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁ ++ asCxt T Γ ++ Δ₂) | cases++-inj₁ (lmap ` Δ₀) (Γ₁ ++ Δ ++ lmap ` Δ₁) (` Y ∷ lmap ` Δ₂) (A ⊸ B) | cases++-inj₂ (Δ ++ lmap ` Δ₁) Γ₁ (lmap ` Δ₂) (` Y)
--     = ⊸c (lmap ` Δ₀) refl ih  
-- ccut-par-ccut-b2 {S₁} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {X} {Y} (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₁ f₂) (base {T} {Γ = Γ₁} x refl refl) g with ccut-par-ccut-b2 f₂ (base x refl refl) g
-- ... | ih
--   rewrite cases++-lmap-refl ` Δ₁ (X ∷ Δ₂ ++ asCxt T Γ₁ ++ Δ₃) | cases++-inj₁ (lmap ` Δ₁ ++ asCxt S₁ Δ₀) (Γ ++ Δ₄ ++ lmap ` Δ₂) (` Y ∷ lmap ` Δ₃) (A ⊸ B) | cases++-inj₂ (Δ₄ ++ lmap ` Δ₂) Γ (lmap ` Δ₃) (` Y) = ⊸c (lmap ` Δ₁ ++ asCxt S₁ Δ₀) refl ih
-- ccut-par-ccut-b2 {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁} f₁ (uf f₂) g =
--   ccut-par-ccut-b2 f₁ f₂ g
--   ∙ ≡-to-≗ (sym (ccut-uf (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ (ccut-b2 Δ₀ f₁ g) refl))
-- ccut-par-ccut-b2 {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁}{Δ₂}  {X = X} f₁ (⊸l {Γ} {Δ} {A} {B} f₂ f₃) g
--   rewrite cases++-inj₂ (` X ∷ lmap ` Δ₁) (lmap ` Δ₀) (Γ ++ Δ ++ lmap ` Δ₂) (A ⊸ B) =
--     ⊸c (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) refl (ccut-par-ccut-b2 f₁ f₃ g)
--     ∙ ~ ccut⊸l (lmap ` Δ₀ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₁) f₂ f₃ (ccut-b2 Δ₀ f₁ g) refl
-- ccut-par-ccut-b2 {S₁} {S₂} {Γ₁ = Γ₁} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {X} f₁ (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₂ f₃) g
--   rewrite cases++-inj₂ (` X ∷ lmap ` Δ₂ ++ asCxt S₂ Δ₀) (lmap ` Δ₁) (Γ ++ Δ₄ ++ lmap ` Δ₃) (A ⊸ B) =
--     ⊸c (lmap ` Δ₁ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₂ ++ asCxt S₂ Δ₀) refl (ccut-par-ccut-b2 f₁ f₃ g)
--     ∙ ~ (ccut⊸c (lmap ` Δ₁ ++ asCxt S₁ Γ₁ ++ lmap ` Δ₂) Δ₀ f₂ f₃ (ccut-b2 Δ₁ f₁ g) refl)

ccut-b2-ass-scut : ∀ {S T Γ Δ₀ Δ₁ Λ X Y Z}
  → (f : S ∣ Γ ⊢ ` X)(g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)(h : just Y ∣ Λ ⊢b Z)
  → ccut-b2 Δ₀ f (scut-b g h) ≗ scut (ccut-b2 Δ₀ f g) (base h refl refl)
-- ccut-b2-ass-scut (base {nothing} x refl refl) g h =
--   ≡-to-≗ (cong (λ x → base x refl refl) (ccut-scut-ass-b _  x g h))
-- ccut-b2-ass-scut (base {just x₁} x refl refl) g h =
--   ≡-to-≗ (cong (λ x → base x refl refl) (ccut-scut-ass-b _  (uf-b x) g h))
-- ccut-b2-ass-scut (uf f) g h = ccut-b2-ass-scut f g h 
-- ccut-b2-ass-scut {Δ₀ = Δ₀} (⊸l f f₁) g h = ⊸c (lmap ` Δ₀) refl (ccut-b2-ass-scut f₁ g h)
-- ccut-b2-ass-scut {S} {Δ₀ = Δ₁} (⊸c Δ₀ f f₁) g h = ⊸c (lmap ` Δ₁ ++ asCxt S Δ₀) refl (ccut-b2-ass-scut f₁ g h)

ccut-ass-ccut-b2-s : ∀ {S T Γ Δ₀ Δ₁ Γ' A X Y}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Γ' ⊢ ` X)(h : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
  → ccut (lmap ` Δ₀) f (ccut-b2 Δ₀ g h) refl ≗ ccut-b2 Δ₀ (scut f g) h
-- ccut-ass-ccut-b2-s (base x refl refl) (base {nothing} x₁ () x₃) h
-- ccut-ass-ccut-b2-s {Δ₀ = Δ₀} {Δ₁} (base {nothing} x refl refl) (base {just x₂} {Γ = Γ} x₁ refl refl) h
--   rewrite cases++-lmap-refl ` Δ₀ (x₂ ∷ Γ ++ Δ₁) =
--     ≡-to-≗ (cong (λ x → base x refl refl)
--         (trans (ccut-ccut-ass-b [] Δ₀ x (uf-b x₁) h)
--           (cong (λ x → ccut-b Δ₀ x h) (ccut-uf-b2 x x₁))))
-- ccut-ass-ccut-b2-s {Δ₀ = Δ₀} {Δ₁} (base {just x₃} x refl refl) (base {just x₂} {Γ = Γ} x₁ refl refl) h
--   rewrite cases++-lmap-refl ` Δ₀ (x₂ ∷ Γ ++ Δ₁) =
--     ≡-to-≗ (cong (λ x → base x refl refl)
--         (trans (ccut-ccut-ass-b [] Δ₀ (uf-b x) (uf-b x₁) h)
--           (cong (λ x → ccut-b Δ₀ x h) (trans (ccut-uf-b2 (uf-b x) x₁) (scut-uf-b x x₁)))))
-- ccut-ass-ccut-b2-s {Δ₀ = Δ₁} {Δ₂} (base {T = T}{Γ = Γ₁} {Y = Y} x refl refl) (⊸c Δ₀ {Γ} {Δ₃} {A} {B} g g₁) h
--   rewrite cases++-inj₂ (` Y ∷ Δ₀) (lmap ` Δ₁) (Γ ++ Δ₃ ++ lmap ` Δ₂) (A ⊸ B) =
--     ⊸c (lmap ` Δ₁ ++ lmap ` (asCxt T Γ₁) ++ Δ₀) refl (ccut-ass-ccut-b2-s (base x refl refl) g₁ h)
-- ccut-ass-ccut-b2-s {Δ₀ = Δ₀} (uf f) g h =
--   ≡-to-≗ (ccut-uf (lmap ` Δ₀) f (ccut-b2 Δ₀ g h) refl) ∙ ccut-ass-ccut-b2-s f g h
-- ccut-ass-ccut-b2-s (⊸r f) (base {nothing} x () x₂) h
-- ccut-ass-ccut-b2-s (⊸r f) (base {just x₁} x () x₂) h
-- ccut-ass-ccut-b2-s {Γ = Γ₁} {Δ₀} {Δ₁} (⊸r {A = A} {B} f) (⊸l {Γ} {Δ} g g₁) h 
--   rewrite cases++-inj₂ [] (lmap ` Δ₀) (Γ ++ Δ ++ lmap ` Δ₁) (A ⊸ B) = ccut-ass-ccut-b2-s (ccut Γ₁ g f refl) g₁ h
-- ccut-ass-ccut-b2-s {S} {Γ = Γ₁} {Δ₁} {Δ₂} (⊸r {A = A} {B} f) (⊸c Δ₀ {Γ} {Δ₃} {A₁} {B₁} g g₁) h
--   rewrite cases++-inj₂ (A ⊸ B ∷ Δ₀) (lmap ` Δ₁) (Γ ++ Δ₃ ++ lmap ` Δ₂) (A₁ ⊸ B₁) =
--     ⊸c (lmap ` Δ₁ ++ asCxt S Γ₁ ++ Δ₀) refl (ccut-ass-ccut-b2-s (⊸r f) g₁ h)
-- ccut-ass-ccut-b2-s {Δ₀ = Δ₀} (⊸l f f₁) g h =
--   ccut⊸l (lmap ` Δ₀) f f₁ (ccut-b2 Δ₀ g h) refl
--   ∙ ⊸c (lmap ` Δ₀) refl (ccut-ass-ccut-b2-s f₁ g h)
-- ccut-ass-ccut-b2-s {S} {Δ₀ = Δ₁} (⊸c Δ₀ f f₁) g h =
--   ccut⊸c (lmap ` Δ₁) Δ₀ f f₁ (ccut-b2 Δ₁ g h) refl
--   ∙ ⊸c (lmap ` Δ₁ ++ asCxt S Δ₀) refl (ccut-ass-ccut-b2-s f₁ g h)

ccut-ass-ccut-b2 : ∀ {S₁ S₂ T Γ Δ₀ Δ₁ Δ Λ₀ Λ₁ A X Y}
  → (f : S₁ ∣ Γ ⊢ A)(g : S₂ ∣ Δ ⊢ ` X)(h : T ∣ Λ₀ ++ X ∷ Λ₁ ⊢b Y)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → ccut (lmap ` Λ₀ ++ asCxt S₂ Δ₀) f (ccut-b2 Λ₀ (subst-cxt eq g) h) refl
         ≗ ccut-b2 Λ₀ (ccut Δ₀ f g eq) h
ccut-ass-ccut-b2 f g h = {!!}


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

ccut-par-pr-ccut : ∀{S₁ S₂ T Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ Δ₃ A B A₂ C}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A ⊸ B)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : nothing ∣ Δ₁ ++ A₂ ∷ Δ₂ ⊢ A) (h : T ∣ Δ₀ ++ B ∷ Δ₃ ⊢ C)
      → pr-ccut Δ₀ f₁ (ccut Δ₁ f₂ g refl) h
             ≗ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) f₂ (pr-ccut Δ₀ f₁ g h) refl
ccut-par-pr-ccut2 : ∀{S₁ S₂ T Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ₂ A B A₂ C}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A ⊸ B)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : nothing ∣ Δ ⊢ A) (h : T ∣ Δ₀ ++ B ∷ Δ₁ ++ A₂ ∷ Δ₂ ⊢ C)
      → pr-ccut Δ₀ f₁ g (ccut (Δ₀ ++ B ∷ Δ₁) f₂ h refl)
             ≗ ccut (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ ++ Δ₁) f₂ (pr-ccut Δ₀ f₁ g h) refl
ccut-par-pr-ccut3 : ∀{S₁ S₂ T Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ₂ A B A₂ C}
      → (f₁ : S₁ ∣ Γ₁ ⊢ A ⊸ B)(f₂ : S₂ ∣ Γ₂ ⊢ A₂)(g : nothing ∣ Δ ⊢ A) (h : T ∣ Δ₀ ++ A₂ ∷ Δ₁ ++ B ∷ Δ₂ ⊢ C)
      → ccut Δ₀ f₂ (pr-ccut (Δ₀ ++ A₂ ∷ Δ₁) f₁ g h) refl
             ≗ pr-ccut (Δ₀ ++ asCxt S₂ Γ₂ ++ Δ₁) f₁ g (ccut Δ₀ f₂ h refl)

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
pr-ccut-ass-scut : ∀ {S T Γ Δ Δ₀ Δ₁ Λ A B C D}
  → (f : S ∣ Γ ⊢ A ⊸ B)(g : nothing ∣ Δ ⊢ A)(h : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)(k : just C ∣ Λ ⊢ D)
  → pr-ccut Δ₀ f g (scut h k) ≗ scut (pr-ccut Δ₀ f g h) k
pr-ccut-ass-scut2 : ∀ {S T Γ Δ Δ₀ Δ₁ Λ A B C D}
  → (k : S ∣ Λ ⊢ D)(f : just D ∣ Γ ⊢ A ⊸ B)(g : nothing ∣ Δ ⊢ A)(h : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
  → ccut Δ₀ k (pr-ccut Δ₀ f g h) refl ≗ pr-ccut Δ₀ (scut k f) g h
pr-ccut-ass-ccut : ∀ {S₁ S₂ T Γ Γ₀ Γ₁ Γ' Δ Λ₀ Λ₁ A A' B C}
  → (f : S₁ ∣ Γ ⊢ A')(g : S₂ ∣ Γ' ⊢ A ⊸ B)(h : nothing ∣ Δ ⊢ A)(k : T ∣ Λ₀ ++ B ∷ Λ₁ ⊢ C)
  → (r : Γ' ≡ Γ₀ ++ A' ∷ Γ₁) 
  → ccut (Λ₀ ++ asCxt S₂ Γ₀) f (pr-ccut Λ₀ (subst-cxt r g) h k) refl
         ≗ pr-ccut Λ₀ (ccut Γ₀ f g r) h k
-- -- pr-ccut-ass-pr-ccut-s : ∀ {S T Γ Δ} Δ₀ {Δ' Γ' A B C}
-- --   → (f' : S ∣ Γ ⊢ A ⊸ B)(g' : just A ∣ Γ' ⊢ A)
-- --   → (f : just B ∣ Γ₁ ⊢ A' ⊸ B')(g : nothing ∣ Γ₁' ⊢ A')(h : T ∣ Δ₀ ++ B' ∷ Δ₁ ⊢ C)
-- --   → pr-ccut Δ₀ f' g' (pr-ccut Δ₀ f g h) ≗ pr-ccut Δ₀ (scut f' g) h r


-- scut-par-ccut Δ₀ {Δ'} {A₂ = A₂} (base f₁ refl refl) f₂ (base {just X} {Γ = Γ} g refl eq) refl with cases++-lmap ` Δ₀ (A₂ ∷ Δ') Γ eq
-- scut-par-ccut .(lmap ` Λ₁) {.(lmap ` Λ₂)} {A₂ = .(` Y)} (base {Γ = Γ} f₁ refl refl) f₂ (base {just X} {Γ = .(Λ₁ ++ Y ∷ Λ₂)} g refl refl) refl | Λ₁ , Y ∷ Λ₂ , refl , refl , refl
--   rewrite cases++-lmap-refl ` (Γ ++ Λ₁) (Y ∷ Λ₂) = ≡-to-≗ (scut-par-ccut-b2 f₁ f₂ g)
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
-- 
-- ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (base {Γ = Γ} x refl x₂) refl with cases++-lmap ` (Δ₀ ++ A₁ ∷ Δ₁) (A₂ ∷ Δ₂) Γ x₂
-- ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {.(lmap ` Λ₂)} {A₁} {.(` x₁)} f₁ f₂ (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl x₂) refl | Λ₁ , x₁ ∷ Λ₂ , p , refl , refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Λ₁ p
-- ccut-par-ccut .(lmap ` Λ₃) {Δ₁ = .(lmap ` Λ₄)} {.(lmap ` Λ₂)} {.(` x₃)} {.(` x₁)} f₁ f₂ (base {_} {_} {.((Λ₃ ++ x₃ ∷ Λ₄) ++ x₁ ∷ Λ₂)} x refl refl) refl | .(Λ₃ ++ x₃ ∷ Λ₄) , x₁ ∷ Λ₂ , refl , refl , refl | Λ₃ , x₃ ∷ Λ₄ , refl , refl , refl
--   rewrite cases++-lmap-refl ` Λ₃ (x₃ ∷ Λ₄ ++ x₁ ∷ Λ₂) = ccut-par-ccut-b2 f₁ f₂ x
-- ccut-par-ccut Δ₀ f₁ f₂ (uf g) r with cases∷ Δ₀ r
-- ccut-par-ccut {nothing} .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = scut-par-ccut Δ₁ f₁ f₂ g refl
-- ccut-par-ccut {just x} .[] {Δ₁ = Δ₁} f₁ f₂ (uf g) refl | inj₁ (refl , refl , refl) = uf (scut-par-ccut Δ₁ f₁ f₂ g refl)
-- ccut-par-ccut .(_ ∷ Γ₀) f₁ f₂ (uf g) refl | inj₂ (Γ₀ , refl , refl) = uf (ccut-par-ccut Γ₀ f₁ f₂ g refl)
-- ccut-par-ccut Δ₀ f₁ f₂ (⊸r g) refl = ⊸r (ccut-par-ccut Δ₀ f₁ f₂ g refl)
-- ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊸l {Γ} {Δ} g g₁) r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r
-- ccut-par-ccut {S₁}{S₂}{_}{Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀ ++ Δ)} {A₁}{A₂} f₁ f₂ (⊸l {.(Δ₀ ++ A₁ ∷ Δ₁ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₀ (Δ₁ ++ asCxt S₂ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
--     ⊸l (ccut-par-ccut Δ₀ f₁ f₂ g refl) refl
-- ccut-par-ccut Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₂)} g g₁) r | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀' ++ Γ₀)} {Δ₂} {A₁}{A₂} f₁ f₂ (⊸l {.(Δ₀ ++ A₁ ∷ Γ₀')} {.(Γ₀ ++ _ ∷ Δ₂)} g g₁) refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀  (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊸l {Γ} {.((Γ₀' ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)} g g₁) refl | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₂ Γ₀' Γ (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀' Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀' ++ asCxt S₁ Γ₁ ++ Δ₁) Γ Δ₂ A₂
--     = ⊸l refl (ccut-par-ccut Γ₀' f₁ f₂ g₁ refl)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {Γ} {Δ₄} {A} {B} g g₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₄) (A₁ ∷ Δ₂ ++ A₂ ∷ Δ₃) (sym r)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Δ₁ ++ A ⊸ B ∷ Γ₀) {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {Γ} {Δ₄} {A} {B} g g₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ (Δ₂ ++ A₂ ∷ Δ₃) Δ₄ q
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Δ₁ ++ A ⊸ B ∷ Γ₀) {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {.(Γ₀ ++ A₁ ∷ Δ₀)} {Δ₄} {A} {B} g g₁) r | inj₁ (Γ₀ , refl , q) | inj₁ (Δ₀ , refl , p') with cases++ Δ₂ Δ₀ Δ₃ Δ₄ (sym p')
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Δ₁ ++ A ⊸ B ∷ Γ₀) {Δ₁ = Δ₂} {.(Δ₀' ++ Δ₄)} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {.(Γ₀ ++ A₁ ∷ Δ₂ ++ A₂ ∷ Δ₀')} {Δ₄} {A} {B} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (.(Δ₂ ++ A₂ ∷ Δ₀') , refl , refl) | inj₁ (Δ₀' , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ₀ ++ A₁ ∷ Δ₂) (A₂ ∷ Δ₀' ++ Δ₄) (A ⊸ B) | cases++-inj₁ Δ₁ (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ₂) (A₂ ∷ Δ₀' ++ Δ₄) (A ⊸ B)
--         | cases++-inj₁ (Γ₀ ++ A₁ ∷ Δ₂) Δ₀' Δ₄ A₂ | cases++-inj₁ (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ₂) Δ₀' Δ₄ A₂
--         | cases++-inj₁ Δ₁ Γ₀ (A₁ ∷ Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₀' ++ Δ₄) (A ⊸ B) | cases++-inj₁ Γ₀ (Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₀') Δ₄ A₁
--         = ⊸c Δ₁ (ccut-par-ccut Γ₀ f₁ f₂ g refl) refl
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Δ₁ ++ A ⊸ B ∷ Γ₀) {Δ₁ = .(Δ₀ ++ Δ₀')} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {.(Γ₀ ++ A₁ ∷ Δ₀)} {.(Δ₀' ++ A₂ ∷ Δ₃)} {A} {B} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Δ₀ , refl , refl) | inj₂ (Δ₀' , refl , refl) 
--   rewrite cases++-inj₁ Δ₁ (Γ₀ ++ A₁ ∷ Δ₀ ++ Δ₀') (A₂ ∷ Δ₃) (A ⊸ B) | cases++-inj₁ Δ₁ (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ₀ ++ Δ₀') (A₂ ∷ Δ₃) (A ⊸ B)
--         | cases++-inj₂  Δ₀' (Γ₀ ++ A₁ ∷ Δ₀) Δ₃ A₂ | cases++-inj₂  Δ₀' (Γ₀ ++ asCxt S₁ Γ₁ ++ Δ₀) Δ₃ A₂
--         | cases++-inj₁ Δ₁ Γ₀ (A₁ ∷ Δ₀ ++ Δ₀' ++ asCxt S₂ Γ₂ ++ Δ₃) (A ⊸ B) | cases++-inj₁ Γ₀ Δ₀ (Δ₀' ++ asCxt S₂ Γ₂ ++ Δ₃) A₁ = refl
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} .(Δ₁ ++ A ⊸ B ∷ Γ ++ Δ₀) {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c Δ₁ {Γ} {.(Δ₀ ++ A₁ ∷ Δ₂ ++ A₂ ∷ Δ₃)} {A} {B} g g₁) refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₀ ++ A₁ ∷ Δ₂)  (A₂ ∷ Δ₃) (A ⊸ B) | cases++-inj₁ Δ₁ (Γ ++ Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₂)  (A₂ ∷ Δ₃) (A ⊸ B)
--         | cases++-inj₂ (Δ₀ ++ A₁ ∷ Δ₂) Γ Δ₃ A₂ | cases++-inj₂ (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₂) Γ Δ₃ A₂
--         | cases++-inj₁ Δ₁ (Γ ++ Δ₀) (A₁ ∷ Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₃) (A ⊸ B) | cases++-inj₂ Δ₀ Γ (Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₃) A₁
--         = ⊸c Δ₁ refl (ccut-par-ccut (Δ₁ ++ B ∷ Δ₀) f₁ f₂ g₁ refl)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c .Δ₀ {Γ} {Δ₄} {A} {B} g g₁) r | inj₂ ([] , p , refl) with inj∷ p
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {Δ₃} {.(A ⊸ B)} {A₂} f₁ f₂ (⊸c .Δ₀ {Γ} {Δ₄} {A} {B} g g₁) r | inj₂ ([] , p , refl) | refl , p' with cases++ Δ₂ Γ Δ₃ Δ₄ (sym p')
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {.(Δ₀' ++ Δ₄)} {.(A ⊸ B)} {A₂} f₁ f₂ (⊸c .Δ₀ {.(Δ₂ ++ A₂ ∷ Δ₀')} {Δ₄} {A} {B} g g₁) refl | inj₂ ([] , refl , refl) | refl , refl | inj₁ (Δ₀' , refl , refl)
--   rewrite cases++-inj₁ Δ₀ Δ₂ (A₂ ∷ Δ₀' ++ Δ₄) (A ⊸ B) | cases++-inj₁ Δ₂ Δ₀' Δ₄ A₂ | cases++-inj₂ [] Δ₀ (Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₀' ++ Δ₄) (A ⊸ B) = ccut-par-pr-ccut f₁ f₂ g g₁
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ ++ Δ₀')} {Δ₃} {.(A ⊸ B)} {A₂} f₁ f₂ (⊸c .Δ₀ {Γ} {.(Δ₀' ++ A₂ ∷ Δ₃)} {A} {B} g g₁) refl | inj₂ ([] , refl , refl) | refl , refl | inj₂ (Δ₀' , refl , refl)
--   rewrite cases++-inj₁ Δ₀ (Γ ++ Δ₀') (A₂ ∷ Δ₃) (A ⊸ B) | cases++-inj₂ Δ₀' Γ Δ₃ A₂ | cases++-inj₂ [] Δ₀ (Γ ++ Δ₀' ++ asCxt S₂ Γ₂ ++ Δ₃) (A ⊸ B) = ccut-par-pr-ccut2 f₁ f₂ g g₁
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {Δ₃} {A₁} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₄} {A} {B} g g₁) r | inj₂ (x ∷ Γ₀ , p , refl) with inj∷ p
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {Δ₃} {.x} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₄} {A} {B} g g₁) r | inj₂ (x ∷ Γ₀ , p , refl) | refl , q' with cases++ Δ₂ Γ₀ Δ₃ (_ ∷ Γ ++ Δ₄) (sym q')
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₂} {.(Δ₀' ++ A ⊸ B ∷ Γ ++ Δ₄)} {.x} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Δ₂ ++ A₂ ∷ Δ₀') {Γ} {Δ₄} {A} {B} g g₁) refl | inj₂ (x ∷ .(Δ₂ ++ A₂ ∷ Δ₀') , refl , refl) | refl , refl | inj₁ (Δ₀' , refl , refl)
--   rewrite cases++-inj₂ (A₂ ∷ Δ₀') (Δ₀ ++ x ∷ Δ₂) (Γ ++ Δ₄) (A ⊸ B) | cases++-inj₂ (A₂ ∷ Δ₀') (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₂) (Γ ++ Δ₄) (A ⊸ B)
--         | cases++-inj₂ (x ∷ Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₀') Δ₀ (Γ ++ Δ₄) (A ⊸ B)
--         = ⊸c (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₂ ++ asCxt S₂ Γ₂ ++ Δ₀') refl (ccut-par-ccut Δ₀ f₁ f₂ g₁ refl)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .Γ₀} {.(Γ ++ Δ₄)} {.x} {.(A ⊸ B)} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₄} {A} {B} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) | refl , refl | inj₂ ([] , refl , refl)
--   rewrite cases++-inj₂ [] (Δ₀ ++ x ∷ Γ₀) (Γ ++ Δ₄) (A ⊸ B) | cases++-inj₂ [] (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀) (Γ ++ Δ₄) (A ⊸ B)
--   = ccut-par-pr-ccut3 f₂ f₁ g g₁
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀ ++ x₁ ∷ Δ₀')} {Δ₃} {.x} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₄} {A} {B} g g₁) r | inj₂ (x ∷ Γ₀ , p , refl) | refl , q' | inj₂ (x₁ ∷ Δ₀' , s , refl) with cases++ Δ₀' Γ Δ₃ Δ₄ (inj∷ s .proj₂)
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {_} {.(Γ₀ ++ A ⊸ B ∷ Δ₀')} {.(Γ₀' ++ Δ₄)} {.x} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {.(Δ₀' ++ A₂ ∷ Γ₀')} {Δ₄} {A} {B} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) | refl , refl | inj₂ (.(A ⊸ B) ∷ Δ₀' , refl , refl) | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Δ₀ ++ x ∷ Γ₀) Δ₀' (A₂ ∷ Γ₀' ++ Δ₄) (A ⊸ B) | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀) Δ₀' (A₂ ∷ Γ₀' ++ Δ₄) (A ⊸ B)
--         | cases++-inj₁ Δ₀' Γ₀' Δ₄ A₂ | cases++-inj₂ (x ∷ Γ₀) Δ₀ (Δ₀' ++ asCxt S₂ Γ₂ ++ Γ₀' ++ Δ₄) (A ⊸ B) = refl
-- ccut-par-ccut {S₁} {S₂} {Γ₁ = Γ₁} {Γ₂} Δ₀ {_} {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Γ₀')} {Δ₃} {.x} {A₂} f₁ f₂ (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {.(Γ₀' ++ A₂ ∷ Δ₃)} {A} {B} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) | refl , refl | inj₂ (.(A ⊸ B) ∷ .(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Δ₀ ++ x ∷ Γ₀) (Γ ++ Γ₀')  (A₂ ∷ Δ₃) (A ⊸ B) | cases++-inj₁ (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀) (Γ ++ Γ₀')  (A₂ ∷ Δ₃) (A ⊸ B)
--         | cases++-inj₂  Γ₀' Γ Δ₃ A₂ | cases++-inj₂ (x ∷ Γ₀) Δ₀ (Γ ++ Γ₀' ++ asCxt S₂ Γ₂ ++ Δ₃) (A ⊸ B)
--         = ⊸c (Δ₀ ++ asCxt S₁ Γ₁ ++ Γ₀) refl (ccut-par-ccut Δ₀ {Δ₁ = Γ₀ ++ B ∷ Γ₀'} f₁ f₂ g₁ refl)
-- 
-- ccut-par-pr-ccut (uf f₁) f₂ g h = ccut-par-pr-ccut f₁ f₂ g h
-- ccut-par-pr-ccut {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁} (⊸r f₁) f₂ g h = 
--   ~ ccut-ass-ccut Γ₁ Δ₀ (ccut Δ₁ f₂ g refl) f₁ h refl
--   ∙ ~ ccut-ass-ccut Δ₁ (Δ₀ ++ asCxt S₁ Γ₁) f₂ g (ccut Δ₀ f₁ h refl) refl
--   ∙ cong-ccut2 (Δ₀ ++ asCxt S₁ Γ₁ ++ Δ₁) {f = f₂} refl (ccut-ass-ccut Γ₁ Δ₀ g f₁ h refl) 
-- ccut-par-pr-ccut {Δ₀ = Δ₀} {Δ₁} {Δ₂}{Δ₃} {A₂ = A₂} (⊸l {Γ} {Δ} {A} {B} f₁ f₃) f₂ g h
--   rewrite cases++-inj₁ Δ₀ (Γ ++ Δ ++ Δ₁) (A₂ ∷ Δ₂ ++ Δ₃) (A ⊸ B) | cases++-inj₂ ( Δ ++ Δ₁) Γ (Δ₂ ++ Δ₃) A₂
--     = ⊸c Δ₀ refl (ccut-par-pr-ccut f₃ f₂ g h)
-- ccut-par-pr-ccut {S₁} {Δ₀ = Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₂ = A₂} (⊸c Δ₀ {Γ} {Δ₅} {A} {B} f₁ f₃) f₂ g h
--   rewrite cases++-inj₁ (Δ₁ ++ asCxt S₁ Δ₀) (Γ ++ Δ₅ ++ Δ₂) (A₂ ∷ Δ₃ ++ Δ₄) (A ⊸ B) | cases++-inj₂ ( Δ₅ ++ Δ₂) Γ (Δ₃ ++ Δ₄) A₂
--     = ⊸c (Δ₁ ++ asCxt S₁ Δ₀) refl (ccut-par-pr-ccut f₃ f₂ g h)
-- 
-- ccut-par-pr-ccut2 (uf f₁) f₂ g h = ccut-par-pr-ccut2 f₁ f₂ g h
-- ccut-par-pr-ccut2 {S₁} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁} (⊸r f₁) f₂ g h =
--   ccut-par-ccut Δ₀ (ccut Γ₁ g f₁ refl) f₂ h refl 
-- ccut-par-pr-ccut2 {Δ = Δ} {Δ₀} {Δ₁} {Δ₂} {A₂ = A₂} (⊸l {Γ} {Δ₃} {A} {B} f₁ f₃) f₂ g h
--   rewrite cases++-inj₁ Δ₀ (Γ ++ Δ₃ ++ Δ ++ Δ₁) (A₂ ∷ Δ₂) (A ⊸ B) | cases++-inj₂ ( Δ₃ ++ Δ ++ Δ₁) Γ Δ₂ A₂
--    = ⊸c Δ₀ refl (ccut-par-pr-ccut2 f₃ f₂ g h)
-- ccut-par-pr-ccut2 {S₁} {Δ = Δ} {Δ₁} {Δ₂} {Δ₃} {A₂ = A₂} (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₁ f₃) f₂ g h 
--   rewrite cases++-inj₁ (Δ₁ ++ asCxt S₁ Δ₀) (Γ ++ Δ₄ ++ Δ ++ Δ₂) (A₂ ∷ Δ₃) (A ⊸ B) | cases++-inj₂ (Δ₄ ++ Δ ++ Δ₂) Γ Δ₃ A₂
--    = ⊸c (Δ₁ ++ asCxt S₁ Δ₀) refl (ccut-par-pr-ccut2 f₃ f₂ g h)
-- 
-- ccut-par-pr-ccut3 (uf f₁) f₂ g h = ccut-par-pr-ccut3 f₁ f₂ g h
-- ccut-par-pr-ccut3 {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁} (⊸r f₁) f₂ g h
--   = ccut-par-ccut Δ₀ f₂ (ccut Γ₁ g f₁ refl) h refl
-- ccut-par-pr-ccut3 {S₂ = S₂}{Γ₂ = Γ₂} {Δ = Δ} {Δ₀} {Δ₁} {Δ₂} {A₂ = A₂} (⊸l {Γ} {Δ₃} {A} {B} f₁ f₃) f₂ g h
--   rewrite cases++-inj₂ (A₂ ∷ Δ₁) Δ₀ (Γ ++ Δ₃ ++ Δ ++ Δ₂) (A ⊸ B)
--     = ⊸c (Δ₀ ++ asCxt S₂ Γ₂ ++ Δ₁) refl (ccut-par-pr-ccut3 f₃ f₂ g h)
-- ccut-par-pr-ccut3 {S₁} {S₂} {Γ₂ = Γ₂} {Δ} {Δ₁} {Δ₂} {Δ₃} {A₂ = A₂} (⊸c Δ₀ {Γ} {Δ₄} {A} {B} f₁ f₃) f₂ g h
--   rewrite cases++-inj₂ (A₂ ∷ Δ₂ ++ asCxt S₁ Δ₀) Δ₁ (Γ ++ Δ₄ ++ Δ ++ Δ₃) (A ⊸ B)
--     = ⊸c (Δ₁ ++ asCxt S₂ Γ₂ ++ Δ₂ ++ asCxt S₁ Δ₀) refl (ccut-par-pr-ccut3 f₃ f₂ g h)
-- 
-- scut-par-pr-ccut Δ₀ f' (uf f) g h = scut-par-pr-ccut Δ₀ f' f g h
-- scut-par-pr-ccut {Γ = Γ} Δ₀ f' (⊸r f) g h = scut-par-ccut Δ₀ f' (ccut Γ g f refl) h refl
-- scut-par-pr-ccut {Γ' = Γ'} Δ₀ f' (⊸l f f₁) g h =
--   scut⊸c Δ₀ f' f (pr-ccut Δ₀ f₁ g h)
--   ∙ ⊸c (Γ' ++ Δ₀) refl (scut-par-pr-ccut Δ₀ f' f₁ g h)
-- scut-par-pr-ccut {T = T} {Γ' = Γ'} Δ₀ f' (⊸c Δ₁ f f₁) g h =
--   scut⊸c (Δ₀ ++ asCxt T Δ₁) f' f (pr-ccut Δ₀ f₁ g h)
--   ∙ ⊸c (Γ' ++ Δ₀ ++ asCxt T Δ₁) refl (scut-par-pr-ccut Δ₀ f' f₁ g h)

-- scut-ass-scut (base x refl refl) (base {just x₂} x₁ refl refl) (base {just x₄} x₃ refl refl)
--   = ≡-to-≗ (cong (λ x → base x refl refl) (sym (scut-scut-ass-b x x₁ x₃)))
-- scut-ass-scut (base x refl refl) (base {just x₂} x₁ refl refl) (⊸r h) =
--   ⊸r (scut-ass-scut (base x refl refl) (base {just x₂} x₁ refl refl) h)
-- scut-ass-scut (base {Γ = Γ} x refl refl) (base {just x₂} {Γ = Γ₁} x₁ refl refl) (⊸c Δ₀ h h₁) =
--   ⊸c (lmap ` Γ ++ lmap ` Γ₁ ++ Δ₀) refl (scut-ass-scut (base x refl refl) (base {just x₂} x₁ refl refl) h₁)
-- scut-ass-scut (base x refl refl) (⊸r g) (base {nothing} x₁ () x₃)
-- scut-ass-scut (base x refl refl) (⊸r g) (base {just x₂} x₁ () x₃)
-- scut-ass-scut (base x refl refl) (⊸r g) (⊸r h) =
--   ⊸r (scut-ass-scut (base x refl refl) (⊸r g) h)
-- scut-ass-scut {Δ = Δ} (base {Γ = Γ} x refl refl) (⊸r g) (⊸l h h₁) =
--   scut-ass-scut (base x refl refl) (ccut Δ h g refl) h₁
--   ∙ cong-scut1 (scut-par-ccut Δ (base x refl refl) h g refl)
-- scut-ass-scut {Δ = Δ} (base {Γ = Γ} x refl refl) (⊸r g) (⊸c Δ₀ h h₁) =
--   ⊸c (lmap ` Γ ++ Δ ++ Δ₀) refl (scut-ass-scut (base x refl refl) (⊸r g) h₁)
-- scut-ass-scut (base {Γ = Γ} x refl refl) (⊸c Δ₀ g g₁) h =
--   ⊸c (lmap ` Γ ++ Δ₀) refl (scut-ass-scut (base x refl refl) g₁ h)
-- scut-ass-scut (uf f) g h = uf (scut-ass-scut f g h)
-- scut-ass-scut (⊸r f) (base {nothing} x () x₂) h
-- scut-ass-scut (⊸r f) (base {just x₁} x () x₂) h
-- scut-ass-scut (⊸r f) (⊸r g) (base {nothing} x () x₂)
-- scut-ass-scut (⊸r f) (⊸r g) (base {just x₁} x () x₂)
-- scut-ass-scut (⊸r f) (⊸r g) (⊸r h) = ⊸r (scut-ass-scut (⊸r f) (⊸r g) h)
-- scut-ass-scut (⊸r f) (⊸r {Γ = Δ} g) (⊸l h h₁) =
--   scut-ass-scut (⊸r f) (ccut Δ h g refl) h₁
--   ∙ cong-scut1 (scut-par-ccut Δ (⊸r f) h g refl)
-- scut-ass-scut {Γ = Γ} {Δ} (⊸r f) (⊸r g) (⊸c Δ₀ h h₁) =
--   ⊸c (Γ ++ Δ ++ Δ₀) refl (scut-ass-scut (⊸r f) (⊸r g) h₁)
-- scut-ass-scut {Γ = Γ} (⊸r f) (⊸l g g₁) h =
--   scut-ass-scut (ccut Γ g f refl) g₁ h
-- scut-ass-scut {Γ = Γ} (⊸r f) (⊸c Δ₀ g g₁) h =
--   ⊸c (Γ ++ Δ₀) refl (scut-ass-scut (⊸r f) g₁ h)
-- scut-ass-scut (⊸l f f₁) g h = ⊸l refl (scut-ass-scut f₁ g h)
-- scut-ass-scut (⊸c Δ₀ f f₁) g h = ⊸c Δ₀ refl (scut-ass-scut f₁ g h)

-- ccut-ass-scut Δ₀ {Δ'} f (base {Γ = Γ} g refl refl) h r with cases++-lmap ` Δ₀ (_ ∷ Δ') Γ (sym r)
-- ccut-ass-scut .(lmap ` Λ₁) {.(lmap ` Λ₂)} f (base {Γ = .(Λ₁ ++ X ∷ Λ₂)} g refl refl) (base {just x₁} {Γ = Γ} x refl refl) refl | Λ₁ , X ∷ Λ₂ , refl , refl , refl 
--   rewrite cases++-lmap-refl ` Λ₁ (X ∷ Λ₂ ++ Γ) | cases++-lmap-refl ` Λ₁ (X ∷ Λ₂) = ccut-b2-ass-scut f g x
-- ccut-ass-scut .(lmap ` Λ₁) {.(lmap ` Λ₂)} f (base {Γ = .(Λ₁ ++ X ∷ Λ₂)} g refl refl) (⊸r h) refl | Λ₁ , X ∷ Λ₂ , refl , refl , refl with ccut-ass-scut (lmap ` Λ₁) f (base g refl refl) h refl
-- ... | ih
--   rewrite cases++-lmap-refl ` Λ₁ (X ∷ Λ₂)
--    = ⊸r ih ∙ ~ scut⊸r (ccut-b2 Λ₁ f g) h
-- ccut-ass-scut {S}{Γ = Γ₁} .(lmap ` Λ₁) {.(lmap ` Λ₂)} f (base {Γ = .(Λ₁ ++ X ∷ Λ₂)} g refl refl) (⊸c Δ₀ {Γ} {Δ₁} {A} {B} h h₁) refl | Λ₁ , X ∷ Λ₂ , refl , refl , refl with ccut-ass-scut (lmap ` Λ₁) f (base g refl refl) h₁ refl
-- ... | ih
--   rewrite cases++-lmap-refl ` Λ₁ (X ∷ Λ₂) | cases++-inj₂ (` X ∷ lmap ` Λ₂ ++ Δ₀) (lmap ` Λ₁) (Γ ++ Δ₁) (A ⊸ B)
--     = ⊸c (lmap ` Λ₁ ++ asCxt S Γ₁ ++ lmap ` Λ₂ ++ Δ₀) refl ih
--       ∙ ~ (scut⊸c Δ₀ (ccut-b2 Λ₁ f g) h h₁)
-- ccut-ass-scut Δ₀ f (uf g) h r with  cases∷ Δ₀ r
-- ccut-ass-scut {nothing} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = scut-ass-scut f g h
-- ccut-ass-scut {just x} .[] f (uf g) h refl | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h)
-- ccut-ass-scut .(_ ∷ Γ₀) f (uf g) h refl | inj₂ (Γ₀ , refl , refl) = uf (ccut-ass-scut Γ₀ f g h refl)
-- ccut-ass-scut Δ₀ f (⊸r g) (base {nothing} x () x₂) refl
-- ccut-ass-scut Δ₀ f (⊸r g) (base {just x₁} x () x₂) refl
-- ccut-ass-scut Δ₀ {Δ'} f (⊸r g) (⊸r h) refl = ⊸r (ccut-ass-scut Δ₀ f (⊸r {Γ = Δ₀ ++ _ ∷ Δ'}  g) h refl)
-- ccut-ass-scut {S} {Γ = Γ} Δ₀ {Δ'} f (⊸r g) (⊸l h h₁) refl = 
--   ccut-ass-scut Δ₀ f (ccut (Δ₀ ++ _ ∷ Δ') h g refl) h₁ refl
--   ∙ cong-scut1 (ccut-par-ccut Δ₀ f h g refl)
-- ccut-ass-scut {S} {Γ = Γ} Δ₀ {Δ'} {A = A} f (⊸r g) (⊸c Δ₁ {Γ₁} {Δ₂} {A₁} {B} h h₁) refl
--   rewrite cases++-inj₂ (A ∷ Δ' ++ Δ₁) Δ₀ (Γ₁ ++ Δ₂) (A₁ ⊸ B)
--     = ⊸c (Δ₀ ++ asCxt S Γ ++ Δ' ++ Δ₁) refl (ccut-ass-scut Δ₀ f (⊸r {Γ = Δ₀ ++ _ ∷ Δ'} g) h₁ refl)
-- ccut-ass-scut Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g₁) h r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-ass-scut Δ₀ {.(Γ₀ ++ Δ)} {Δ''} {A} f (⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} g g₁) h refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ Δ'') A = refl
-- ccut-ass-scut .(Γ ++ Γ₀) {Δ'} {Δ''} {A} f (⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} g g₁) h refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ Γ₀ Γ (Δ' ++ Δ'') A = ⊸l refl (ccut-ass-scut Γ₀ f g₁ h refl)
-- ccut-ass-scut Δ₀ {Δ'} {Δ''} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) h r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A ∷ Δ') (sym r)
-- ccut-ass-scut .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {Δ''} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) h r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
-- ccut-ass-scut .(Δ₁ ++ A₁ ⊸ B ∷ Γ₀) {.(Δ₀ ++ Δ₂)} {Δ''} {A} f (⊸c Δ₁ {.(Γ₀ ++ A ∷ Δ₀)} {Δ₂} {A₁} {B} g g₁) h refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ Γ₀ (A ∷ Δ₀ ++ Δ₂ ++ Δ'') (A₁ ⊸ B) | cases++-inj₁ Γ₀ Δ₀ (Δ₂ ++ Δ'') A = refl
-- ccut-ass-scut .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₀) {Δ'} {Δ''} {A} f (⊸c Δ₁ {Γ} {.(Δ₀ ++ A ∷ Δ')} {A₁} {B} g g₁) h refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₀) (A ∷ Δ' ++ Δ'') (A₁ ⊸ B) | cases++-inj₂ Δ₀ Γ (Δ' ++ Δ'') A
--     = ⊸c Δ₁ refl (ccut-ass-scut (Δ₁ ++ B ∷ Δ₀) f g₁ h refl)
-- ccut-ass-scut _ {.(Γ ++ Δ₂)} {Δ''} {.(A ⊸ B)} f (⊸c Δ₁ {Γ} {Δ₂} {A} {B} g g₁) h refl | inj₂ ([] , refl , refl)
--   rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂ ++ Δ'') (A ⊸ B) = pr-ccut-ass-scut f g g₁ h
-- ccut-ass-scut {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Δ₂)} {Δ''} {.x} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} {A} {B} g g₁) h refl | inj₂ (x ∷ Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (x ∷ Γ₀) Δ₀ (Γ ++ Δ₂ ++ Δ'') (A ⊸ B)
--    = ⊸c (Δ₀ ++ asCxt S Γ₁ ++ Γ₀) refl (ccut-ass-scut Δ₀ f g₁ h refl)

-- ccut-ass-ccut-s Δ₀ {Δ'} {B = B} f g (base {Γ = Γ} x refl x₂) refl with cases++-lmap ` Δ₀ (B ∷ Δ') Γ x₂
-- ... | Λ₁ , X ∷ Λ₂ , refl , refl , refl = ccut-ass-ccut-b2-s f g x
-- ccut-ass-ccut-s Δ₀ f g (uf h) r with cases∷ Δ₀ r
-- ccut-ass-ccut-s {nothing} .[] f g (uf h) r | inj₁ (refl , refl , refl) = scut-ass-scut f g h
-- ccut-ass-ccut-s {just x} .[] f g (uf h) r | inj₁ (refl , refl , refl) = uf (scut-ass-scut f g h)
-- ... | inj₂ (Γ₀ , refl , refl) = uf (ccut-ass-ccut-s Γ₀ f g h refl)
-- ccut-ass-ccut-s Δ₀ f g (⊸r h) refl = ⊸r (ccut-ass-ccut-s Δ₀ f g h refl)
-- ccut-ass-ccut-s Δ₀ {Δ'} f g (⊸l {Γ} {Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-ass-ccut-s Δ₀ {.(Γ₀ ++ Δ)} {Γ'} {A} f g (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₀ ( Γ' ++ Γ₀) Δ A = ⊸l (ccut-ass-ccut-s Δ₀ f g h refl) refl
-- ccut-ass-ccut-s .(Γ ++ Γ₀) {Δ'} {Γ'} {A} f g (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} h h₁) refl | inj₂ (Γ₀ , refl , refl)
--   rewrite cases++-inj₂ Γ₀ Γ (Γ' ++ Δ') A = ⊸l refl (ccut-ass-ccut-s Γ₀ f g h₁ refl)
-- ccut-ass-ccut-s Δ₀ {Δ'} {B = B} f g (⊸c Δ₁ {Γ} {Δ₂} h h₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (B ∷ Δ') (sym r)
-- ccut-ass-ccut-s .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {B = B} f g (⊸c Δ₁ {Γ} {Δ₂} h h₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
-- ccut-ass-ccut-s .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ₀) {.(Δ₀ ++ Δ₂)} {Γ'} {A} {B} f g (⊸c Δ₁ {.(Γ₀ ++ B ∷ Δ₀)} {Δ₂} {A₁} {B₁} h h₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ Γ₀ (A ∷ Γ' ++ Δ₀ ++ Δ₂) (A₁ ⊸ B₁) | cases++-inj₁ Γ₀ (Γ' ++ Δ₀) Δ₂ A
--     = ⊸c Δ₁ (ccut-ass-ccut-s Γ₀ f g h refl) refl
-- ccut-ass-ccut-s .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₀) {Δ'} {Γ'} {A} {B} f g (⊸c Δ₁ {Γ} {.(Δ₀ ++ B ∷ Δ')} {A₁} {B₁} h h₁) refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₀) (A ∷ Γ' ++ Δ') (A₁ ⊸ B₁) | cases++-inj₂  Δ₀ Γ (Γ' ++ Δ') A
--     = ⊸c Δ₁ refl (ccut-ass-ccut-s (Δ₁ ++ B₁ ∷ Δ₀) f g h₁ refl)
-- ccut-ass-ccut-s Δ₀ {.(Γ ++ Δ₂)} {B = .(_ ⊸ _)} f g (⊸c .Δ₀ {Γ} {Δ₂} h h₁) refl | inj₂ ([] , refl , refl) = pr-ccut-ass-scut2 f g h h₁
-- ccut-ass-ccut-s {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ A₁ ⊸ B ∷ Γ ++ Δ₂)} {Γ'} {A} {.x} f g (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} {A₁} {B} h h₁) refl | inj₂ (x ∷ Γ₀ , refl , refl)
--   rewrite cases++-inj₂ (A ∷ Γ' ++ Γ₀) Δ₀ (Γ ++ Δ₂) (A₁ ⊸ B)
--     = ⊸c (Δ₀ ++ asCxt S Γ₁ ++ Γ' ++ Γ₀) refl (ccut-ass-ccut-s Δ₀ f g h₁ refl)



-- pr-ccut-ass-scut (uf f) g h k = pr-ccut-ass-scut f g h k
-- pr-ccut-ass-scut {Γ = Γ} {Δ₀ = Δ₀} (⊸r f) g h k = ccut-ass-scut Δ₀ (ccut Γ g f refl) h k refl
-- pr-ccut-ass-scut {Δ₀ = Δ₀} (⊸l f f₁) g h k = ⊸c Δ₀ refl (pr-ccut-ass-scut f₁ g h k)
-- pr-ccut-ass-scut {S} {Δ₀ = Δ₁} (⊸c Δ₀ f f₁) g h k = ⊸c (Δ₁ ++ asCxt S Δ₀) refl (pr-ccut-ass-scut f₁ g h k)

-- pr-ccut-ass-scut2 {Γ = Γ} {Δ₀ = Δ₀} {Λ = Λ} k (⊸r f) g h = 
--   ccut-ass-ccut-s Δ₀ k (ccut Γ g f refl) h refl
--   ∙ cong-ccut1 Δ₀ h refl (scut-par-ccut Γ k g f refl)
--   ∙ ~ (cong-pr-ccut1 Δ₀ (scut⊸r k f) g h)
-- pr-ccut-ass-scut2 {Δ = Δ} {Δ₀} {Δ₁} (uf k) (⊸l {Γ} {Δ₂} {A} {B} f f₁) g h with pr-ccut-ass-scut2 k (⊸l f f₁) g h
-- ... | ih rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ Δ ++ Δ₁) (A ⊸ B ) = ih
-- pr-ccut-ass-scut2 {Δ = Δ} {Δ₀} {Δ₁} (⊸r {Γ = Λ} k) (⊸l {Γ} {Δ₂} {A} {B} f f₁) g h
--   rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ Δ ++ Δ₁) (A ⊸ B ) = pr-ccut-ass-scut2 (ccut Λ f k refl) f₁ g h 
-- pr-ccut-ass-scut2 {Δ = Δ} {Δ₀} {Δ₁} (⊸l k k₁) (⊸l {Γ} {Δ₂} {A} {B} f f₁) g h with pr-ccut-ass-scut2 k₁ (⊸l f f₁) g h
-- ... | ih rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ Δ ++ Δ₁) (A ⊸ B ) =
--     ⊸c Δ₀ refl ih
-- pr-ccut-ass-scut2 {S} {Δ = Δ} {Δ₀} {Δ₁} (⊸c Δ₃ k k₁) (⊸l {Γ} {Δ₂} {A} {B} f f₁) g h with pr-ccut-ass-scut2 k₁ (⊸l f f₁) g h
-- ... | ih rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ Δ ++ Δ₁) (A ⊸ B )
--   = ⊸c (Δ₀ ++ asCxt S Δ₃) refl ih
-- pr-ccut-ass-scut2 {S} {Δ = Δ} {Δ₁} {Δ₂} {Λ} {D = D} k (⊸c Δ₀ {Γ} {Δ₃} {A} {B} f f₁) g h
--   rewrite cases++-inj₂ (D ∷ Δ₀) Δ₁ (Γ ++ Δ₃ ++ Δ ++ Δ₂) (A ⊸ B) =
--     ⊸c (Δ₁ ++ asCxt S Λ ++ Δ₀) refl (pr-ccut-ass-scut2 k f₁ g h)
--     ∙ ~ cong-pr-ccut1 Δ₁ (scut⊸c Δ₀ k f f₁) g h


-- ccut-ass-ccut {Γ = Γ} Γ₀ Δ₀ {Δ'} {B = B} f g (base {Γ = Γ₁} x refl x₂) refl with cases++-lmap ` Δ₀ (B ∷ Δ') Γ₁ x₂
-- ccut-ass-ccut {Γ = Γ} Γ₀ .(lmap ` Λ₁) {.(lmap ` Λ₂)} {B = .(` X)} f g (base {Γ = .(Λ₁ ++ X ∷ Λ₂)} x refl refl) refl | Λ₁ , X ∷ Λ₂ , refl , refl , refl
--   = ccut-ass-ccut-b2 f g x refl
-- ccut-ass-ccut Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
-- ccut-ass-ccut {S₂ = nothing} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccut-ass-scut Γ₀ f g h refl
-- ccut-ass-ccut {S₂ = just x} Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = uf (ccut-ass-scut Γ₀ f g h refl)
-- ... | inj₂ (Γ₀' , refl , refl) = uf (ccut-ass-ccut Γ₀ Γ₀' f g h refl)
-- ccut-ass-ccut Γ₀ Δ₀ f g (⊸r h) refl = ⊸r (ccut-ass-ccut Γ₀ Δ₀ f g h refl)
-- ccut-ass-ccut Γ₀ Δ₀ {Δ'} f g (⊸l {Γ} {Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r
-- ccut-ass-ccut {S₂ = S₂} Γ₀ Δ₀ {.(Γ₀' ++ Δ)} {Γ'} {A} f g (⊸l {.(Δ₀ ++ _ ∷ Γ₀')} {Δ} h h₁) refl | inj₁ (Γ₀' , refl , refl)
--   rewrite cases++-inj₁ (Δ₀ ++ asCxt S₂ Γ₀) (Γ' ++ Γ₀') Δ A
--     = ⊸l (ccut-ass-ccut Γ₀ Δ₀ f g h refl) refl
-- ccut-ass-ccut {S₂ = S₂} Γ₀ .(Γ ++ Γ₀') {Δ'} {Γ'} {A} f g (⊸l {Γ} {.(Γ₀' ++ _ ∷ Δ')} h h₁) refl | inj₂ (Γ₀' , refl , refl)
--   rewrite cases++-inj₂ (Γ₀' ++ asCxt S₂ Γ₀) Γ (Γ' ++ Δ') A
--     = ⊸l refl (ccut-ass-ccut Γ₀ Γ₀' f g h₁ refl)
-- ccut-ass-ccut {S₂ = S₂} Γ₀ Δ₀ {Δ'} {B = B} f g (⊸c Δ₁ {Γ} {Δ₂} h h₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (B ∷ Δ') (sym r)
-- ccut-ass-ccut {S₂ = S₂} Γ₀ .(Δ₁ ++ _ ⊸ _ ∷ Γ₀') {Δ'} {B = B} f g (⊸c Δ₁ {Γ} {Δ₂} h h₁) r | inj₁ (Γ₀' , refl , q) with cases++ Γ₀' Γ Δ' Δ₂ q
-- ccut-ass-ccut {S₂ = S₂} Γ₀ .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ₀') {.(Δ₀ ++ Δ₂)} {Γ'} {A} {B} f g (⊸c Δ₁ {.(Γ₀' ++ B ∷ Δ₀)} {Δ₂} {A₁} {B₁} h h₁) refl | inj₁ (Γ₀' , refl , refl) | inj₁ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ₀' ++ asCxt S₂ Γ₀)  (A ∷ Γ' ++ Δ₀ ++ Δ₂) (A₁ ⊸ B₁) | cases++-inj₁ (Γ₀' ++ asCxt S₂ Γ₀) (Γ' ++ Δ₀) Δ₂ A
--     = ⊸c Δ₁ (ccut-ass-ccut Γ₀ Γ₀' f g h refl) refl
-- ccut-ass-ccut {S₂ = S₂} Γ₀ .(Δ₁ ++ A₁ ⊸ B₁ ∷ Γ ++ Δ₀) {Δ'} {Γ'} {A} {B} f g (⊸c Δ₁ {Γ} {.(Δ₀ ++ B ∷ Δ')} {A₁} {B₁} h h₁) refl | inj₁ (.(Γ ++ Δ₀) , refl , refl) | inj₂ (Δ₀ , refl , refl)
--   rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₀ ++ asCxt S₂ Γ₀) (A ∷ Γ' ++ Δ') (A₁ ⊸ B₁) | cases++-inj₂ (Δ₀ ++ asCxt S₂ Γ₀) Γ (Γ' ++ Δ') A
--     = ⊸c Δ₁ refl (ccut-ass-ccut Γ₀ (Δ₁ ++ _ ∷ Δ₀) f g h₁ refl)
-- ccut-ass-ccut {S₂ = S₂} Γ₀ _ {.(Γ ++ Δ₂)} {B = .(_ ⊸ _)} f g (⊸c _ {Γ} {Δ₂} h h₁) refl | inj₂ ([] , refl , refl) = pr-ccut-ass-ccut f g h h₁ refl
-- ccut-ass-ccut {S₁}{S₂ = S₂}{Γ = Γ₁} Γ₀ Δ₀ {.(Γ₀' ++ A₁ ⊸ B ∷ Γ ++ Δ₂)} {Γ'} {A} {.x} f g (⊸c .(Δ₀ ++ x ∷ Γ₀') {Γ} {Δ₂} {A₁} {B} h h₁) refl | inj₂ (x ∷ Γ₀' , refl , refl)
--   rewrite cases++-inj₂ (A ∷ Γ' ++ Γ₀') (Δ₀ ++ asCxt S₂ Γ₀) (Γ ++ Δ₂) (A₁ ⊸ B) =
--     ⊸c (Δ₀ ++ asCxt S₂ Γ₀ ++ asCxt S₁ Γ₁ ++ Γ' ++ Γ₀') refl (ccut-ass-ccut Γ₀ Δ₀ f g h₁ refl)

pr-ccut-ass-ccut {Γ₀ = Γ₀} f (uf g) h k r with cases∷ Γ₀ r
pr-ccut-ass-ccut {nothing} {Γ₀ = .[]} f (uf g) h k refl | inj₁ (refl , refl , refl) = pr-ccut-ass-scut2 f g h k
pr-ccut-ass-ccut {just x} {Γ₀ = .[]} f (uf g) h k refl | inj₁ (refl , refl , refl) = pr-ccut-ass-scut2 f g h k
pr-ccut-ass-ccut {Γ₀ = .(_ ∷ Δ₀)} f (uf g) h k refl | inj₂ (Δ₀ , refl , refl) = pr-ccut-ass-ccut f g h k refl
pr-ccut-ass-ccut {S₁} {S₂} {Γ₀ = Γ₀} {Γ₁} {Λ₀ = Λ₀} {A' = A'} f (⊸r g) h k refl
  = ccut-ass-ccut Γ₀ Λ₀ f (ccut (Γ₀ ++ A' ∷ Γ₁) h g refl) k refl
    ∙ cong-ccut1 Λ₀ k refl (ccut-par-ccut Γ₀ f h g refl)
pr-ccut-ass-ccut {Γ₀ = Γ₀} {Γ₁} f (⊸l {Γ} {Δ} g g₁) h k r with  cases++ Γ₀ Γ Γ₁ Δ r
pr-ccut-ass-ccut {Γ₀ = .(Γ ++ Γ₀')} {Γ₁} {Δ = Δ} {Λ₀} {Λ₁} {A' = A'} f (⊸l {Γ} {.(Γ₀' ++ A' ∷ Γ₁)} {A} {B} g g₁) h k refl | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Λ₀ (Γ ++ Γ₀') (A' ∷ Γ₁ ++ Δ ++ Λ₁) (A ⊸ B) | cases++-inj₂ Γ₀' Γ (Γ₁ ++ Δ ++ Λ₁) A'
    = ⊸c Λ₀ refl (pr-ccut-ass-ccut f g₁ h k refl)
pr-ccut-ass-ccut {Γ₀ = Γ₀} {.(Γ₀' ++ Δ)} {Δ = Δ₁} {Λ₀} {Λ₁} {A' = A'} f (⊸l {.(Γ₀ ++ A' ∷ Γ₀')} {Δ} {A} {B} g g₁) h k refl | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Λ₀ Γ₀ (A' ∷ Γ₀' ++ Δ ++ Δ₁ ++ Λ₁) (A ⊸ B) | cases++-inj₁ Γ₀ Γ₀' (Δ ++ Δ₁ ++ Λ₁) A' = refl
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {Γ₀} {Γ₂} {A' = A'} f (⊸c Δ₀ {Γ₁} {Δ₁} g g₁) h k r with cases++ Δ₀ Γ₀ (Γ₁ ++ Δ₁) (A' ∷ Γ₂) (sym r)
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {.(Δ₀ ++ _ ⊸ _ ∷ Γ₀')} {Γ₂} {A' = A'} f (⊸c Δ₀ {Γ₁} {Δ₁} g g₁) h k r | inj₁ (Γ₀' , refl , q) with  cases++ Γ₀' Γ₁ Γ₂ Δ₁ q
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {.(Δ₀ ++ _ ⊸ _ ∷ Γ₀')} {.(Γ₀'' ++ Δ₁)} {A' = A'} f (⊸c Δ₀ {.(Γ₀' ++ A' ∷ Γ₀'')} {Δ₁} g g₁) h k refl | inj₁ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl) = {!!}
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {.(Δ₀ ++ _ ⊸ _ ∷ Γ₁ ++ Γ₀'')} {Γ₂} {A' = A'} f (⊸c Δ₀ {Γ₁} {.(Γ₀'' ++ A' ∷ Γ₂)} g g₁) h k refl | inj₁ (.(Γ₁ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) = {!!}
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {.Δ₀} {.(Γ₁ ++ Δ₁)} {Δ = Δ} {Λ₀} {Λ₁} {A' = .(A ⊸ B)} f (⊸c Δ₀ {Γ₁} {Δ₁} {A} {B} g g₁) h k refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Λ₀ ++ asCxt S₂ Δ₀) (Γ₁ ++ Δ₁ ++ Δ ++ Λ₁) (A ⊸ B) = {!!}
pr-ccut-ass-ccut {S₂ = S₂} {Γ = Γ} {Γ₀} {.(Γ₀' ++ _ ⊸ _ ∷ Γ₁ ++ Δ₁)} {A' = .x} f (⊸c .(Γ₀ ++ x ∷ Γ₀') {Γ₁} {Δ₁} g g₁) h k refl | inj₂ (x ∷ Γ₀' , refl , refl) = {!!}




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
