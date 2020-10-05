{-# OPTIONS --rewriting  #-}

open import SkMults

module CutsCong where
--(M : SkMult) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.List hiding (map)
open import Data.Product hiding (uncurry;curry)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae 
open import SeqCalc
--open import FreeSkewClosed



scut-unit : {Γ : Cxt}{A C : Fma}(f : just A ∣ Γ ⊢ C) → scut ax f ≗ f
scut-unit2 : {S : Stp}{Γ : Cxt}{A : Fma}(f : S ∣ Γ ⊢ A) → scut f ax ≗ f
ccut-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Fma}
  → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
  → ccut Δ₀ ax g r ≗ subst-cxt r g
⊸c-alt : {S : Stp} (Δ₀ : Cxt) {Δ Γ Δ₁ : Cxt} {A B C : Fma}
  → (f : nothing ∣ Γ ⊢ A) (g : S ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ B ∷ Δ₁)
  → ccut Δ₀ (uf (⊸l f ax)) g eq ≗ ⊸c Δ₀ f (subst-cxt eq g)
cong-ccut1 : {S T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma} → 
               {f f' : S ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               f ≗ f' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g r
cong-scut1 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
               {f g : S ∣ Γ ⊢ A}  → {h : just A ∣ Δ' ⊢ C} →
               f ≗ g → scut f h ≗ scut g h
cong-scut2 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
            (h : S ∣ Γ ⊢ A)  → {f g : just A ∣ Δ' ⊢ C} →
            f ≗ g → scut h f ≗ scut h g
cong-ccut2 : {S T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma} → 
               {f : S ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
               g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f g' r
cong-scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Fma} → 
             {f g : S ∣ Γ ⊢ A}  → {h k : just A ∣ Δ' ⊢ C} →
             f ≗ g → h ≗ k → scut f h ≗ scut g k
cong-ccut : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma}
  → {f f' : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C} (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  →  f ≗ f' → g ≗ g' → ccut Δ₀ f g r ≗ ccut Δ₀ f' g' r
cong-pr-ccut1 : ∀ {S T Γ Γ₁} Δ₀ {Δ₁ A B C}
    → {f f' : S ∣ Γ ⊢ A ⊸ B} → f ≗ f'
    → (g : nothing ∣ Γ₁ ⊢ A) (h : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    →  pr-ccut Δ₀ f g h ≗ pr-ccut Δ₀ f' g h
cong-pr-ccut2 : ∀ {S T Γ Γ₁} Δ₀ {Δ₁ A B C}
    → (f : S ∣ Γ ⊢ A ⊸ B) {g g' : nothing ∣ Γ₁ ⊢ A} → g ≗ g'
    → (h : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    → pr-ccut Δ₀ f g h ≗ pr-ccut Δ₀ f g' h
cong-pr-ccut3 : ∀ {S T Γ Γ₁} Δ₀ {Δ₁ A B C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A)
    → {h h' : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C}  → h ≗ h'
    → pr-ccut Δ₀ f g h ≗ pr-ccut Δ₀ f g h'

pr-ccut⊸c22 : ∀ {S T Γ Γ₁} Δ₀ Λ₀ {Δ₁ Λ₁ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A') (h : nothing ∣ Λ₀ ++ B' ∷ Λ₁ ⊢ A) (k : T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    → pr-ccut Δ₀ f (⊸c Λ₀ g h) k ≗ ⊸c (Δ₀ ++ asCxt S Γ ++ Λ₀) g (pr-ccut Δ₀ f h k)

⊸c-alt Δ₀ {Δ₁ = Δ₁} {B = B} f (base {Γ = Γ} g refl eq) refl with cases++-lmap ` Δ₀ (B ∷ Δ₁) Γ eq
⊸c-alt _ {Δ₁ = _} {B = _} f (base {Γ = _} g refl refl) refl | Γ₁ , X ∷ Γ₂ , refl , refl , refl
  rewrite cases++-lmap-refl ` Γ₁ (X ∷ Γ₂) | cases++-lmap-refl ` Γ₁ (X ∷ Γ₂) =
    ⊸c (lmap ` Γ₁) refl (≡-to-≗ (cong (λ x → base x refl refl) (ccut-ax-b  Γ₁ g)))
⊸c-alt Δ₀ f (uf g) eq with cases∷ Δ₀ eq
⊸c-alt .[] f (uf g) refl | inj₁ (refl , refl , refl) =
  uf (⊸l refl (scut-unit _)) ∙ (~ ⊸cuf2)
⊸c-alt .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  uf (⊸c-alt Γ₀ f g refl) ∙ (~ ⊸cuf)
⊸c-alt Δ₀ f (⊸r g) refl =
  ⊸r (⊸c-alt Δ₀ f g refl) ∙ ⊸r⊸c
⊸c-alt Δ₀ {Δ₁ = Δ₁} f (⊸l {Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ₁ Δ eq
⊸c-alt Δ₀ {Γ = Γ} {Δ₁ = .(Γ₀ ++ Δ)} f (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  ⊸l (⊸c-alt Δ₀ f g refl) refl ∙ (~ ⊸c⊸l2)
⊸c-alt .(Γ ++ Γ₀) {Δ₁ = Δ₁} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} g g') refl | inj₂ (Γ₀ , refl , refl) =
  ⊸l refl (⊸c-alt Γ₀ f g' refl) ∙ (~ ⊸c⊸l)
⊸c-alt Δ₀ {Δ₁ = Δ₂} {B = B} f (⊸c Δ₁ {Γ} {Δ₃} g g') eq with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (B ∷ Δ₂) (sym eq)
⊸c-alt .Δ₁ {Δ₁ = .(Γ ++ Δ₃)} {B = .(A ⊸ B)} f (⊸c Δ₁ {Γ} {Δ₃} {A} {B} g g') refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₃) (A ⊸ B) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₃) (A ⊸ B) =
    ⊸c Δ₁ refl
      (cong-ccut1 Δ₁ g' refl (⊸l (scut-unit2 g) refl)
        ∙ ≡-to-≗ (sym (ccut-uf Δ₁ (⊸l g ax) g' refl))
        ∙ ⊸c-alt Δ₁ g g' refl)
⊸c-alt Δ₀ {Γ = Γ₁} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₃} g g') refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ _ ∷ Γ₁ ++ Γ₀) refl (⊸c-alt Δ₀ f g' refl) ∙ ⊸c⊸c
⊸c-alt .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ₁ = Δ₂} {B = B} f (⊸c Δ₁ {Γ} {Δ₃} g g') eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₂ Δ₃ q
⊸c-alt ._ {B = B} f (⊸c Δ₁ {.(Γ₀ ++ B ∷ Γ₀')} {Δ₃} g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (⊸c-alt Γ₀ f g refl) refl ∙ (~ ⊸c⊸c2)
⊸c-alt ._ {Δ₁ = Δ₂} {B = B} f (⊸c Δ₁ {Γ} g g') refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ refl (⊸c-alt (Δ₁ ++ _ ∷ Γ₀') f g' refl) ∙ (~ ⊸c⊸c)

ccut-unit {Γ = Γ} Δ₀ (base {Γ = Γ₁} x refl x₂) refl with  cases++-lmap ` Δ₀ (_ ∷ Γ) Γ₁ x₂
ccut-unit {Γ = .(lmap ` Λ₂)} .(lmap ` Λ₁) (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl refl) refl | Λ₁ , x₁ ∷ Λ₂ , refl , refl , refl 
  rewrite cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) =
    ≡-to-≗ (cong (λ y → base y refl refl) (ccut-ax-b Λ₁ x))
ccut-unit Δ₀ (uf g) r with cases∷ Δ₀ r
ccut-unit .[] (uf g) refl | inj₁ (refl , refl , refl) = uf (scut-unit g)
ccut-unit .(_ ∷ Γ₀) (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  uf (ccut-unit Γ₀ g refl)
ccut-unit Δ₀ (⊸r g) refl = ⊸r (ccut-unit Δ₀ g refl )
ccut-unit {Γ = Γ} Δ₀ (⊸l {Γ₁} {Δ} g g₁) r with cases++ Δ₀ Γ₁ Γ Δ r
ccut-unit {Γ = .(Γ₀ ++ Δ)} Δ₀ (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) =
  ⊸l (ccut-unit Δ₀ g refl) refl
ccut-unit {Γ = Γ} .(Γ₁ ++ Γ₀) (⊸l {Γ₁} {.(Γ₀ ++ _ ∷ Γ)} g g₁) refl | inj₂ (Γ₀ , refl , refl) =
  ⊸l refl (ccut-unit Γ₀ g₁ refl)
ccut-unit {Γ = Γ} Δ₀ {A} (⊸c Δ₁ {Γ₁} {Δ₂} g g₁) r with cases++ Δ₁ Δ₀ (Γ₁ ++ Δ₂) (A ∷ Γ) (sym r)
ccut-unit {Γ = Γ} .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {A} (⊸c Δ₁ {Γ₁} {Δ₂} g g₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ₁ Γ Δ₂ q
ccut-unit {Γ = .(Γ₀' ++ Δ₂)} .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {A} (⊸c Δ₁ {.(Γ₀ ++ A ∷ Γ₀')} {Δ₂} g g₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (ccut-unit Γ₀ g refl) refl
ccut-unit {Γ = Γ} .(Δ₁ ++ _ ⊸ _ ∷ Γ₁ ++ Γ₀') {A} (⊸c Δ₁ {Γ₁} {.(Γ₀' ++ A ∷ Γ)} g g₁) refl | inj₁ (.(Γ₁ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ refl (ccut-unit (Δ₁ ++ _ ∷ Γ₀') g₁ refl)
ccut-unit {Γ = .(Γ₁ ++ Δ₂)} _ {.(A ⊸ B)} (⊸c Δ₁ {Γ₁} {Δ₂} {A} {B} g g₁) refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₁ (Γ₁ ++ Δ₂) (A ⊸ B) =
    cong-ccut1 Δ₁ g₁ refl (⊸l (scut-unit2 g) refl)
    ∙ ≡-to-≗ (sym (ccut-uf Δ₁ (⊸l g ax) g₁ refl))
    ∙ ⊸c-alt Δ₁ g g₁ refl
ccut-unit {Γ = .(Γ₀ ++ _ ⊸ _ ∷ Γ₁ ++ Δ₂)} Δ₀ {.x} (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ₁} {Δ₂} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ x ∷ Γ₀) refl (ccut-unit Δ₀ g₁ refl)

scut-unit2 (base x refl refl) =
  ≡-to-≗ (cong (λ y → base y refl refl) (scut-ax-b x))
scut-unit2 (uf f) = uf (scut-unit2 f)
scut-unit2 (⊸r {Γ = Γ} f) =
  ⊸r (cong-scut1 (≡-to-≗ (ccut-uf Γ ax f refl) ∙ ccut-unit Γ f refl) ∙ scut-unit2 f)
scut-unit2 (⊸l f f₁) = ⊸l refl (scut-unit2 f₁)
scut-unit2 (⊸c Δ₀ f f₁) = ⊸c Δ₀ refl (scut-unit2 f₁)

scut-unit {A = ` X} (base {just .X} x refl refl) =
  ≡-to-≗ (cong (λ y → base y refl refl) (scut-ax-b2 x))
scut-unit {A = ` X} (⊸r f) = ⊸r (scut-unit f)
scut-unit {A = ` X} (⊸c Δ₀ f f₁) = ⊸c Δ₀ refl (scut-unit f₁) 
scut-unit {A = A ⊸ B} (base {nothing} x () refl)
scut-unit {A = A ⊸ B} (base {just x₁} x () refl)
scut-unit {A = A ⊸ B} (⊸r f) = ⊸r (scut-unit f)
scut-unit {A = A ⊸ B} (⊸l f f₁) = ⊸l (scut-unit2 f) (scut-unit f₁)
scut-unit {A = A ⊸ B} (⊸c Δ₀ f f₁) = ⊸c Δ₀ refl (scut-unit f₁)

cong-scut1 refl = refl
cong-scut1 (~ p) = ~ cong-scut1 p
cong-scut1 (p ∙ p₁) = cong-scut1 p ∙ cong-scut1 p₁
cong-scut1 (uf p) = uf (cong-scut1 p)
cong-scut1 {h = base {nothing} x () refl} (⊸r p)
cong-scut1 {h = base {just x₁} x () refl} (⊸r p)
cong-scut1 {h = ⊸r h} (⊸r p) = ⊸r (cong-scut1 {h = h} (⊸r p))
cong-scut1 {Γ = Γ} {h = ⊸l {Γ₁} h h₁} (⊸r p) =
  cong-scut1 {Γ = Γ ++ Γ₁} {h = h₁} (cong-ccut2 Γ {f = h} refl p)
cong-scut1 {Γ = Γ} {h = ⊸c Δ₀ h h₁} (⊸r p) = ⊸c (Γ ++ Δ₀) refl (cong-scut1 {h = h₁} (⊸r p))
cong-scut1 (⊸l p p₁) = ⊸l p (cong-scut1 p₁)
cong-scut1 (⊸c Δ₀ p p₁) = ⊸c Δ₀ p (cong-scut1 p₁)
cong-scut1 {h = h} (⊸ruf {f = f}) = scut⊸ruf f h
cong-scut1 {h = h} (⊸r⊸l {f = f} {g}) = scut⊸r⊸l f g h
cong-scut1 {h = h} (⊸r⊸c {Δ₀ = Δ₀} {f = f} {g}) = scut⊸r⊸c Δ₀ f g h
cong-scut1 ⊸cuf = ⊸cuf
cong-scut1 ⊸cuf2 = ⊸cuf2
cong-scut1 ⊸c⊸l = ⊸c⊸l
cong-scut1 ⊸c⊸l2 = ⊸c⊸l2
cong-scut1 ⊸c⊸c = ⊸c⊸c
cong-scut1 ⊸c⊸c2 = ⊸c⊸c2
cong-scut1 {h = base {nothing} x () refl} baseuf
cong-scut1 {h = base {just x₁} x refl refl} baseuf =
  ≡-to-≗ (cong (λ x → base x refl refl) (scut-uf-b _ _)) ∙ baseuf
cong-scut1 {h = ⊸r h} baseuf =
  ⊸r (cong-scut1 {h = h} baseuf) ∙ ⊸ruf
cong-scut1 {h = ⊸c Δ₀ h h₁} (baseuf {Γ} {X}) =
  ⊸c (` X ∷ lmap ` Γ ++ Δ₀) refl (cong-scut1 {h = h₁} baseuf) ∙ ⊸cuf {Δ₀ = lmap ` Γ ++ Δ₀}

cong-scut2 (base x refl refl) refl = refl
cong-scut2 (base x refl refl) (~ p) = ~ (cong-scut2 (base x refl refl) p)
cong-scut2 (base x refl refl) (p ∙ p₁) = cong-scut2 (base x refl refl) p ∙ cong-scut2 (base x refl refl) p₁
cong-scut2 (base x refl refl) (⊸r p) = ⊸r (cong-scut2 (base x refl refl) p)
cong-scut2 (base {Γ = Γ} x refl refl) (⊸c Δ₀ p p₁) = ⊸c (lmap ` Γ ++ Δ₀) p (cong-scut2 (base x refl refl) p₁)
cong-scut2 (base {Γ = Γ} x refl refl) (⊸r⊸c {Δ₀ = Δ₀}) = ⊸r⊸c {Δ₀ = lmap ` Γ ++ Δ₀}
cong-scut2 (base {Γ = Γ} x refl refl) (⊸c⊸c {Δ₀ = Δ₀}) = ⊸c⊸c {Δ₀ = lmap ` Γ ++ Δ₀}
cong-scut2 (base {Γ = Γ} x refl refl) (⊸c⊸c2 {Δ₀ = Δ₀} {Δ₂ = Δ₂}) = ⊸c⊸c2 {Δ₀ = Δ₀}{Δ₂ = lmap ` Γ ++ Δ₂}
cong-scut2 (uf f) p = uf (cong-scut2 f p)
cong-scut2 (⊸r f) refl = refl
cong-scut2 (⊸r f) (~ p) = ~ (cong-scut2 (⊸r f) p)
cong-scut2 (⊸r f) (p ∙ p₁) = cong-scut2 (⊸r f) p ∙ cong-scut2 (⊸r f) p₁
cong-scut2 (⊸r f) (⊸r p) = ⊸r (cong-scut2 (⊸r f) p)
cong-scut2 {Γ = Γ} (⊸r f) (⊸l p p₁) = cong-scut (cong-ccut1 Γ f refl p) p₁
cong-scut2 {Γ = Γ} (⊸r f) (⊸c Δ₀ p p₁) = ⊸c (Γ ++ Δ₀) p (cong-scut2 (⊸r f) p₁)
cong-scut2 {Γ = Γ} (⊸r f) (⊸r⊸l {f = f₁} {g}) = ~ (scut⊸r (ccut Γ f₁ f refl) g)
cong-scut2 {Γ = Γ} (⊸r f) (⊸r⊸c {Δ₀ = Δ₀}) = ⊸r⊸c {Δ₀ = Γ ++ Δ₀}
cong-scut2 {Γ = Γ} (⊸r f) (⊸c⊸l {Γ₁} {Δ} {f = f₁} {f'} {g}) = ~ scut⊸c Δ (ccut Γ f₁ f refl) f' g
cong-scut2 {Γ = Γ} (⊸r f) (⊸c⊸l2 {Δ = Δ} {Γ'} {Λ} {f = f₁} {f'} {g}) = ~ (cong-scut1 {Γ = Γ ++ Δ ++ _ ∷ Γ' ++ Λ} {h = g} (ccut⊸c Γ Δ f' f₁ f refl))
cong-scut2 {Γ = Γ} (⊸r f) (⊸c⊸c {Δ₀ = Δ₀} {Δ₁}) = ⊸c⊸c {Δ₀ = Γ ++ Δ₀}{Δ₁ = Δ₁}
cong-scut2 {Γ = Γ} (⊸r f) (⊸c⊸c2 {Δ₀ = Δ₀} {Δ₂ = Δ₂}) = ⊸c⊸c2 {Δ₀ = Δ₀}{Δ₂ = Γ ++ Δ₂}
cong-scut2 (⊸l f f₁) p = ⊸l refl (cong-scut2 f₁ p)
cong-scut2 (⊸c Δ₀ f f₁) p = ⊸c Δ₀ refl (cong-scut2 f₁ p)


cong-ccut1 Δ₀ {Δ'} {A} (base {Γ = Γ} g refl eq2) refl eq with cases++-lmap ` Δ₀ (A ∷ Δ') Γ eq2
cong-ccut1 ._ (base g refl eq2) refl eq | Λ₁ , X ∷ Λ₂ , refl , refl , refl = cong-ccut-b2 Λ₁ g eq
cong-ccut1 Δ₀ (uf g) r p with cases∷ Δ₀ r
cong-ccut1 {nothing} .[] (uf g) refl p | inj₁ (refl , refl , refl) = cong-scut1 p
cong-ccut1 {just x} .[] (uf g) refl p | inj₁ (refl , refl , refl) = uf (cong-scut1 p)
... | inj₂ (Γ₀ , refl , refl) = uf (cong-ccut1 Γ₀ g refl p)
cong-ccut1 Δ₀ (⊸r g) refl p = ⊸r (cong-ccut1 Δ₀ g refl p)
cong-ccut1 Δ₀ {Δ'} (⊸l {Γ} {Δ} g g₁) r p with cases++ Δ₀ Γ Δ' Δ r
cong-ccut1 Δ₀ {.(Γ₀ ++ Δ)} (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl p | inj₁ (Γ₀ , refl , refl) = ⊸l (cong-ccut1 Δ₀ g refl p) refl
cong-ccut1 .(Γ ++ Γ₀) {Δ'} (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) refl p | inj₂ (Γ₀ , refl , refl) = ⊸l refl (cong-ccut1  Γ₀ g₁ refl p)
cong-ccut1 Δ₀ {Δ'} (⊸c Δ₁ {Γ} {Δ₂} g g₁) r p with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (_ ∷ Δ') (sym r)
cong-ccut1 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} (⊸c Δ₁ {Γ} {Δ₂} g g₁) r p | inj₁ (Γ₀ , refl , s) with cases++ Γ₀ Γ Δ' Δ₂ s
cong-ccut1 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {.(Γ₀' ++ Δ₂)} (⊸c Δ₁ {.(Γ₀ ++ _ ∷ Γ₀')} {Δ₂} g g₁) refl p | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (cong-ccut1 Γ₀ g refl p) refl
cong-ccut1 .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') {Δ'} (⊸c Δ₁ {Γ} {.(Γ₀' ++ _ ∷ Δ')} g g₁) refl p | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ refl (cong-ccut1 (Δ₁ ++ _ ∷ Γ₀') g₁ refl p)
cong-ccut1 Δ₀ {.(Γ ++ Δ₂)} (⊸c .Δ₀ {Γ} {Δ₂} g g₁) refl p | inj₂ ([] , refl , refl) = cong-pr-ccut1 Δ₀ p g g₁
cong-ccut1 {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₂)} (⊸c .(Δ₀ ++ A ∷ Γ₀) {Γ} {Δ₂} g g₁) refl p | inj₂ (A ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ asCxt S Γ₁ ++ Γ₀) refl (cong-ccut1 Δ₀ g₁ refl p) 

cong-ccut2 Δ₀ r refl = refl
cong-ccut2 Δ₀ r (~ p) = ~ cong-ccut2 Δ₀ r p
cong-ccut2 Δ₀ r (p ∙ p₁) = cong-ccut2 Δ₀ r p ∙ cong-ccut2 Δ₀ r p₁
cong-ccut2 Δ₀ r (uf p) with cases∷ Δ₀ r
cong-ccut2 {nothing} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = cong-scut2 f p
cong-ccut2 {just x} .[] {f = f} r (uf p) | inj₁ (refl , refl , refl) = uf (cong-scut2 f p)
... | inj₂ (Γ₀ , refl , refl) = uf (cong-ccut2 Γ₀ refl p)
cong-ccut2 Δ₀ refl (⊸r p) = ⊸r (cong-ccut2 Δ₀ refl p)
cong-ccut2 Δ₀ {Δ'} r (⊸l {Γ} {Δ} p p₁) with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ {.(Γ₀ ++ Δ)} refl (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} p p₁) | inj₁ (Γ₀ , refl , refl) =
  ⊸l (cong-ccut2 Δ₀ refl p) p₁
cong-ccut2 .(Γ ++ Γ₀) {Δ'} refl (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} p p₁) | inj₂ (Γ₀ , refl , refl) =
  ⊸l p (cong-ccut2 Γ₀ refl p₁)
cong-ccut2 Δ₀ {Δ'} r (⊸c {Γ = Γ} Δ₁ {Δ₂} p p₁) with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (_ ∷ Δ') (sym r)
cong-ccut2 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} r (⊸c {Γ = Γ} Δ₁ {Δ₂} p p₁) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
cong-ccut2 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {.(Γ₀' ++ Δ₂)} refl (⊸c {Γ = .(Γ₀ ++ _ ∷ Γ₀')} Δ₁ {Δ₂} p p₁) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (cong-ccut2 Γ₀ refl p) p₁
cong-ccut2 .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') {Δ'} refl (⊸c {Γ = Γ} Δ₁ {.(Γ₀' ++ _ ∷ Δ')} p p₁) | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ p (cong-ccut2 (Δ₁ ++ _ ∷ Γ₀') refl p₁)
cong-ccut2 _ {.(Γ ++ Δ₂)} {f = f} refl (⊸c {Γ = Γ} Δ₁ {Δ₂} {g = g} {f'} p p₁) | inj₂ ([] , refl , refl) = cong-pr-ccut2 Δ₁ f p f' ∙ cong-pr-ccut3 Δ₁ f g p₁
cong-ccut2 {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₂)} refl (⊸c {Γ = Γ} .(Δ₀ ++ x ∷ Γ₀) {Δ₂} p p₁) | inj₂ (x ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ asCxt S Γ₁ ++ Γ₀) p (cong-ccut2 Δ₀ refl p₁)
cong-ccut2 Δ₀ r ⊸ruf with cases∷ Δ₀ r
cong-ccut2 {nothing} .[] {f = f} refl (⊸ruf {f = f₁}) | inj₁ (refl , refl , refl) = ~ scut⊸r f f₁
cong-ccut2 {just x} .[] {f = f} refl (⊸ruf {f = f₁}) | inj₁ (refl , refl , refl) = ⊸ruf ∙ uf (~ scut⊸r f f₁) 
cong-ccut2 .(_ ∷ Γ₀) refl ⊸ruf | inj₂ (Γ₀ , refl , refl) = ⊸ruf
cong-ccut2 Δ₀ {Δ'} r (⊸r⊸l {Γ} {Δ}) with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ {.(Γ₀ ++ Δ)} {A} refl (⊸r⊸l {.(Δ₀ ++ A ∷ Γ₀)} {Δ} {C = C}) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ++ C ∷ []) A = ⊸r⊸l
cong-ccut2 {S}{Γ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A} refl (⊸r⊸l {Γ} {.(Γ₀ ++ A ∷ Δ')} {C = C}) | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ (Δ' ++ C ∷ []) A = ⊸r⊸l {Γ}{Γ₀ ++ asCxt S Γ₁ ++ Δ'}
cong-ccut2 Δ₀ {Δ'} {A} r (⊸r⊸c {Γ = Γ} {Δ₁} {Δ₂}) with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A ∷ Δ') (sym r)
cong-ccut2 .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A} r (⊸r⊸c {Γ = Γ} {Δ₁} {Δ₂}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ₀) {.(Γ₀' ++ Δ₂)} {A} refl (⊸r⊸c {Γ = .(Γ₀ ++ A ∷ Γ₀')} {Δ₁} {Δ₂} {A₁} {B} {C}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₁ Γ₀ (A ∷ Γ₀' ++ Δ₂ ++ C ∷ []) (A₁ ⊸ B) | cases++-inj₁ Γ₀ Γ₀' (Δ₂ ++ C ∷ []) A = ⊸r⊸c
cong-ccut2 {S}{Γ = Γ₁} .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Γ₀') {Δ'} {A} refl (⊸r⊸c {Γ = Γ} {Δ₁} {.(Γ₀' ++ A ∷ Δ')} {A₁} {B} {C}) | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) 
  rewrite cases++-inj₁ Δ₁ (Γ ++ Γ₀') (A ∷ Δ' ++ C ∷ []) (A₁ ⊸ B) | cases++-inj₂ Γ₀' Γ (Δ' ++ C ∷ []) A = ⊸r⊸c {_}{_}{Δ₁}{Γ₀' ++ asCxt S Γ₁ ++ Δ'}
cong-ccut2 Δ₀ {.(Γ ++ Δ₂)} {.(A ⊸ B)} {f = f} refl (⊸r⊸c {Γ = Γ} {.Δ₀} {Δ₂} {A} {B} {C} {f = f₁} {g}) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ C ∷ []) (A ⊸ B) = ~ (pr-ccut⊸r Δ₀ f f₁ g)
cong-ccut2 {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ A ⊸ B ∷ Γ ++ Δ₂)} {.x} refl (⊸r⊸c {Γ = Γ} {.(Δ₀ ++ x ∷ Γ₀)} {Δ₂} {A} {B} {C}) | inj₂ (x ∷ Γ₀ , refl , refl) 
  rewrite cases++-inj₂ (x ∷ Γ₀) Δ₀ (Γ ++ Δ₂ ++ C ∷ []) (A ⊸ B) = ⊸r⊸c {_}{_}{Δ₀ ++ asCxt S Γ₁ ++ Γ₀} 
cong-ccut2 Δ₀ r ⊸cuf with cases∷ Δ₀ r
cong-ccut2 {nothing} {Γ = Γ} .[] {f = f} refl (⊸cuf {Δ₀ = Δ₀} {f = f₁} {g}) | inj₁ (refl , refl , refl) = ~ scut⊸c Δ₀ f f₁ g 
cong-ccut2 {just x} {Γ = Γ} .[] {f = f} refl (⊸cuf {Δ₀ = Δ₀} {f = f₁} {g}) | inj₁ (refl , refl , refl) = ⊸cuf {_}{Γ ++ Δ₀} ∙ uf (~ scut⊸c Δ₀ f f₁ g) 
cong-ccut2 .(_ ∷ Γ₀) r ⊸cuf | inj₂ (Γ₀ , p , refl) with inj∷ (sym r)
cong-ccut2 .(_ ∷ Γ₀) {Δ'} {A} r (⊸cuf {Γ} {Δ₀ = Δ₀} {Δ₁ = Δ₁}) | inj₂ (Γ₀ , p , refl) | refl , q with cases++ Δ₀ Γ₀ (Γ ++ Δ₁) (A ∷ Δ') q
cong-ccut2 .(_ ∷ Δ₀ ++ _ ⊸ _ ∷ Γ₀') {Δ'} {A} r (⊸cuf {Γ} {Δ₀} {Δ₁}) | inj₂ (.(Δ₀ ++ _ ⊸ _ ∷ Γ₀') , p , refl) | refl , q | inj₁ (Γ₀' , refl , q') with cases++ Γ₀' Γ Δ' Δ₁ q'
cong-ccut2 .(_ ∷ Δ₀ ++ A₁ ⊸ B ∷ Γ₀') {.(Γ₀'' ++ Δ₁)} {A} refl (⊸cuf {.(Γ₀' ++ A ∷ Γ₀'')} {Δ₀} {Δ₁} {A₁} {B = B}) | inj₂ (.(Δ₀ ++ A₁ ⊸ B ∷ Γ₀') , refl , refl) | refl , refl | inj₁ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (A ∷ Γ₀'' ++ Δ₁) (A₁ ⊸ B) | cases++-inj₁ Γ₀' Γ₀'' Δ₁ A
    = ⊸cuf
cong-ccut2 .(_ ∷ Δ₀ ++ A ⊸ B ∷ Γ ++ Γ₀'') {Δ'} {` x} refl (⊸cuf {Γ} {Δ₀} {.(Γ₀'' ++ ` x ∷ Δ')} {A} {B = B}) | inj₂ (.(Δ₀ ++ A ⊸ B ∷ Γ ++ Γ₀'') , refl , refl) | refl , refl | inj₁ (.(Γ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀'') (` x ∷ Δ') (A ⊸ B) | cases++-inj₂ Γ₀'' Γ Δ' (` x) = ⊸cuf
cong-ccut2 .(_ ∷ Δ₀ ++ A₂ ⊸ B ∷ Γ ++ Γ₀'') {Δ'} {A ⊸ A₁} refl (⊸cuf {Γ} {Δ₀} {.(Γ₀'' ++ A ⊸ A₁ ∷ Δ')} {A₂} {B = B}) | inj₂ (.(Δ₀ ++ A₂ ⊸ B ∷ Γ ++ Γ₀'') , refl , refl) | refl , refl | inj₁ (.(Γ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl) rewrite cases++-inj₁ Δ₀ (Γ ++ Γ₀'') (A ⊸ A₁ ∷ Δ') (A₂ ⊸ B) | cases++-inj₂ Γ₀'' Γ Δ' (A ⊸ A₁) = ⊸cuf
cong-ccut2 .(_ ∷ Γ₀) {.(Γ ++ Δ₁)} {.(A ⊸ B)} {f = f} refl (⊸cuf {Γ} {.Γ₀} {Δ₁} {A} {B = B} {f = f₁} {g}) | inj₂ (Γ₀ , refl , refl) | refl , refl | inj₂ ([] , refl , refl)  
  rewrite cases++-inj₂ [] Γ₀ (Γ ++ Δ₁) (A ⊸ B) = pr-ccutuf Γ₀ f f₁ g
cong-ccut2 {S} {Γ = Γ₁} .(_ ∷ Γ₀) {.(Γ₀' ++ A ⊸ B ∷ Γ ++ Δ₁)} {.x} refl (⊸cuf {Γ} {.(Γ₀ ++ x ∷ Γ₀')} {Δ₁} {A} {B = B}) | inj₂ (Γ₀ , refl , refl) | refl , refl | inj₂ (x ∷ Γ₀' , refl , refl) 
  rewrite cases++-inj₂ (x ∷ Γ₀') Γ₀ (Γ ++ Δ₁) (A ⊸ B) = ⊸cuf {Δ₀ = Γ₀ ++ asCxt S Γ₁ ++ Γ₀'}
cong-ccut2 Δ₀ {Δ'} {A} r (⊸cuf2 {Γ} {Δ}) with cases++ [] Δ₀ (Γ ++ Δ) (A ∷ Δ') (sym r)
cong-ccut2 .(_ ⊸ _ ∷ Γ₀) {Δ'} {A} r (⊸cuf2 {Γ} {Δ}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ q
cong-ccut2 .(_ ⊸ _ ∷ Γ₀) {.(Γ₀' ++ Δ)} {A} refl (⊸cuf2 {.(Γ₀ ++ A ∷ Γ₀')} {Δ}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Γ₀ Γ₀' Δ A = ⊸cuf2
cong-ccut2 .(_ ⊸ _ ∷ Γ ++ Γ₀') {Δ'} {A} refl (⊸cuf2 {Γ} {.(Γ₀' ++ A ∷ Δ')}) | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ Γ₀' Γ Δ' A = ⊸cuf2 
cong-ccut2 {nothing} [] {.(Γ ++ Δ)} {.(_ ⊸ _)} {f = f} refl (⊸cuf2 {Γ} {Δ} {f = f₁} {g}) | inj₂ (.[] , refl , refl) = pr-ccutuf2-n f f₁ g
cong-ccut2 {just x} [] {.(Γ ++ Δ)} {.(_ ⊸ _)} {f = f} refl (⊸cuf2 {Γ} {Δ} {f = f₁} {g}) | inj₂ (.[] , refl , refl) = pr-ccutuf2-j f f₁ g
cong-ccut2 Δ₀ {Δ'} {A} r (⊸c⊸l {Γ} {Δ} {Γ'} {Λ} {A' = A'} {B'}) with cases++ (Γ ++ Δ) Δ₀ (Γ' ++ Λ) (A ∷ Δ') (sym r)
cong-ccut2 .(Γ ++ Δ ++ A' ⊸ B' ∷ Γ₀) {Δ'} {A} r (⊸c⊸l {Γ} {Δ} {Γ'} {Λ} {A' = A'} {B'}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ' Δ' Λ q
cong-ccut2 .(Γ ++ Δ ++ A' ⊸ B' ∷ Γ₀) {.(Γ₀' ++ Λ)} {A} refl (⊸c⊸l {Γ} {Δ} {.(Γ₀ ++ A ∷ Γ₀')} {Λ} {A' = A'} {B'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ (Δ ++ A' ⊸ B' ∷ Γ₀) Γ (Γ₀' ++ Λ) A | cases++-inj₁ Δ Γ₀ (A ∷ Γ₀' ++ Λ) (A' ⊸ B') | cases++-inj₁ Γ₀ Γ₀' Λ A = ⊸c⊸l
cong-ccut2 .(Γ ++ Δ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') {Δ'} {A} refl (⊸c⊸l {Γ} {Δ} {Γ'} {.(Γ₀' ++ A ∷ Δ')} {A' = A'} {B'}) | inj₁ (.(Γ' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₂ (Δ ++ B' ∷ Γ₀') Γ Δ' A | cases++-inj₂ (Δ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') Γ Δ' A | cases++-inj₁ Δ (Γ' ++ Γ₀') (A ∷ Δ') (A' ⊸ B') | cases++-inj₂ Γ₀' Γ' Δ' A = ⊸c⊸l
cong-ccut2 .(Γ ++ Δ) {.(Γ' ++ Λ)} {.(A' ⊸ B')} {f = f} refl (⊸c⊸l {Γ} {Δ} {Γ'} {Λ} {A' = A'} {B'} {f = f₁} {f'} {g}) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₂ Δ Γ (Γ' ++ Λ) (A' ⊸ B') | cases++-inj₂ [] Δ (Γ' ++ Λ) (A' ⊸ B') = pr-ccut⊸l1 Δ f f' f₁ g
cong-ccut2 Δ₀ {.(Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Λ)} r (⊸c⊸l {Γ} {Δ} {Γ'} {Λ} {A' = A'} {B'}) | inj₂ (D ∷ Γ₀ , refl , q) with cases++ Δ₀ Γ Γ₀ Δ q
cong-ccut2 Δ₀ {.((Γ₀' ++ Δ) ++ A' ⊸ B' ∷ Γ' ++ Λ)} {.D} refl (⊸c⊸l {.(Δ₀ ++ D ∷ Γ₀')} {Δ} {Γ'} {Λ} {A' = A'} {B'}) | inj₂ (D ∷ .(Γ₀' ++ Δ) , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Δ ++ B' ∷ Λ) D | cases++-inj₁ Δ₀ Γ₀' (Δ ++ A' ⊸ B' ∷ Γ' ++ Λ) D = ⊸c⊸l
cong-ccut2 {S} {Γ = Γ₁} .(Γ ++ Γ₀') {.(Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Λ)} {.D} refl (⊸c⊸l {Γ} {.(Γ₀' ++ D ∷ Γ₀)} {Γ'} {Λ} {A' = A'} {B'}) | inj₂ (D ∷ Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) 
  rewrite cases++-inj₂ Γ₀' Γ (Γ₀ ++ B' ∷ Λ) D | cases++-inj₂ Γ₀' Γ (Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Λ) D | cases++-inj₂ (D ∷ Γ₀) Γ₀' (Γ' ++ Λ) (A' ⊸ B') = ⊸c⊸l {Δ = Γ₀' ++ asCxt S Γ₁ ++ Γ₀}
cong-ccut2 Δ₀ {Δ'} {A} r (⊸c⊸l2 {Γ} {Δ} {Γ'} {Λ}) with cases++ Δ Δ₀ (Γ' ++ Λ ++ Γ) (A ∷ Δ') (sym r)
cong-ccut2 .(Δ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A} r (⊸c⊸l2 {Γ} {Δ} {Γ'} {Λ}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ' Δ' (Λ ++ Γ) q
cong-ccut2 .(Δ ++ A' ⊸ B' ∷ Γ₀) {.(Γ₀' ++ Λ ++ Γ)} {A} refl (⊸c⊸l2 {Γ} {Δ} {.(Γ₀ ++ A ∷ Γ₀')} {Λ} {A' = A'} {B'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ (Δ ++ A' ⊸ B' ∷ Γ₀) (Γ₀' ++ Λ) Γ A | cases++-inj₁ Δ Γ₀ (A ∷ Γ₀' ++ Λ) (A' ⊸ B') | cases++-inj₁ Γ₀ Γ₀' Λ A = ⊸c⊸l2
cong-ccut2 .(Δ ++ _ ⊸ _ ∷ Γ' ++ Γ₀') {Δ'} {A} r (⊸c⊸l2 {Γ} {Δ} {Γ'} {Λ}) | inj₁ (.(Γ' ++ Γ₀') , refl , q) | inj₂ (Γ₀' , p , refl) with cases++ Γ₀' Λ Δ' Γ p
cong-ccut2 .(Δ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') {.(Γ₀ ++ Γ)} {A} refl (⊸c⊸l2 {Γ} {Δ} {Γ'} {.(Γ₀' ++ A ∷ Γ₀)} {A' = A'} {B'}) | inj₁ (.(Γ' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₁ (Δ ++ B' ∷ Γ₀') Γ₀ Γ A | cases++-inj₁ (Δ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') Γ₀ Γ A | cases++-inj₁ Δ (Γ' ++ Γ₀') (A ∷ Γ₀) (A' ⊸ B') | cases++-inj₂ Γ₀' Γ' Γ₀ A = ⊸c⊸l2
cong-ccut2 .(Δ ++ A' ⊸ B' ∷ Γ' ++ Λ ++ Γ₀) {Δ'} {A} refl (⊸c⊸l2 {.(Γ₀ ++ A ∷ Δ')} {Δ} {Γ'} {Λ} {A' = A'} {B'}) | inj₁ (.(Γ' ++ Λ ++ Γ₀) , refl , refl) | inj₂ (.(Λ ++ Γ₀) , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ (Δ ++ B' ∷ Λ) Δ' A | cases++-inj₂ Γ₀ (Δ ++ A' ⊸ B' ∷ Γ' ++ Λ) Δ' A = ⊸c⊸l2
cong-ccut2 Δ₀ {.(Γ' ++ Λ ++ Γ)} {.(A' ⊸ B')} {f = f} refl (⊸c⊸l2 {Γ} {.Δ₀} {Γ'} {Λ} {A' = A'} {B'} {f = f₁} {f'} {g}) | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ' ++ Λ) Γ (A' ⊸ B') | cases++-inj₂ [] Δ₀ (Γ' ++ Λ) (A' ⊸ B') = pr-ccut⊸l2 Δ₀ f f' f₁ g
cong-ccut2 {S} {Γ = Γ₁} Δ₀ {.(Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Λ ++ Γ)} {.x} refl (⊸c⊸l2 {Γ} {.(Δ₀ ++ x ∷ Γ₀)} {Γ'} {Λ} {A' = A'} {B'}) | inj₂ (x ∷ Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Γ₀ ++ B' ∷ Λ) Γ x | cases++-inj₁ Δ₀ (Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Λ) Γ x | cases++-inj₂ (x ∷ Γ₀) Δ₀ (Γ' ++ Λ) (A' ⊸ B') = ⊸c⊸l2 {_}{(Δ₀ ++ asCxt S Γ₁ ++ Γ₀)}
cong-ccut2 Δ₀ {Δ'} {A} r (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B}) with cases++ (Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₂) Δ₀ (Γ' ++ Δ₃) (A ∷ Δ') (sym r)
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₂ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A} r (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ' Δ' Δ₃ q
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ₀) {.(Γ₀' ++ Δ₃)} {A} refl (⊸c⊸c {Γ = Γ} {.(Γ₀ ++ A ∷ Γ₀')} {Δ₁} {Δ₂} {Δ₃} {A₁} {B} {A'} {B'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ₀)  (A ∷ Γ₀' ++ Δ₃) (A₁ ⊸ B) | cases++-inj₂ (Δ₂ ++ A' ⊸ B' ∷ Γ₀) Γ (Γ₀' ++ Δ₃) A | cases++-inj₁ (Δ₁ ++ B ∷ Δ₂) Γ₀ (A ∷ Γ₀' ++ Δ₃) (A' ⊸ B') | cases++-inj₁ Γ₀ Γ₀' Δ₃ A =   ⊸c⊸c
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') {Δ'} {A} refl (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {.(Γ₀' ++ A ∷ Δ')} {A₁} {B} {A'} {B'}) | inj₁ (.(Γ' ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂ ++ B' ∷ Γ₀') (A ∷ Δ') (A₁ ⊸ B) | cases++-inj₁ Δ₁ (Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') (A ∷ Δ') (A₁ ⊸ B) | cases++-inj₂ (Δ₂ ++ B' ∷ Γ₀') Γ Δ' A | cases++-inj₂ (Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Γ₀') Γ Δ' A | cases++-inj₁ (Δ₁ ++ B ∷ Δ₂) (Γ' ++ Γ₀') (A ∷ Δ') (A' ⊸ B') | cases++-inj₂ Γ₀' Γ' Δ' A = ⊸c⊸c
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Δ₂) {.(Γ' ++ Δ₃)} {.(A' ⊸ B')} {f = f} refl (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B} {A'} {B'} {f = f₁} {f'} {g}) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂) (A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B)  | cases++-inj₂ Δ₂ Γ (Γ' ++ Δ₃) (A' ⊸ B') | cases++-inj₂ [] (Δ₁ ++ B ∷ Δ₂) (Γ' ++ Δ₃) (A' ⊸ B') = pr-ccut⊸c11 Δ₁ f f' f₁ g
cong-ccut2 Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ' ++ Δ₃)} {.x} r (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B}) | inj₂ (x ∷ Γ₀ , refl , q) with cases++ Δ₁ Δ₀ ( Γ ++ Δ₂) (x ∷ Γ₀) (sym q)
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ₀') {.(Γ₀ ++ _ ⊸ _ ∷ Γ' ++ Δ₃)} {.x} r (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B}) | inj₂ (x ∷ Γ₀ , refl , q) | inj₁ (Γ₀' , refl , q') with cases++ Γ₀' Γ Γ₀ Δ₂ q'
cong-ccut2 .(Δ₁ ++ A₁ ⊸ B ∷ Γ₀') {.((Γ₀'' ++ Δ₂) ++ A' ⊸ B' ∷ Γ' ++ Δ₃)} {.x} refl (⊸c⊸c {Γ = .(Γ₀' ++ x ∷ Γ₀'')} {Γ'} {Δ₁} {Δ₂} {Δ₃} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ .(Γ₀'' ++ Δ₂) , refl , refl) | inj₁ (Γ₀' , refl , refl) | inj₁ (Γ₀'' , refl , refl)
  rewrite cases++-inj₁ Δ₁ Γ₀' (x ∷ Γ₀'' ++ Δ₂ ++ B' ∷ Δ₃) (A₁ ⊸ B) | cases++-inj₁ Δ₁ Γ₀' (x ∷ Γ₀'' ++ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B) | cases++-inj₁ Γ₀' Γ₀'' (Δ₂ ++ B' ∷ Δ₃) x | cases++-inj₁ Γ₀' Γ₀'' (Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) x  = ⊸c⊸c
cong-ccut2 {S}{Γ = Γ₁} .(Δ₁ ++ A₁ ⊸ B ∷ Γ ++ Γ₀'') {.(Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Δ₃)} {.x} refl (⊸c⊸c {Γ = Γ} {Γ'} {Δ₁} {.(Γ₀'' ++ x ∷ Γ₀)} {Δ₃} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ Γ₀ , refl , refl) | inj₁ (.(Γ ++ Γ₀'') , refl , refl) | inj₂ (Γ₀'' , refl , refl)
  rewrite cases++-inj₁ Δ₁ (Γ ++ Γ₀'') (x ∷ Γ₀ ++ B' ∷ Δ₃) (A₁ ⊸ B) | cases++-inj₁ Δ₁ (Γ ++ Γ₀'') (x ∷ Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B) | cases++-inj₂ Γ₀'' Γ (Γ₀ ++ B' ∷ Δ₃) x | cases++-inj₂ Γ₀'' Γ (Γ₀ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) x | cases++-inj₂ (x ∷ Γ₀) (Δ₁ ++ B ∷ Γ₀'') (Γ' ++ Δ₃) (A' ⊸ B') = ⊸c⊸c {Δ₁ = Γ₀'' ++ asCxt S Γ₁ ++ Γ₀}
cong-ccut2 Δ₀ {.((Γ ++ Δ₂) ++ A' ⊸ B' ∷ Γ' ++ Δ₃)} {.(A₁ ⊸ B)} {f = f} refl (⊸c⊸c {Γ = Γ} {Γ'} {.Δ₀} {Δ₂} {Δ₃} {A₁} {B} {A'} {B'} {f = f₁} {f'} {g}) | inj₂ (.(A₁ ⊸ B) ∷ .(Γ ++ Δ₂) , refl , refl) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ B' ∷ Δ₃) (A₁ ⊸ B) | cases++-inj₂ [] Δ₀ (Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B) = ~ pr-ccut⊸c12 Δ₀ f f' f₁ g
cong-ccut2 {S}{Γ = Γ₁} Δ₀ {.((Γ₀' ++ A₁ ⊸ B ∷ Γ ++ Δ₂) ++ A' ⊸ B' ∷ Γ' ++ Δ₃)} {.x} refl (⊸c⊸c {Γ = Γ} {Γ'} {.(Δ₀ ++ x ∷ Γ₀')} {Δ₂} {Δ₃} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ .(Γ₀' ++ A₁ ⊸ B ∷ Γ ++ Δ₂) , refl , refl) | inj₂ (x ∷ Γ₀' , refl , refl)
  rewrite cases++-inj₂ (x ∷ Γ₀') Δ₀ (Γ ++ Δ₂ ++ B' ∷ Δ₃) (A₁ ⊸ B) | cases++-inj₂ (x ∷ Γ₀') Δ₀ (Γ ++ Δ₂ ++ A' ⊸ B' ∷ Γ' ++ Δ₃) (A₁ ⊸ B) | cases++-inj₂ (x ∷ Γ₀' ++ B ∷ Δ₂) Δ₀ (Γ' ++ Δ₃) (A' ⊸ B') = ⊸c⊸c {Δ₀ = Δ₀ ++ asCxt S Γ₁ ++ Γ₀'}
cong-ccut2 Δ₀ {Δ'} {A} r (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) with cases++ (Δ₃ ++ A₁ ⊸ B' ∷ Δ₁) Δ₀ (Γ ++ Δ₂ ++ Δ₄) (A ∷ Δ') (sym r)
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁ ++ A' ⊸ B ∷ Γ₀) {Δ'} {A} r (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' (Δ₂ ++ Δ₄) q
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁ ++ A' ⊸ B ∷ Γ₀) {.(Γ₀' ++ Δ₂ ++ Δ₄)} {A} refl (⊸c⊸c2 {Γ = .(Γ₀ ++ A ∷ Γ₀')} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₃ (Δ₁ ++ A' ⊸ B ∷ Γ₀) (A ∷ Γ₀' ++ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ (Δ₁ ++ A' ⊸ B ∷ Γ₀) (Γ₀' ++ Δ₂) Δ₄ A | cases++-inj₁ Δ₁ Γ₀ (A ∷ Γ₀' ++ Δ₂) (A' ⊸ B) | cases++-inj₁ Γ₀ Γ₀' Δ₂ A = ⊸c⊸c2
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁ ++ A' ⊸ B ∷ Γ ++ Γ₀') {Δ'} {A} r (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₁ (.(Γ ++ Γ₀') , refl , q) | inj₂ (Γ₀' , p' , refl) with cases++ Γ₀' Δ₂ Δ' Δ₄ p'
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁ ++ A' ⊸ B ∷ Γ ++ Γ₀') {.(Γ₀ ++ Δ₄)} {A} refl (⊸c⊸c2 {Γ = Γ} {Δ₁} {.(Γ₀' ++ A ∷ Γ₀)} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₃ (Δ₁ ++ B ∷ Γ₀') (A ∷ Γ₀ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ Δ₃  (Δ₁ ++ A' ⊸ B ∷ Γ ++ Γ₀') (A ∷ Γ₀ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ (Δ₁ ++ B ∷ Γ₀') Γ₀ Δ₄ A | cases++-inj₁ (Δ₁ ++ A' ⊸ B ∷ Γ ++ Γ₀') Γ₀ Δ₄ A | cases++-inj₁ Δ₁ (Γ ++ Γ₀') (A ∷ Γ₀) (A' ⊸ B) | cases++-inj₂ Γ₀' Γ Γ₀ A = ⊸c⊸c2
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Γ₀) {Δ'} {A} refl (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {.(Γ₀ ++ A ∷ Δ')} {A₁} {B} {A'} {B'}) | inj₁ (.(Γ ++ Δ₂ ++ Γ₀) , refl , refl) | inj₂ (.(Δ₂ ++ Γ₀) , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₃ (Δ₁ ++ B ∷ Δ₂ ++ Γ₀) (A ∷ Δ') (A₁ ⊸ B') | cases++-inj₁ Δ₃ (Δ₁ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Γ₀) (A ∷ Δ') (A₁ ⊸ B') | cases++-inj₂ Γ₀ (Δ₁ ++ B ∷ Δ₂) Δ' A | cases++-inj₂ Γ₀ (Δ₁ ++ A' ⊸ B ∷ Γ ++ Δ₂) Δ' A = ⊸c⊸c2
cong-ccut2 .(Δ₃ ++ A₁ ⊸ B' ∷ Δ₁) {.(Γ ++ Δ₂ ++ Δ₄)} {.(A' ⊸ B)} {f = f} refl (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'} {f = f₁} {f'} {g}) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₁ Δ₃ Δ₁ (A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ Δ₁ (Γ ++ Δ₂) Δ₄ (A' ⊸ B) | cases++-inj₂ [] Δ₁ (Γ ++ Δ₂) (A' ⊸ B) = pr-ccut⊸c21 Δ₃ Δ₁ f f' f₁ g 
cong-ccut2 Δ₀ {.(Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄)} {.x} r (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ Γ₀ , refl , q) with cases++ Δ₃ Δ₀ Δ₁ (x ∷ Γ₀) (sym q)
cong-ccut2 {S}{Γ = Γ₁} .(Δ₃ ++ A₁ ⊸ B' ∷ Γ₀') {.(Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄)} {.x} refl (⊸c⊸c2 {Γ = Γ} {.(Γ₀' ++ x ∷ Γ₀)} {Δ₂} {Δ₃} {Δ₄} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₃ Γ₀' (x ∷ Γ₀ ++ B ∷ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ Δ₃ Γ₀' (x ∷ Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₁ Γ₀' (Γ₀ ++ B ∷ Δ₂) Δ₄ x | cases++-inj₁ Γ₀' (Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂) Δ₄ x | cases++-inj₂ (x ∷ Γ₀) Γ₀' (Γ ++ Δ₂) (A' ⊸ B) =  ⊸c⊸c2 {Δ₀ = Γ₀' ++ asCxt S Γ₁ ++ Γ₀}
cong-ccut2 Δ₀ {.(Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄)} {.(A₁ ⊸ B')} {f = f} refl (⊸c⊸c2 {Γ = Γ} {.Γ₀} {Δ₂} {.Δ₀} {Δ₄} {A₁} {B} {A'} {B'} {f = f₁} {f'} {g}) | inj₂ (.(A₁ ⊸ B') ∷ Γ₀ , refl , refl) | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₀ (Γ₀ ++ B ∷ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₂ [] Δ₀ (Γ₀ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄) (A₁ ⊸ B') = ~ pr-ccut⊸c22 Δ₀ Γ₀ f f' f₁ g 
cong-ccut2 {S}{Γ = Γ₁} Δ₀ {.((Γ₀' ++ A₁ ⊸ B' ∷ Δ₁) ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄)} {.x} refl (⊸c⊸c2 {Γ = Γ} {Δ₁} {Δ₂} {.(Δ₀ ++ x ∷ Γ₀')} {Δ₄} {A₁} {B} {A'} {B'}) | inj₂ (x ∷ .(Γ₀' ++ A₁ ⊸ B' ∷ Δ₁) , refl , refl) | inj₂ (.x ∷ Γ₀' , refl , refl)
  rewrite cases++-inj₂ (x ∷ Γ₀') Δ₀ (Δ₁ ++ B ∷ Δ₂ ++ Δ₄) (A₁ ⊸ B') | cases++-inj₂ (x ∷ Γ₀') Δ₀ (Δ₁ ++ A' ⊸ B ∷ Γ ++ Δ₂ ++ Δ₄) (A₁ ⊸ B') = ⊸c⊸c2 {Δ₂ = Δ₀ ++ asCxt S Γ₁ ++ Γ₀'}
cong-ccut2 Δ₀ r baseuf with cases∷ Δ₀ r
cong-ccut2 {nothing} .[] {f = f} refl (baseuf {f = f₁}) | inj₁ (refl , refl , refl) = ccut-b2-uf-b-n f f₁
cong-ccut2 {just x} .[] {f = f} refl (baseuf {f = f₁}) | inj₁ (refl , refl , refl) = ccut-b2-uf-b-j f f₁
cong-ccut2 .(` _ ∷ Γ₀) {Δ'} {A} r (baseuf {Γ}) | inj₂ (Γ₀ , p , refl) with cases++-lmap ` Γ₀ (A ∷ Δ') Γ (sym p)
cong-ccut2 .(` _ ∷ lmap ` Λ₁) {.(lmap ` Λ₂)} {.(` X)} {f = f} refl (baseuf {.(Λ₁ ++ X ∷ Λ₂)} {f = f₁}) | inj₂ (.(lmap ` Λ₁) , refl , refl) | Λ₁ , X ∷ Λ₂ , refl , refl , refl
  rewrite cases++-lmap-refl `  Λ₁ (X ∷ Λ₂) = ccut-b2-uf-b2 f f₁




cong-pr-ccut1 Δ₀ refl g h = refl
cong-pr-ccut1 Δ₀ (~ p) g h = ~ cong-pr-ccut1 Δ₀ p g h
cong-pr-ccut1 Δ₀ (p ∙ p₁) g h = cong-pr-ccut1 Δ₀ p g h ∙ cong-pr-ccut1 Δ₀ p₁ g h
cong-pr-ccut1 Δ₀ (uf p) g h = cong-pr-ccut1 Δ₀ p g h
cong-pr-ccut1 {Γ = Γ} Δ₀ (⊸r p) g h = cong-ccut1 Δ₀ h refl (cong-ccut2 Γ refl p)
cong-pr-ccut1 Δ₀ (⊸l p p₁) g h = ⊸c Δ₀ p (cong-pr-ccut1 Δ₀ p₁ g h)
cong-pr-ccut1 {S} Δ₀ (⊸c Δ₁ p p₁) g h = ⊸c (Δ₀ ++ asCxt S Δ₁) p (cong-pr-ccut1 Δ₀ p₁ g h )
cong-pr-ccut1 Δ₀ (⊸ruf {Γ}{f = f}) g h = ≡-to-≗ (ccut-uf Δ₀ (ccut Γ g f refl) h refl)
cong-pr-ccut1 Δ₀ {A = A} (⊸r⊸l {Γ} {Δ} {f = f} {g₁}) g h
  rewrite cases++-inj₂ Δ Γ [] A = ccut⊸l Δ₀ f (ccut Δ g g₁ refl) h refl
cong-pr-ccut1 {S} Δ₀ {A = A} (⊸r⊸c {Γ = Γ} {Δ₁} {Δ₂} {A₁} {B} {f = f} {g₁}) g h
  rewrite cases++-inj₁ Δ₁ (Γ ++ Δ₂) (A ∷ []) (A₁ ⊸ B) | cases++-inj₂ Δ₂ Γ [] A
    = ccut⊸c Δ₀ Δ₁ f (ccut (Δ₁ ++ B ∷ Δ₂) g g₁ refl) h refl
cong-pr-ccut1 Δ₀ ⊸cuf g h = refl
cong-pr-ccut1 Δ₀ ⊸cuf2 g h = refl
cong-pr-ccut1 Δ₀ ⊸c⊸l g h = ⊸c⊸c
cong-pr-ccut1 Δ₀ ⊸c⊸l2 g h = ⊸c⊸c2
cong-pr-ccut1 {S} Δ₀ (⊸c⊸c {Δ₀ = Δ₁}) g h = ⊸c⊸c {Δ₀ = Δ₀ ++ asCxt S Δ₁}
cong-pr-ccut1 {S} Δ₀ (⊸c⊸c2 {Δ₂ = Δ₂}) g h = ⊸c⊸c2 {Δ₂ = Δ₀ ++ asCxt S Δ₂}

cong-pr-ccut2 Δ₀ (uf f) p h = cong-pr-ccut2 Δ₀ f p h
cong-pr-ccut2 Δ₀ (⊸r {Γ = Γ} f) p h = cong-ccut1 Δ₀ h refl (cong-ccut1 Γ f refl p)
cong-pr-ccut2 Δ₀ (⊸l f f₁) p h = ⊸c Δ₀ refl (cong-pr-ccut2 Δ₀ f₁ p h)
cong-pr-ccut2 {S} Δ₀ (⊸c Δ₁ f f₁) p h = ⊸c (Δ₀ ++ asCxt S Δ₁) refl (cong-pr-ccut2 Δ₀ f₁ p h)

cong-pr-ccut3 Δ₀ (uf f) g p = cong-pr-ccut3 Δ₀ f g p
cong-pr-ccut3 Δ₀ (⊸r f) g p = cong-ccut2 Δ₀ refl p
cong-pr-ccut3 Δ₀ (⊸l f f₁) g p = ⊸c Δ₀ refl (cong-pr-ccut3 Δ₀ f₁ g p)
cong-pr-ccut3 {S} Δ₀ (⊸c Δ₁ f f₁) g p = ⊸c (Δ₀ ++ asCxt S Δ₁) refl (cong-pr-ccut3 Δ₀ f₁ g p)


pr-ccut⊸c22 Δ₀ Λ₀ (uf f) g h k = pr-ccut⊸c22 Δ₀ Λ₀ f g h k
pr-ccut⊸c22 {Γ = Γ} Δ₀ Λ₀ (⊸r f) g h k =
  cong-ccut1 Δ₀ k refl (ccut⊸c Γ Λ₀ g h f refl) ∙ ccut⊸c Δ₀ (Γ ++ Λ₀) g (ccut Γ h f refl) k refl
pr-ccut⊸c22 Δ₀ Λ₀ (⊸l {Γ} {Δ} f f₁) g h k =
  ⊸c Δ₀ refl (pr-ccut⊸c22 Δ₀ Λ₀ f₁ g h k) ∙ (~ ⊸c⊸c {Δ₁ = Δ ++ Λ₀})
pr-ccut⊸c22 {S} Δ₀ Λ₀ (⊸c Δ₁ {Δ₁ = Δ₂} f f₁) g h k = 
  ⊸c (Δ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸c22 Δ₀ Λ₀ f₁ g h k) ∙ (~ ⊸c⊸c {Δ₀ = Δ₀ ++ asCxt S Δ₁} {Δ₁ = Δ₂ ++ Λ₀})

cong-scut {g = g} p q = cong-scut1 p ∙ cong-scut2 g q             

cong-ccut Δ₀ {g = g} r p q = cong-ccut1 Δ₀ g r p  ∙ cong-ccut2 Δ₀ r q

