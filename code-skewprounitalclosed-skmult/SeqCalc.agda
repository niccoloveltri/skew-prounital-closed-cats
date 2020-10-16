{-# OPTIONS --rewriting  #-}

open import SkMults

module SeqCalc where

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

-- =======================================================================

-- Sequent calculus

-- -- (In addition to the conclusion, sequents have a stoup and a context.)

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  base : ∀ {T S Γ Δ Y} → T ∣ Γ ⊢b Y
    → S ≡ mmap ` T → Δ ≡ lmap ` Γ
    → S ∣ Δ ⊢ ` Y
  uf : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C 
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢ A → just B ∣ Δ ⊢ C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢ C
  ⊸c : {S : Stp} (Δ₀ : Cxt) {Γ Δ₁ : Cxt} {A B C : Fma}
    → nothing ∣ Γ ⊢ A → S ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C
    → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢ C

subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f


-- -- equality of derivations

infixl 20 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  uf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → uf f ≗ uf g
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'
  ⊸c : ∀{S Γ} Δ₀ {Δ₁}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : S ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸c Δ₀ f f' ≗ ⊸c Δ₀ g g'
  ⊸ruf : {Γ : Cxt}{A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (uf f) ≗ uf (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)
  ⊸r⊸c : {S : Stp} {Γ Δ₀ Δ₁ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : S ∣ Δ₀ ++ B ∷ Δ₁ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁} (⊸c Δ₀ f g) ≗ ⊸c Δ₀ f (⊸r g)
  ⊸cuf : {Γ Δ₀ Δ₁ : Cxt}{A A' B C : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just A' ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C}
    → ⊸c (A' ∷ Δ₀) f (uf g) ≗ uf (⊸c Δ₀ f g)
  ⊸cuf2 : {Γ Δ : Cxt}{A B C : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ⊢ C}
    → ⊸c [] f (uf g) ≗ uf (⊸l f g)
  ⊸c⊸l : {Γ Δ Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢ A} {f' : nothing ∣ Γ' ⊢ A'} {g : just B ∣ Δ ++ B' ∷ Λ ⊢ C} 
    → ⊸c (Γ ++ Δ) f' (⊸l f g) ≗ ⊸l f (⊸c Δ f' g)
  ⊸c⊸l2 : {Γ Δ Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ ++ B' ∷ Λ ⊢ A} {f' : nothing ∣ Γ'  ⊢ A'} {g : just B ∣ Γ ⊢ C} 
    → ⊸c Δ f' (⊸l f g) ≗ ⊸l (⊸c Δ f' f) g
  ⊸c⊸c : {S : Stp} {Γ Γ' Δ₀ Δ₁ Δ₂ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢ A} {f' : nothing ∣ Γ' ⊢ A'} {g : S ∣ Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂ ⊢ C} 
    → ⊸c (Δ₀ ++ _ ∷ Γ ++ Δ₁) f' (⊸c Δ₀ f g) ≗ ⊸c Δ₀ f (⊸c (Δ₀ ++ B ∷ Δ₁) f' g)
  ⊸c⊸c2 : {S : Stp} {Γ Δ₀ Δ₁ Δ₂ Δ₃ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ₀ ++ B ∷ Δ₁ ⊢ A} {f' : nothing ∣ Γ ⊢ A'} {g : S ∣ Δ₂ ++ B' ∷ Δ₃ ⊢ C} 
    → ⊸c (Δ₂ ++ _ ∷  Δ₀) f' (⊸c Δ₂ f g) ≗ ⊸c Δ₂ (⊸c Δ₀ f' f) g
  baseuf : ∀ {Γ X Y} {f : just X ∣ Γ ⊢b Y}
    → base (uf-b f) refl refl ≗ uf (base f refl refl)

≡-to-≗ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≗ f'
≡-to-≗ refl = refl

-- ====================================================================

-- -- equational reasoning sugar for ≗

infix 4 _≗'_
infix 1 proof≗_
infixr 2 _≗〈_〉_
infix 3 _qed≗

data _≗'_ {S  : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≗ g → f ≗' g

proof≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} {f g : S ∣ Γ ⊢ A} → f ≗' g → f ≗ g
proof≗ relto p = p

_≗〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗' h → f ≗' h 
_ ≗〈 p 〉 relto q = relto (p ∙ q)

_qed≗  :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) → f ≗' f
_qed≗ _ = relto refl

-- ====================================================================

-- ⊸r are invertible rules

⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ⊢ A ⊸ B → S ∣ Γ ++ A ∷ [] ⊢ B
⊸r-1 (uf f) = uf (⊸r-1 f)
⊸r-1 (⊸r f) = f
⊸r-1 (⊸l f g) = ⊸l f (⊸r-1 g)              
⊸r-1 (⊸c Δ₀ {Δ₁}{Δ₂} f g) =
  ⊸c Δ₀ f (⊸r-1 {Γ = Δ₀ ++ _ ∷ Δ₂} g)
  
⊸r-iso : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
  (f : S ∣ Γ ⊢ A ⊸ B) → ⊸r (⊸r-1 f) ≗ f
⊸r-iso (uf f) = ⊸ruf ∙ uf (⊸r-iso f)
⊸r-iso (⊸r f) = refl
⊸r-iso (⊸l f f₁) = ⊸r⊸l ∙ ⊸l refl (⊸r-iso f₁)
⊸r-iso (⊸c Δ₀ f g) = ⊸r⊸c ∙ ⊸c Δ₀ refl (⊸r-iso g)

cong⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              {f g : S ∣ Γ ⊢ A ⊸ B} → f ≗ g → ⊸r-1 f ≗ ⊸r-1 g
cong⊸r-1 refl = refl
cong⊸r-1 (~ p) = ~ (cong⊸r-1 p)
cong⊸r-1 (p ∙ p₁) = (cong⊸r-1 p) ∙ (cong⊸r-1 p₁)
cong⊸r-1 (uf p) = uf (cong⊸r-1 p)
cong⊸r-1 (⊸r p) = p
cong⊸r-1 (⊸l p p₁) = ⊸l p (cong⊸r-1 p₁)
cong⊸r-1 ⊸ruf = refl
cong⊸r-1 ⊸r⊸l = refl
cong⊸r-1 (⊸c Δ₀ {Δ₁} p q) = ⊸c Δ₀ p (cong⊸r-1 {Γ = Δ₀ ++ _ ∷ Δ₁} q)
cong⊸r-1 ⊸r⊸c = refl
cong⊸r-1 ⊸cuf = ⊸cuf
cong⊸r-1 ⊸c⊸l = ⊸c⊸l
cong⊸r-1 ⊸c⊸c = ⊸c⊸c
cong⊸r-1 ⊸cuf2 = ⊸cuf2
cong⊸r-1 ⊸c⊸l2 = ⊸c⊸l2
cong⊸r-1 ⊸c⊸c2 = ⊸c⊸c2


-- ====================================================================

-- Admissibility of ax

ax : ∀{A} → just A ∣ [] ⊢ A
ax {` X} = base ax-b refl refl
ax {A ⊸ B} = ⊸r (⊸l (uf ax) ax)


-- Admissibility of cut
-- -- (There are two kinds of cut: stoup cut and context cut.)

-- -- NB: notice that the type of ccut more general than the type of
-- -- ccut for the sequent calculus of skew prounital closed
-- -- categories on a *set*

ccut-b2 : ∀ {S T Γ} Δ₀ {Δ₁ X Y}
    → S ∣ Γ ⊢ ` X → T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y
    →  mmap ` T ∣ lmap ` Δ₀ ++ asCxt S Γ ++ lmap ` Δ₁ ⊢ ` Y
ccut-b2 Δ₀ (base f refl refl) g = base (ccut-b-gen Δ₀ f g) refl refl
ccut-b2 Δ₀ (uf f) g = ccut-b2 Δ₀ f g
ccut-b2 Δ₀ (⊸l f f') g = ⊸c (lmap ` Δ₀) f (ccut-b2 Δ₀ f' g)
ccut-b2 {S} Δ₀ (⊸c Δ₁ f f') g = ⊸c (lmap ` Δ₀ ++ asCxt S Δ₁) f (ccut-b2 Δ₀ f' g)


scut : ∀ {S Γ Δ A C} → S ∣ Γ ⊢ A → just A ∣ Δ ⊢ C → S ∣ Γ ++ Δ ⊢ C
ccut : ∀ {S T Γ Δ} Δ₀ {Δ₁ A C}
    → S ∣ Γ ⊢ A → T ∣ Δ ⊢ C → Δ ≡ Δ₀ ++ A ∷ Δ₁
    →  T ∣ Δ₀ ++ asCxt S Γ ++ Δ₁ ⊢ C
pr-ccut : ∀ {S T Γ Γ₁} Δ₀ {Δ₁ A B C}
    → S ∣ Γ ⊢ A ⊸ B → nothing ∣ Γ₁ ⊢ A → T ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C
    →  T ∣ Δ₀ ++ asCxt S Γ ++ Γ₁ ++ Δ₁ ⊢ C

pr-ccut Δ₀ (uf f) g h = pr-ccut Δ₀ f g h
pr-ccut {Γ = Γ} Δ₀ (⊸r f) g h = ccut Δ₀ (ccut Γ g f refl) h refl
pr-ccut Δ₀ (⊸l f f₁) g h = ⊸c Δ₀ f (pr-ccut Δ₀ f₁ g h)
pr-ccut {S} Δ₀ (⊸c Δ₁ f f₁) g h = ⊸c (Δ₀ ++ asCxt S Δ₁) f (pr-ccut Δ₀ f₁ g h)

scut (base {Γ = Γ} f refl refl) (base {just _} {Γ = Γ'} g refl refl) =
  base (scut-b f g) refl refl
scut (base f refl refl) (⊸r g) = ⊸r (scut (base f refl refl) g)
scut (base {Γ = Γ} f refl refl) (⊸c Δ₀ g g') =
  ⊸c (lmap ` Γ ++ Δ₀) g (scut (base f refl refl) g')
scut (uf f) g = uf (scut f g)
scut (⊸r {Γ = Γ} f) (⊸l g g') = scut (ccut Γ g f refl) g'
scut {Γ = Γ} (⊸r f) (⊸c Δ₀ g g') = ⊸c (Γ ++ Δ₀) g (scut (⊸r f) g')
scut (⊸r f) (⊸r g) = ⊸r (scut (⊸r f) g)
scut (⊸r f) (base {nothing} g () eqg)
scut (⊸r f) (base {just _} g () eqg)
scut (⊸l f f') g = ⊸l f (scut f' g)
scut (⊸c Δ₀ f f') g = ⊸c Δ₀ f (scut f' g)

ccut Δ₀ {Δ₁} f (base {Γ = Γ} g refl eq) refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Γ eq
ccut _ f (base g refl eq) refl | Γ₀ , X ∷ Δ₁ , refl , refl , refl = ccut-b2 Γ₀ f g
ccut Δ₀ f (uf g) eq with cases∷  Δ₀ eq
ccut {nothing} .[] f (uf g) eq | inj₁ (refl , refl , refl) = scut f g
ccut {just _} .[] f (uf g) eq | inj₁ (refl , refl , refl) = uf (scut f g)
ccut .(_ ∷ Δ₀) f (uf g) eq | inj₂ (Δ₀ , refl , refl) = uf (ccut Δ₀ f g refl)
ccut Δ₀ f (⊸r g) refl = ⊸r (ccut Δ₀ f g refl)
ccut Δ₀ {Δ'} f (⊸l {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
ccut Δ₀ f (⊸l g g') p | inj₁ (Γ₀ , r , refl) = ⊸l (ccut Δ₀ f g r) g'
ccut ._ f (⊸l g g') p | inj₂ (Γ₀ , refl , refl) = ⊸l g (ccut Γ₀ f g' refl)
ccut Δ₀ {Δ₁} f (⊸c Λ₀ {Γ} {Δ₂} g g') eq with cases++ Λ₀ Δ₀ (Γ ++ Δ₂) (_ ∷ Δ₁) (sym eq)
ccut ._ {Δ₁} f (⊸c Λ₀ {Γ} {Δ₂} g g') eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₁ Δ₂ q
ccut ._ f (⊸c Λ₀ g g') eq | inj₁ (Γ₀ , refl , q) | inj₁ (_ , refl , refl) =
  ⊸c Λ₀ (ccut Γ₀ f g refl) g'
ccut ._ f (⊸c Λ₀ g g') eq | inj₁ (._ , refl , q) | inj₂ (Γ₀ , refl , refl) =
  ⊸c Λ₀ g (ccut (Λ₀ ++ _ ∷ Γ₀) f g' refl)
ccut Δ₀ f (⊸c Λ₀ g g') refl | inj₂ ([] , refl , refl) = pr-ccut Λ₀ f g g'  
ccut {S} {Γ = Γ} Δ₀ f (⊸c ._ g g') eq | inj₂ (_ ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ asCxt S Γ ++ Γ₀) g (ccut Δ₀ f g' refl)



-- Many equalities disclosing the relation between cut and other
-- rules.


scut⊸r : {S : Stp} {Γ Δ : Cxt} {A B C : Fma}
  → (f : S ∣ Γ ⊢ A)
  → (g : just A ∣ Δ ++ B ∷ [] ⊢ C)
  → scut f (⊸r g) ≗ ⊸r (scut f g)
scut⊸r (base x refl refl) g = refl
scut⊸r (uf f) g = uf (scut⊸r f g) ∙ (~ ⊸ruf)
scut⊸r (⊸r f) g = refl
scut⊸r {Δ = Δ} (⊸l {Δ = Δ'} f f₁) g =
  ⊸l refl (scut⊸r f₁ g) ∙ (~ ⊸r⊸l {Δ = Δ' ++ Δ})
scut⊸r {Δ = Δ} (⊸c Δ₀ {Δ₁ = Δ₁} f f₁) g =
  ⊸c Δ₀ refl (scut⊸r f₁ g) ∙ (~ ⊸r⊸c {Δ₀ = Δ₀}{Δ₁ ++ Δ})

ccut-uf : {S : Stp} → {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A A' C : Fma} → 
               (f : just A' ∣ Γ ⊢ A)(g : S ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ') → 
          ccut Δ₀ (uf f) g r ≡ ccut Δ₀ f g r
ccut-uf Δ₀ {Δ'} {A} f (base {Γ = Γ} x refl eq) refl with cases++-lmap ` Δ₀ (A ∷ Δ') Γ eq
ccut-uf .(lmap ` Λ₁) {.(lmap ` Λ₂)} {.(` x₁)} (base {just x₄} x₂ refl refl) (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl refl) refl | Λ₁ , x₁ ∷ Λ₂ , refl , refl , refl
  rewrite cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) = refl
ccut-uf .(lmap ` Λ₁) {.(lmap ` Λ₂)} {.(` x₁)} (⊸l f f₁) (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl refl) refl | Λ₁ , x₁ ∷ Λ₂ , refl , refl , refl
  rewrite cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) | cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) = refl
ccut-uf .(lmap ` Λ₁) {.(lmap ` Λ₂)} {.(` x₁)} (⊸c Δ₀ f f₁) (base {Γ = .(Λ₁ ++ x₁ ∷ Λ₂)} x refl refl) refl | Λ₁ , x₁ ∷ Λ₂ , refl , refl , refl
  rewrite cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) | cases++-lmap-refl ` Λ₁ (x₁ ∷ Λ₂) = refl
ccut-uf Δ₀ f (uf g) r with cases∷ Δ₀ r
ccut-uf .[] f (uf g) refl | inj₁ (refl , refl , refl) = refl
ccut-uf .(_ ∷ Γ₀) f (uf g) refl | inj₂ (Γ₀ , refl , refl) =
  cong uf (ccut-uf Γ₀ f g refl)
ccut-uf Δ₀ f (⊸r g) refl =
  cong ⊸r (ccut-uf Δ₀ f g refl)
ccut-uf Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
ccut-uf {Γ = Γ} Δ₀ {.(Γ₀ ++ Δ)} f (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → ⊸l {Δ₀ ++ _ ∷ Γ ++ Γ₀} x g₁) (ccut-uf Δ₀ f g refl)
ccut-uf .(Γ ++ Γ₀) {Δ'} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) refl | inj₂ (Γ₀ , refl , refl) =
  cong (⊸l g) (ccut-uf Γ₀ f g₁ refl)
ccut-uf Δ₀ {Δ'} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) r with cases++ Δ₁ Δ₀ (Γ ++ Δ₂) (A ∷ Δ') (sym r)
ccut-uf .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ'} {A} f (⊸c Δ₁ {Γ} {Δ₂} g g₁) r | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ' Δ₂ q
ccut-uf {Γ = Γ} .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {.(Γ₀' ++ Δ₂)} {A} f (⊸c Δ₁ {.(Γ₀ ++ A ∷ Γ₀')} {Δ₂} g g₁) r | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  cong (λ x → ⊸c Δ₁ {Γ = Γ₀ ++ _ ∷ Γ ++ Γ₀'} x g₁) (ccut-uf Γ₀ f g refl)
ccut-uf .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') {Δ'} {A} f (⊸c Δ₁ {Γ} {.(Γ₀' ++ A ∷ Δ')} g g₁) refl | inj₁ (.(Γ ++ Γ₀') , refl , q) | inj₂ (Γ₀' , refl , refl) =
  cong (⊸c Δ₁ g) (ccut-uf (Δ₁ ++ _ ∷ Γ₀') f g₁ refl)
ccut-uf _ {.(Γ ++ Δ₂)} {.(A ⊸ B)} f (⊸c Δ₁ {Γ} {Δ₂} {A} {B} g g₁) refl | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₂) (A ⊸ B) = refl
ccut-uf {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₂)} {.x} f (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₂} g g₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  cong (⊸c (Δ₀ ++ _ ∷ Γ₁ ++ Γ₀) g) (ccut-uf Δ₀ f g₁ refl)

scut⊸ruf : {Γ Δ : Cxt} → {A B C D : Fma}
  → (f : just A ∣ Γ ++ B ∷ [] ⊢ C) (g : just (B ⊸ C) ∣ Δ ⊢ D)
  → scut (⊸r (uf f)) g ≗ uf (scut (⊸r f) g)
scut⊸ruf f (base {nothing} x () x₂)
scut⊸ruf f (base {just x₁} x () x₂)
scut⊸ruf f (⊸r g) = ⊸r (scut⊸ruf f g) ∙ ⊸ruf
scut⊸ruf f (⊸l g g₁) = refl
scut⊸ruf {Γ} {A = A} f (⊸c Δ₀ g g₁) =
  ⊸c (_ ∷ Γ ++ Δ₀) refl (scut⊸ruf f g₁) ∙ ⊸cuf {Δ₀ = Γ ++ Δ₀}

scut⊸r⊸l : {Γ Δ Λ : Cxt} → {A B C D E : Fma}
  → (f : nothing ∣ Γ ⊢ A) (g : just B ∣ Δ ++ C ∷ [] ⊢ D) (h : just (C ⊸ D) ∣ Λ ⊢ E)
  → scut (⊸r {Γ = Γ ++ Δ} (⊸l f g)) h ≗ ⊸l f (scut (⊸r g) h)
scut⊸r⊸l f g (base {nothing} x () x₂)
scut⊸r⊸l f g (base {just x₁} x () x₂)
scut⊸r⊸l {Γ} {Δ} {Λ} f g (⊸r h) = ⊸r (scut⊸r⊸l f g h) ∙ ⊸r⊸l {Γ = Γ}{Δ ++ Λ}
scut⊸r⊸l {Γ} {Δ} {C = C} f g (⊸l h h₁)
  rewrite cases++-inj₂ Δ Γ [] C = refl
scut⊸r⊸l {Γ} {Δ} f g (⊸c Δ₀ h h₁) =
  ⊸c (Γ ++ Δ ++ Δ₀) refl (scut⊸r⊸l f g h₁)
  ∙ ⊸c⊸l {Γ = Γ}{Δ ++ Δ₀} 

scut⊸r⊸c : ∀ {S : Stp} {Γ} Δ₀ {Δ₁ Λ : Cxt} → {A B C D E : Fma}
  → (f : nothing ∣ Γ ⊢ A) (g : S ∣ Δ₀ ++ B ∷ Δ₁ ++ C ∷ [] ⊢ D) (h : just (C ⊸ D) ∣ Λ ⊢ E)
  → scut (⊸r {Γ = Δ₀ ++ _ ∷ Γ ++ Δ₁} (⊸c Δ₀ f g)) h
         ≗ ⊸c Δ₀ f (scut (⊸r {Γ = Δ₀ ++ _ ∷ Δ₁} g) h)
scut⊸r⊸c Δ₀ f g (base {nothing} x () x₂)
scut⊸r⊸c Δ₀ f g (base {just x₁} x () x₂)
scut⊸r⊸c {Γ = Γ} Δ₀ {Δ₁} {Λ} f g (⊸r h) = ⊸r (scut⊸r⊸c Δ₀ f g h) ∙ ⊸r⊸c {Γ = Γ}{Δ₀}{Δ₁ ++ Λ}
scut⊸r⊸c {Γ = Γ} Δ₀ {Δ₁} {A = A} {B} {C} f g (⊸l h h₁)
  rewrite cases++-inj₁ Δ₀ (Γ ++ Δ₁) (C ∷ []) (A ⊸ B) | cases++-inj₂ Δ₁ Γ [] C = refl
scut⊸r⊸c {Γ = Γ} Δ₀ {Δ₂} f g (⊸c Δ₁ h h₁) =
  ⊸c (Δ₀ ++ _ ∷ Γ ++ Δ₂ ++ Δ₁) refl (scut⊸r⊸c Δ₀ f g h₁) ∙ ⊸c⊸c {Δ₀ = Δ₀}{Δ₂ ++ Δ₁}

scut⊸c : ∀ {S : Stp} {Γ} Δ₀ {Δ₁ Λ : Cxt} → {A B C D : Fma}
  → (f : S ∣ Γ ⊢ A)  (g : nothing ∣ Λ ⊢ B) (h : just A ∣ Δ₀ ++ C ∷ Δ₁ ⊢ D)
  → scut f (⊸c Δ₀ g h) ≗ ⊸c (Γ ++ Δ₀) g (scut f h)
scut⊸c Δ₀ (base x refl refl) g h = refl
scut⊸c Δ₀ (uf {Γ} f) g h = uf (scut⊸c Δ₀ f g h) ∙ (~ ⊸cuf {Δ₀ = Γ ++ Δ₀})
scut⊸c Δ₀ (⊸r f) g h = refl
scut⊸c Δ₀ (⊸l {Δ = Δ} f f₁) g h = ⊸l refl (scut⊸c Δ₀ f₁ g h) ∙ (~ ⊸c⊸l {Δ = Δ ++ Δ₀})
scut⊸c Δ₀ (⊸c Δ₁ {Γ} {Δ₂} f f₁) g h = ⊸c Δ₁ refl (scut⊸c Δ₀ f₁ g h) ∙ (~ ⊸c⊸c {Δ₀ = Δ₁} {Δ₂ ++ Δ₀})

ccut⊸l : ∀ {T : Stp} {Γ} Δ₀ {Δ₁ Δ Λ : Cxt} → {A A' B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)  (g : just B ∣ Λ ⊢ A') (h : T ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A' ∷ Δ₁)
  → ccut Δ₀ (⊸l f g) h eq ≗ ⊸c Δ₀ f (ccut Δ₀ g h eq)
ccut⊸l Δ₀ {Δ₁} {A' = A'} f g (base {Γ = Γ} x refl x₂) refl with cases++-lmap ` Δ₀ (A' ∷ Δ₁) Γ x₂
... | (Λ₁ , X ∷ Λ₂ , refl , refl , refl) = refl
ccut⊸l Δ₀ f g (uf h) eq with cases∷ Δ₀ eq
... | inj₁ (refl , refl , refl) = ~ ⊸cuf2
... | inj₂ (Γ₀ , refl , refl) = uf (ccut⊸l Γ₀ f g h refl ) ∙ (~ ⊸cuf)
ccut⊸l Δ₀ {Δ₁} {Λ = Λ} f g (⊸r h) refl = ⊸r (ccut⊸l Δ₀ f g h refl) ∙ ⊸r⊸c {Δ₁ = Λ ++ Δ₁}
ccut⊸l Δ₀ {Δ₁} f g (⊸l {Γ} {Δ} h h₁) eq with cases++ Δ₀ Γ Δ₁ Δ eq
ccut⊸l Δ₀ {.(Γ₀ ++ Δ)} f g (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl) =
  ⊸l (ccut⊸l Δ₀ f g h refl) refl ∙ (~ ⊸c⊸l2)
ccut⊸l .(Γ ++ Γ₀) {Δ₁} f g (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} h h₁) refl | inj₂ (Γ₀ , refl , refl) =
  ⊸l refl (ccut⊸l Γ₀ f g h₁ refl) ∙ (~ ⊸c⊸l)
ccut⊸l Δ₀ {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {Δ₃} h h₁) eq with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (A' ∷ Δ₂) (sym eq)
ccut⊸l .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {Δ₃} h h₁) eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₂ Δ₃ q
ccut⊸l .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) {.(Γ₀' ++ Δ₃)} {A' = A'} f g (⊸c Δ₁ {.(Γ₀ ++ A' ∷ Γ₀')} {Δ₃} h h₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (ccut⊸l Γ₀ f g h refl) refl ∙ (~ ⊸c⊸c2)
ccut⊸l .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {.(Γ₀' ++ A' ∷ Δ₂)} h h₁) refl | inj₁ (.(Γ ++ Γ₀') , refl , refl) | inj₂ (Γ₀' , refl , refl) =
    ⊸c Δ₁ refl (ccut⊸l (Δ₁ ++ _ ∷ Γ₀') f g h₁ refl) ∙ (~ ⊸c⊸c)
ccut⊸l Δ₀ {.(Γ ++ Δ₃)} {A' = .(_ ⊸ _)} f g (⊸c .Δ₀ {Γ} {Δ₃} h h₁) refl | inj₂ ([] , refl , refl) = refl
ccut⊸l {Γ = Γ₁} Δ₀ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} {Λ = Λ} {A' = .x} f g (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₃} h h₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ _ ∷ Γ₁ ++ Λ ++ Γ₀) refl (ccut⊸l Δ₀ f g h₁ refl) ∙ ⊸c⊸c {Δ₀ = Δ₀}{Δ₁ = Λ ++ Γ₀} 

ccut⊸c : ∀ {S T : Stp} {Γ} Δ₀ Λ₀ {Δ₁ Λ₁ Δ : Cxt} → {A A' B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)  (g : S ∣ Λ₀ ++ B ∷ Λ₁ ⊢ A') (h : T ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A' ∷ Δ₁)
  → ccut Δ₀ (⊸c Λ₀ f g) h eq ≗ ⊸c (Δ₀ ++ asCxt S Λ₀) f (ccut Δ₀ g h eq)
ccut⊸c Δ₀ Λ₁ {Δ₁} f g (base {Γ = Γ} x refl x₂) refl with cases++-lmap ` Δ₀ (_ ∷ Δ₁) Γ x₂
... | Λ₁' , X ∷ Λ₂' , refl , refl , refl = refl
ccut⊸c Δ₀ Λ₁ f g (uf h) eq with cases∷ Δ₀ eq
ccut⊸c {nothing} .[] Λ₁ f g (uf h) refl | inj₁ (refl , refl , refl) = refl
ccut⊸c {just x} .[] Λ₁ f g (uf h) refl | inj₁ (refl , refl , refl) = ~ ⊸cuf
ccut⊸c {S} .(_ ∷ Γ₀) Λ₁ f g (uf h) eq | inj₂ (Γ₀ , refl , refl) = uf (ccut⊸c Γ₀ Λ₁ f g h refl) ∙ (~ ⊸cuf {Δ₀ = Γ₀ ++ asCxt S Λ₁}) 
ccut⊸c {S} Δ₀ Λ₁ {Δ₁} {Λ₂} f g (⊸r h) refl = ⊸r (ccut⊸c Δ₀ Λ₁ f g h refl) ∙ (⊸r⊸c {Δ₀ = Δ₀ ++ asCxt S Λ₁}{Λ₂ ++ Δ₁}) 
ccut⊸c Δ₀ Λ₁ {Δ₁} f g (⊸l {Γ} {Δ} h h₁) eq with cases++ Δ₀ Γ Δ₁ Δ eq
ccut⊸c {S} Δ₀ Λ₁ {.(Γ₀ ++ Δ)}{Λ₂} f g (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} h h₁) refl | inj₁ (Γ₀ , refl , refl) =
  ⊸l (ccut⊸c Δ₀ Λ₁ f g h refl) refl ∙ (~ (⊸c⊸l2 {Δ = Δ₀ ++ asCxt S Λ₁}{_}{Λ₂ ++ Γ₀}))
ccut⊸c {S} .(Γ ++ Γ₀) Λ₁ {Δ₁} {Λ₂} f g (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} h h₁) refl | inj₂ (Γ₀ , refl , refl) =
  ⊸l refl (ccut⊸c Γ₀ Λ₁ f g h₁ refl) ∙ (~ (⊸c⊸l {Γ}{Γ₀ ++ asCxt S Λ₁}))
ccut⊸c Δ₀ Λ₁ {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {Δ₃} h h₁) eq with cases++ Δ₁ Δ₀ (Γ ++ Δ₃) (A' ∷ Δ₂) (sym eq)
ccut⊸c .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) Λ₁ {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {Δ₃} h h₁) eq | inj₁ (Γ₀ , refl , q) with cases++ Γ₀ Γ Δ₂ Δ₃ q
ccut⊸c {S} .(Δ₁ ++ _ ⊸ _ ∷ Γ₀) Λ₁ {.(Γ₀' ++ Δ₃)} {A' = A'} f g (⊸c Δ₁ {.(Γ₀ ++ A' ∷ Γ₀')} {Δ₃} h h₁) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) =
  ⊸c Δ₁ (ccut⊸c Γ₀ Λ₁ f g h refl) refl ∙ (~ ⊸c⊸c2 {Δ₀ = Γ₀ ++ asCxt S Λ₁} )
ccut⊸c {S} .(Δ₁ ++ _ ⊸ _ ∷ Γ ++ Γ₀') Λ₁ {Δ₂} {A' = A'} f g (⊸c Δ₁ {Γ} {.(Γ₀' ++ A' ∷ Δ₂)} h h₁) refl | inj₁ (.(Γ ++ Γ₀') , refl , q) | inj₂ (Γ₀' , refl , refl) =
  ⊸c Δ₁ refl (ccut⊸c (Δ₁ ++ _ ∷ Γ₀') Λ₁ f g h₁ refl) ∙ (~ (⊸c⊸c {Γ = Γ}{Δ₀ = Δ₁}{Γ₀' ++ asCxt S Λ₁}))
ccut⊸c _ Λ₁ {.(Γ ++ Δ₃)} {A' = .(A ⊸ B)} f g (⊸c Δ₁ {Γ} {Δ₃} {A} {B} h h₁) refl | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₂ [] Δ₁ (Γ ++ Δ₃) (A ⊸ B) = refl
ccut⊸c {S} {Γ = Γ₁} Δ₀ Λ₁ {.(Γ₀ ++ _ ⊸ _ ∷ Γ ++ Δ₃)} {Λ₂} {A' = .x} f g (⊸c .(Δ₀ ++ x ∷ Γ₀) {Γ} {Δ₃} h h₁) refl | inj₂ (x ∷ Γ₀ , refl , refl) =
  ⊸c (Δ₀ ++ asCxt S Λ₁ ++ _ ∷ Γ₁ ++ Λ₂ ++ Γ₀) refl (ccut⊸c Δ₀ Λ₁ f g h₁ refl) ∙ ⊸c⊸c {Δ₀ = Δ₀ ++ asCxt S Λ₁}{Δ₁ = Λ₂ ++ Γ₀}

cong-ccut-b2 : ∀ {S T Γ} Δ₀ {Δ₁ X Y} → 
               {f f' : S ∣ Γ ⊢ ` X}(g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y) →  
               f ≗ f' → ccut-b2 Δ₀ f g ≗ ccut-b2 Δ₀ f' g
cong-ccut-b2 Δ₀ g refl = refl
cong-ccut-b2 Δ₀ g (~ p) = ~ cong-ccut-b2 Δ₀ g p
cong-ccut-b2 Δ₀ g (p ∙ p₁) = cong-ccut-b2 Δ₀ g p ∙ cong-ccut-b2 Δ₀ g p₁
cong-ccut-b2 Δ₀ g (uf p) = cong-ccut-b2 Δ₀ g p
cong-ccut-b2 Δ₀ g (⊸l p p₁) = ⊸c (lmap ` Δ₀) p (cong-ccut-b2 Δ₀ g p₁)
cong-ccut-b2 {S} Δ₀ g (⊸c Δ₁ p p₁) = ⊸c (lmap ` Δ₀ ++ asCxt S Δ₁) p (cong-ccut-b2 Δ₀ g p₁)
cong-ccut-b2 Δ₀ g ⊸cuf = refl
cong-ccut-b2 Δ₀ g ⊸cuf2 = refl
cong-ccut-b2 Δ₀ g ⊸c⊸l = ⊸c⊸c
cong-ccut-b2 Δ₀ g ⊸c⊸l2 = ⊸c⊸c2
cong-ccut-b2 {S} Δ₀ g (⊸c⊸c {Δ₀ = Δ₁} {Δ₂}) = ⊸c⊸c {Δ₀ = lmap ` Δ₀ ++ asCxt S Δ₁} {Δ₂}
cong-ccut-b2 {S} Δ₀ g (⊸c⊸c2 {Δ₀ = Δ₁} {Δ₂ = Δ₂}) = ⊸c⊸c2 {Δ₀ = Δ₁} {Δ₂ = lmap ` Δ₀ ++ asCxt S Δ₂}
cong-ccut-b2 Δ₀ g baseuf = refl


ccut-b2-uf-b-n : ∀ {Γ Δ X Y} → 
               (f : nothing ∣ Γ ⊢ ` X)(g : just X ∣ Δ ⊢b Y) →
          ccut-b2 [] f (uf-b g) ≗ scut f (base g refl refl)
ccut-b2-uf-b-j : ∀ {Γ Δ X X' Y} → 
               (f : just X' ∣ Γ ⊢ ` X)(g : just X ∣ Δ ⊢b Y) →
          ccut-b2 [] f (uf-b g) ≗ uf (scut f (base g refl refl))

ccut-b2-uf-b-n (base {nothing} x refl refl) g =
  ≡-to-≗ (cong (λ x → base x refl refl) (ccut-uf-b2 x g))
ccut-b2-uf-b-n (uf f) g = ccut-b2-uf-b-j f g
ccut-b2-uf-b-n (⊸c Δ₀ f f₁) g =
  ⊸c Δ₀ refl (ccut-b2-uf-b-n f₁ g)

ccut-b2-uf-b-j (base {just x₁} x refl refl) g =
  ≡-to-≗ (cong (λ x → base x refl refl) (trans (ccut-uf-b2 (uf-b x) g) (scut-uf-b x g)))
  ∙ baseuf
ccut-b2-uf-b-j(⊸l f f₁) g =
  ⊸c [] refl (ccut-b2-uf-b-j f₁ g) ∙ ⊸cuf2
ccut-b2-uf-b-j (⊸c Δ₀ f f₁) g =
  ⊸c (_ ∷ Δ₀) refl (ccut-b2-uf-b-j f₁ g) ∙ ⊸cuf

ccut-b2-uf-b2 : ∀ {S Γ Δ₀ Δ₁ X X' Y} → 
               (f : S ∣ Γ ⊢ ` X)(g : just X' ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y) →
          ccut-b2 (X' ∷ Δ₀) f (uf-b g) ≗ uf (ccut-b2 Δ₀ f g)
ccut-b2-uf-b2 (base x refl refl) g =
  ≡-to-≗ (cong (λ x → base x refl refl) (cut-gen-uf-b _ x g)) ∙ baseuf
ccut-b2-uf-b2 (uf f) g = ccut-b2-uf-b2 f g
ccut-b2-uf-b2 {Δ₀ = Δ₀} (⊸l f f₁) g =
  ⊸c (_ ∷ lmap ` Δ₀) refl (ccut-b2-uf-b2 f₁ g) ∙ ⊸cuf
ccut-b2-uf-b2 {S} {Δ₀ = Δ₁} (⊸c Δ₀ f f₁) g =
  ⊸c (_ ∷ lmap ` Δ₁ ++ asCxt S Δ₀) refl (ccut-b2-uf-b2 f₁ g) ∙ ⊸cuf {_}{lmap ` Δ₁ ++ asCxt S Δ₀}

pr-ccut⊸r : ∀ {S T Γ Γ₁} Δ₀ {Δ₁ A B C D}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : T ∣ Δ₀ ++ B ∷ Δ₁ ++ D ∷ [] ⊢ C)
    →  pr-ccut Δ₀ f g (⊸r h) ≗ ⊸r (pr-ccut Δ₀ f g h)
pr-ccut⊸r Δ₀ (uf f) g h = pr-ccut⊸r Δ₀ f g h
pr-ccut⊸r Δ₀ (⊸r f) g h = refl
pr-ccut⊸r {Γ₁ = Γ₁} Δ₀ {Δ₁} (⊸l {Δ = Δ} f f₁) g h =
  ⊸c Δ₀ refl (pr-ccut⊸r Δ₀ f₁ g h) ∙ (~ ⊸r⊸c {_}{_}{Δ₀}{Δ ++ Γ₁ ++ Δ₁}) 
pr-ccut⊸r {S} {Γ₁ = Γ₁} Δ₀ {Δ₂} (⊸c Δ₁ {Γ} {Δ₃} f f₁) g h =
  ⊸c (Δ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸r Δ₀ f₁ g h) ∙ (~ (⊸r⊸c {_}{_}{Δ₀ ++ asCxt S Δ₁}{Δ₃ ++ Γ₁ ++ Δ₂}))


pr-ccutuf : ∀ {S Γ Γ₁} Δ₀ {Δ₁ A B C D}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : just D ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    →  pr-ccut (_ ∷ Δ₀) f g (uf h) ≗ uf (pr-ccut Δ₀ f g h)
pr-ccutuf Δ₀ (uf f) g h = pr-ccutuf Δ₀ f g h
pr-ccutuf Δ₀ (⊸r f) g h = refl
pr-ccutuf Δ₀ (⊸l f f₁) g h =
  ⊸c (_ ∷ Δ₀) refl (pr-ccutuf Δ₀ f₁ g h) ∙ ⊸cuf
pr-ccutuf {S} Δ₀ (⊸c Δ₁ f f₁) g h =
  ⊸c (_ ∷ Δ₀ ++ asCxt S Δ₁) refl (pr-ccutuf Δ₀ f₁ g h) ∙ ⊸cuf {_}{Δ₀ ++ asCxt S Δ₁}

pr-ccutuf2-n : ∀ {Γ Γ₁ Δ A B C}
    → (f : nothing ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : just B ∣ Δ ⊢ C)
    →  pr-ccut [] f g (uf h) ≗ scut f (⊸l g h)
pr-ccutuf2-j : ∀ {Γ Γ₁ Δ A A' B C}
    → (f : just A' ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : just B ∣ Δ ⊢ C)
    →  pr-ccut [] f g (uf h) ≗ uf (scut f (⊸l g h))

pr-ccutuf2-n (uf f) g h = pr-ccutuf2-j f g h
pr-ccutuf2-n (⊸r f) g h = refl
pr-ccutuf2-n (⊸c Δ₀ f f₁) g h = ⊸c Δ₀ refl (pr-ccutuf2-n f₁ g h)

pr-ccutuf2-j (⊸r f) g h = refl
pr-ccutuf2-j (⊸l f f₁) g h = ⊸c [] refl (pr-ccutuf2-j f₁ g h) ∙ ⊸cuf2
pr-ccutuf2-j (⊸c Δ₀ f f₁) g h = ⊸c (_ ∷ Δ₀) refl (pr-ccutuf2-j f₁ g h) ∙ ⊸cuf


pr-ccut⊸l1 : ∀ {S Γ Γ₁ Λ} Δ₀ {Δ₁ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : nothing ∣ Λ ⊢ A') (k : just B' ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C)
    → pr-ccut (Λ ++ Δ₀) f g (⊸l h k) ≗ ⊸l h (pr-ccut Δ₀ f g k)
pr-ccut⊸l1 Δ₀ (uf f) g h k = pr-ccut⊸l1 Δ₀ f g h k
pr-ccut⊸l1 {Λ = Λ} Δ₀ {Δ₁} {B = B} (⊸r f) g h k
  rewrite cases++-inj₂ Δ₀ Λ Δ₁ B = refl
pr-ccut⊸l1 {Λ = Λ} Δ₀ (⊸l f f₁) g h k =
  ⊸c (Λ ++ Δ₀) refl (pr-ccut⊸l1 Δ₀ f₁ g h k) ∙ ⊸c⊸l
pr-ccut⊸l1 {S} {Λ = Λ} Δ₀ (⊸c Δ₁ f f₁) g h k = 
  ⊸c (Λ ++ Δ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸l1 Δ₀ f₁ g h k) ∙ ⊸c⊸l {Δ = Δ₀ ++ asCxt S Δ₁}

pr-ccut⊸l2 : ∀ {S Γ Γ₁ Λ} Δ₀ {Δ₁ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : nothing ∣ Δ₀ ++ B ∷ Δ₁ ⊢ A') (k : just B' ∣ Λ ⊢ C)
    → pr-ccut Δ₀ f g (⊸l h k) ≗ ⊸l (pr-ccut Δ₀ f g h) k
pr-ccut⊸l2 Δ₀ (uf f) g h k = pr-ccut⊸l2 Δ₀ f g h k
pr-ccut⊸l2 {Λ = Λ} Δ₀ {Δ₁} {B = B} (⊸r f) g h k
  rewrite cases++-inj₁ Δ₀ Δ₁ Λ B = refl
pr-ccut⊸l2 Δ₀ (⊸l f f₁) g h k =
  ⊸c Δ₀ refl (pr-ccut⊸l2 Δ₀ f₁ g h k) ∙ ⊸c⊸l2
pr-ccut⊸l2 {S} Δ₀ (⊸c Δ₁ f f₁) g h k = 
  ⊸c (Δ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸l2 Δ₀ f₁ g h k) ∙ ⊸c⊸l2 {Δ = Δ₀ ++ asCxt S Δ₁}

pr-ccut⊸c11 : ∀ {S T Γ Γ₁ Λ} Δ₀ {Δ₁ Δ₂ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : nothing ∣ Λ ⊢ A') (k : T ∣ Δ₀ ++ B' ∷ Δ₁ ++ B ∷ Δ₂ ⊢ C)
    → pr-ccut (Δ₀ ++ A' ⊸ B' ∷ Λ ++ Δ₁) f g (⊸c Δ₀ h k) ≗ ⊸c Δ₀ h (pr-ccut (Δ₀ ++ B' ∷ Δ₁) f g k) 
pr-ccut⊸c11 Δ₀ (uf f) g h k = pr-ccut⊸c11 Δ₀ f g h k
pr-ccut⊸c11 {Λ = Λ} Δ₀ {Δ₁} {Δ₂} {B = B} {A'} {B'} (⊸r f) g h k
  rewrite cases++-inj₁ Δ₀ (Λ ++ Δ₁) (B ∷ Δ₂) (A' ⊸ B') | cases++-inj₂ Δ₁ Λ Δ₂ B = refl
pr-ccut⊸c11 {Λ = Λ} Δ₀ {Δ₁} (⊸l f f₁) g h k =
  ⊸c (Δ₀ ++ _ ∷ Λ ++ Δ₁) refl (pr-ccut⊸c11 Δ₀ f₁ g h k) ∙ ⊸c⊸c 
pr-ccut⊸c11 {S} {Λ = Λ} Δ₀ {Δ₂} (⊸c Δ₁ f f₁) g h k = 
  ⊸c (Δ₀ ++ _ ∷ Λ ++ Δ₂ ++ asCxt S Δ₁) refl (pr-ccut⊸c11 Δ₀ f₁ g h k) ∙ ⊸c⊸c {Δ₁ = Δ₂ ++ asCxt S Δ₁} 

pr-ccut⊸c12 : ∀ {S T Γ Γ₁ Λ} Δ₀ {Δ₁ Δ₂ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A') (h : nothing ∣ Λ ⊢ A) (k : T ∣ Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂ ⊢ C)
    → pr-ccut Δ₀ f h (⊸c (Δ₀ ++ B ∷ Δ₁) g k) ≗ ⊸c (Δ₀ ++ asCxt S Γ ++ Λ ++ Δ₁) g (pr-ccut Δ₀ f h k) 
pr-ccut⊸c12 Δ₀ (uf f) g h k = pr-ccut⊸c12 Δ₀ f g h k
pr-ccut⊸c12 {Γ₁ = Γ₁} Δ₀ {Δ₁} {Δ₂} {B = B} {A'} {B'} (⊸r f) g h k
  rewrite cases++-inj₂ (B ∷ Δ₁) Δ₀ (Γ₁ ++ Δ₂) (A' ⊸ B') = refl
pr-ccut⊸c12 {Λ = Λ} Δ₀ {Δ₁} (⊸l {Δ = Δ} f f₁) g h k = 
  ⊸c Δ₀ refl (pr-ccut⊸c12 Δ₀ f₁ g h k) ∙ (~ ⊸c⊸c {Δ₁ = Δ ++ Λ ++ Δ₁})
pr-ccut⊸c12 {S} {Λ = Λ} Δ₀ {Δ₂} (⊸c Δ₁ {Δ₁ = Δ₃} f f₁) g h k =
  ⊸c (Δ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸c12 Δ₀ f₁ g h k) ∙ (~ ⊸c⊸c {Δ₀ = Δ₀ ++ asCxt S Δ₁} {Δ₁ = Δ₃ ++ Λ ++ Δ₂})

pr-ccut⊸c21 : ∀ {S T Γ Γ₁} Δ₀ Λ₀ {Δ₁ Λ₁ A B A' B' C}
    → (f : S ∣ Γ ⊢ A ⊸ B) (g : nothing ∣ Γ₁ ⊢ A) (h : nothing ∣ Λ₀ ++ B ∷ Λ₁ ⊢ A') (k : T ∣ Δ₀ ++ B' ∷ Δ₁ ⊢ C)
    → pr-ccut (Δ₀ ++ A' ⊸ B' ∷ Λ₀) f g (⊸c Δ₀ h k) ≗ ⊸c Δ₀ (pr-ccut Λ₀ f g h) k
pr-ccut⊸c21 Δ₀ Λ₀ (uf f) g h k = pr-ccut⊸c21 Δ₀ Λ₀ f g h k
pr-ccut⊸c21 Δ₀ Λ₀ {Δ₁} {Λ₁} {B = B} {A'} {B'} (⊸r f) g h k
  rewrite cases++-inj₁ Δ₀ Λ₀ (B ∷ Λ₁ ++ Δ₁) (A' ⊸ B') | cases++-inj₁ Λ₀ Λ₁ Δ₁ B = refl
pr-ccut⊸c21 Δ₀ Λ₀ (⊸l f f₁) g h k =
  ⊸c (Δ₀ ++ _ ∷ Λ₀) refl (pr-ccut⊸c21 Δ₀ Λ₀ f₁ g h k) ∙ ⊸c⊸c2
pr-ccut⊸c21 {S} Δ₀ Λ₀ (⊸c Δ₁ f f₁) g h k = 
  ⊸c (Δ₀ ++ _ ∷ Λ₀ ++ asCxt S Δ₁) refl (pr-ccut⊸c21 Δ₀ Λ₀ f₁ g h k) ∙ ⊸c⊸c2 {Δ₀ = Λ₀ ++ asCxt S Δ₁}



