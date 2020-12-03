{-# OPTIONS --rewriting  #-}

open import SkMults

module SeqCalcVar where

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
-- =======================================================================

-- Variant of the sequent calculus, now with admissible uf rule. This
-- admissibility result is possible because of the presence of the new
-- constructor ⊸c and of the uf-b rule in the base skew multicategory

infix 15 _∣_⊢V_

data _∣_⊢V_ : Stp → Cxt → Fma → Set where
  base : ∀ {T S Γ Δ Y} → T ∣ Γ ⊢b Y
    → S ≡ mmap ` T → Δ ≡ lmap ` Γ
    → S ∣ Δ ⊢V ` Y
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢V B → S ∣ Γ ⊢V A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢V A → just B ∣ Δ ⊢V C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢V C
  ⊸c : {S : Stp} (Δ₀ : Cxt) {Γ Δ₁ : Cxt} {A B C : Fma}
    → nothing ∣ Γ ⊢V A → S ∣ Δ₀ ++ B ∷ Δ₁ ⊢V C
    → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢V C

subst-cxtV : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢V A → S ∣ Γ' ⊢V A 
subst-cxtV refl f = f

ufV : {Γ : Cxt} → {A C : Fma} → 
               just A ∣ Γ ⊢V C → nothing ∣ A ∷ Γ ⊢V C 
ufV (base {just X} f refl refl) = base (uf-b f) refl refl
ufV (⊸r f) = ⊸r (ufV f)
ufV (⊸l f g) = ⊸c [] f (ufV g)
ufV (⊸c Δ₀ f g) = ⊸c (_ ∷ Δ₀) f (ufV g)

-- -- equality of derivations

infixl 20 _∙_

data _≗V_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢V A → S ∣ Γ ⊢V A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢V A} → f ≗V f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢V A} → f ≗V g → g ≗V f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢V A} → f ≗V g → g ≗V h → f ≗V h
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢V C} → f ≗V g → ⊸r f ≗V ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢V A}{f' g' : just B ∣ Δ ⊢V C}
    → f ≗V g → f' ≗V g' → ⊸l f f' ≗V ⊸l g g'
  ⊸c : ∀{S Γ} Δ₀ {Δ₁}{A}{B}{C}{f g : nothing ∣ Γ ⊢V A}{f' g' : S ∣ Δ₀ ++ B ∷ Δ₁ ⊢V C}
    → f ≗V g → f' ≗V g' → ⊸c Δ₀ f f' ≗V ⊸c Δ₀ g g'
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢V A}{g : just B ∣ Δ ++ C ∷ [] ⊢V D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗V ⊸l f (⊸r g)
  ⊸r⊸c : {S : Stp} {Γ Δ₀ Δ₁ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢V A}{g : S ∣ Δ₀ ++ B ∷ Δ₁ ++ C ∷ [] ⊢V D}
    → ⊸r {Γ = Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁} (⊸c Δ₀ f g) ≗V ⊸c Δ₀ f (⊸r g)
  ⊸c⊸l : {Γ Δ Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢V A} {f' : nothing ∣ Γ' ⊢V A'} {g : just B ∣ Δ ++ B' ∷ Λ ⊢V C} 
    → ⊸c (Γ ++ Δ) f' (⊸l f g) ≗V ⊸l f (⊸c Δ f' g)
  ⊸c⊸l2 : {Γ Δ Γ' Λ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ ++ B' ∷ Λ ⊢V A} {f' : nothing ∣ Γ'  ⊢V A'} {g : just B ∣ Γ ⊢V C} 
    → ⊸c Δ f' (⊸l f g) ≗V ⊸l (⊸c Δ f' f) g
  ⊸c⊸c : {S : Stp} {Γ Γ' Δ₀ Δ₁ Δ₂ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Γ ⊢V A} {f' : nothing ∣ Γ' ⊢V A'} {g : S ∣ Δ₀ ++ B ∷ Δ₁ ++ B' ∷ Δ₂ ⊢V C} 
    → ⊸c (Δ₀ ++ _ ∷ Γ ++ Δ₁) f' (⊸c Δ₀ f g) ≗V ⊸c Δ₀ f (⊸c (Δ₀ ++ B ∷ Δ₁) f' g)
  ⊸c⊸c2 : {S : Stp} {Γ Δ₀ Δ₁ Δ₂ Δ₃ : Cxt} {A B A' B' C : Fma}
    → {f : nothing ∣ Δ₀ ++ B ∷ Δ₁ ⊢V A} {f' : nothing ∣ Γ ⊢V A'} {g : S ∣ Δ₂ ++ B' ∷ Δ₃ ⊢V C} 
    → ⊸c (Δ₂ ++ _ ∷  Δ₀) f' (⊸c Δ₂ f g) ≗V ⊸c Δ₂ (⊸c Δ₀ f' f) g


-- this sequent calculus is equivalent to the one having uf as
-- primitive rule

≡-to-≗V : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢V A} → f ≡ f' → f ≗V f'
≡-to-≗V refl = refl

fromV : ∀{S Γ C} → S ∣ Γ ⊢V C → S ∣ Γ ⊢ C
fromV (base f eq1 eq2) = base f eq1 eq2
fromV (⊸r f) = ⊸r (fromV f)
fromV (⊸l f g) = ⊸l (fromV f) (fromV g)
fromV (⊸c Δ₀ f g) = ⊸c Δ₀ (fromV f) (fromV g)

toV : ∀{S Γ C} → S ∣ Γ ⊢ C → S ∣ Γ ⊢V C
toV (base f eq1 eq2) = base f eq1 eq2
toV (uf f) = ufV (toV f)
toV (⊸r f) = ⊸r (toV f)
toV (⊸l f g) = ⊸l (toV f) (toV g)
toV (⊸c Δ₀ f g) = ⊸c Δ₀ (toV f) (toV g)

congfromV : ∀{S Γ C}{f g : S ∣ Γ ⊢V C} → f ≗V g → fromV f ≗ fromV g
congfromV refl = refl
congfromV (~ eq) = ~ congfromV eq
congfromV (eq ∙ eq₁) = congfromV eq ∙ congfromV eq₁
congfromV (⊸r eq) = ⊸r (congfromV eq)
congfromV (⊸l eq eq₁) = ⊸l (congfromV eq) (congfromV eq₁)
congfromV (⊸c Δ₀ eq eq₁) = ⊸c Δ₀ (congfromV eq) (congfromV eq₁)
congfromV ⊸r⊸l = ⊸r⊸l
congfromV ⊸r⊸c = ⊸r⊸c
congfromV ⊸c⊸l = ⊸c⊸l
congfromV ⊸c⊸l2 = ⊸c⊸l2
congfromV ⊸c⊸c = ⊸c⊸c
congfromV ⊸c⊸c2 = ⊸c⊸c2

congufV : ∀{A Γ C}{f g : just A ∣ Γ ⊢V C} → f ≗V g → ufV f ≗V ufV g
congufV refl = refl
congufV (~ eq) = ~ congufV eq
congufV (eq ∙ eq₁) = congufV eq ∙ congufV eq₁
congufV (⊸r eq) = ⊸r (congufV eq)
congufV (⊸l eq eq₁) = ⊸c [] eq (congufV eq₁)
congufV (⊸c Δ₀ eq eq₁) = ⊸c (_ ∷ Δ₀) eq (congufV eq₁)
congufV ⊸r⊸l = ⊸r⊸c
congufV ⊸r⊸c = ⊸r⊸c
congufV ⊸c⊸l = ⊸c⊸c
congufV ⊸c⊸l2 = ⊸c⊸c2
congufV ⊸c⊸c = ⊸c⊸c
congufV ⊸c⊸c2 = ⊸c⊸c2

congtoV : ∀{S Γ C}{f g : S ∣ Γ ⊢ C} → f ≗ g → toV f ≗V toV g
congtoV refl = refl
congtoV (~ eq) = ~ congtoV eq
congtoV (eq ∙ eq₁) = congtoV eq ∙ congtoV eq₁
congtoV (uf eq) = congufV (congtoV eq)
congtoV (⊸r eq) = ⊸r (congtoV eq)
congtoV (⊸l eq eq₁) = ⊸l (congtoV eq) (congtoV eq₁)
congtoV (⊸c Δ₀ eq eq₁) = ⊸c Δ₀ (congtoV eq) (congtoV eq₁)
congtoV ⊸ruf = refl
congtoV ⊸r⊸l = ⊸r⊸l
congtoV ⊸r⊸c = ⊸r⊸c
congtoV ⊸cuf = refl
congtoV ⊸cuf2 = refl
congtoV ⊸c⊸l = ⊸c⊸l
congtoV ⊸c⊸l2 = ⊸c⊸l2
congtoV ⊸c⊸c = ⊸c⊸c
congtoV ⊸c⊸c2 = ⊸c⊸c2
congtoV baseuf = refl

toVfromV : ∀{S Γ C} (f : S ∣ Γ ⊢V C)
  → toV (fromV f) ≗V f
toVfromV (base f eq1 eq2) = refl
toVfromV (⊸r f) = ⊸r (toVfromV f)
toVfromV (⊸l f g) = ⊸l (toVfromV f) (toVfromV g)
toVfromV (⊸c Δ₀ f g) = ⊸c Δ₀ (toVfromV f) (toVfromV g)

fromVufV : ∀{A Γ C} (f : just A ∣ Γ ⊢V C)
  → fromV (ufV f) ≗ uf (fromV f)
fromVufV (base {just X} f refl refl) = baseuf
fromVufV (⊸r f) = ⊸r (fromVufV f) ∙ ⊸ruf
fromVufV (⊸l f g) = ⊸c [] refl (fromVufV g) ∙ ⊸cuf2
fromVufV (⊸c Δ₀ f g) = ⊸c (_ ∷ Δ₀) refl (fromVufV g) ∙ ⊸cuf

fromVtoV : ∀{S Γ C} (f : S ∣ Γ ⊢ C)
  → fromV (toV f) ≗ f
fromVtoV (base f eq1 eq2) = refl
fromVtoV (⊸r f) = ⊸r (fromVtoV f)
fromVtoV (⊸l f g) = ⊸l (fromVtoV f) (fromVtoV g)
fromVtoV (⊸c Δ₀ f g) = ⊸c Δ₀ (fromVtoV f) (fromVtoV g)
fromVtoV (uf f) = fromVufV _ ∙ uf (fromVtoV f)

