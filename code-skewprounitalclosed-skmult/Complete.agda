{-# OPTIONS --rewriting #-}

open import SkMults

module Complete where --(M : SkMult) where

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
open import CutsCong
open import Sound

--open SkMult M

⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma} → S ∣ Γ ++ Δ ⊢ C → S ∣ Γ ⊢ [ Δ ∣ C ]
⊸r⋆ [] f = f
⊸r⋆ (A ∷ Δ) f = ⊸r (⊸r⋆ Δ f)

cong⊸r⋆ : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ++ Δ ⊢ C} → f ≗ g → ⊸r⋆ Δ f ≗ ⊸r⋆ Δ g
cong⊸r⋆ [] p = p
cong⊸r⋆ (_ ∷ Δ) p = ⊸r (cong⊸r⋆ Δ p)

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

scut⊸r⋆ : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A C : Fma}
  → (f : S ∣ Γ ⊢ A)
  → (g : just A ∣ Γ' ++ Δ ⊢ C)
  → scut f (⊸r⋆ Δ g) ≗ ⊸r⋆ Δ (scut f g)
scut⊸r⋆ [] f g = refl
scut⊸r⋆ {Γ' = Γ'} (_ ∷ Δ) f g =
  scut⊸r f (⊸r⋆ Δ g) ∙ 
    ⊸r (scut⊸r⋆ {Γ' = Γ' ++ _ ∷ []} Δ f g)

-- ====================================================================

-- completeness

cmplt : ∀{S B} → S ⇒ B → S ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊸ g) = ⊸r (⊸l (uf (cmplt f)) (cmplt g))
cmplt (i e) = ⊸l (cmplt e) ax
cmplt j = ⊸r (uf ax) 
cmplt L = ⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax))
cmplt (base {Γ = Γ}{Δ} f eq eq2) = ⊸r⋆ Δ (base f eq eq2)

-- ====================================================================

-- cmplt preserves equality

≐cmplt≗ : ∀{S B} {f g : S ⇒ B} → f ≐ g → cmplt f ≗ cmplt g
≐cmplt≗ refl = refl
≐cmplt≗ (~ p) = ~ (≐cmplt≗ p)
≐cmplt≗ (p ∙ q) = (≐cmplt≗ p) ∙ (≐cmplt≗ q)
≐cmplt≗ (_∘_ {f = f}{k = k} p q) =
  cong-scut (≐cmplt≗ q) (≐cmplt≗ p)
≐cmplt≗ (p ⊸ q) = ⊸r (⊸l (uf (≐cmplt≗ p)) (≐cmplt≗ q))
≐cmplt≗ (lid {f = f}) = scut-unit2 (cmplt f)
≐cmplt≗ (rid {f = f}) = ~ scut-unit (cmplt f)
≐cmplt≗ (ass {f = f}{g}{h}) = 
  scut-ass-scut (cmplt h) (cmplt g) (cmplt f)
≐cmplt≗ (f⊸id {A}{B}) = refl
≐cmplt≗ f⊸∘ = refl
≐cmplt≗ (i p) = ⊸l (≐cmplt≗ p) refl
≐cmplt≗ (ni {e = e}) =
  ⊸l (~ scut-unit2 _)
     (scut-unit _ ∙ scut-unit _ ∙ ~ (scut-unit2 _))
≐cmplt≗ (nj {f = f}) =
  ⊸r (uf (scut-unit2 _ ∙ scut-unit2 _ ∙ ~ (scut-unit _) ∙ cong-scut1 (~ (scut-unit _))))
≐cmplt≗ (nL {f = f}{g}{h}) =
  ⊸r (⊸r
    (⊸l
      (uf (⊸l (uf (scut-unit _ ∙ scut-unit _ ∙
               ~ (cong-scut2 (cmplt f) (scut-unit _) ∙ scut-unit2 _ )))
              (scut-unit2 _ ∙ ~ (cong-scut1 (scut-unit _) ∙ scut-unit _))))
      (scut-unit _ ∙ ~ (cong-scut2 (cmplt h) (scut-unit _) ∙ scut-unit2 _))))
≐cmplt≗ LLL =
  ⊸r (⊸r (⊸r
    (⊸l (uf (⊸l (uf
                (⊸l (uf (~ (cong-scut1 (scut-unit _)
                            ∙ scut-unit _
                            ∙ scut-unit _
                            ∙ scut-unit2 _
                            ∙ scut-unit _
                            ∙ scut-unit _)))
                    refl))
                (~ scut-unit2 _)))
        (~ scut-unit _))))
≐cmplt≗ ijL =
  ⊸r (⊸l (uf
    (scut-unit _ ∙ scut-unit2 _ ∙ scut-unit _)) (scut-unit _))
≐cmplt≗ Lj =
  ⊸r (⊸ruf ∙ uf (⊸r (⊸l refl (scut-unit2 _ ∙ scut-unit _))))
≐cmplt≗ (iL {e = e}) =
  ⊸r (⊸l (uf
         (⊸l (cong-scut2 (cmplt e) (scut-unit _) ∙ scut-unit2 _)
             (scut-unit _)))
     (scut-unit _))
≐cmplt≗ ij = scut-unit2 _ ∙ scut-unit2 _
≐cmplt≗ baseax = refl
≐cmplt≗ (baseuf {Γ = Γ} {f = f}) =
  ⊸r (cong⊸r⋆ (lmap ` Γ) (baseuf ∙ uf
      (≡-to-≗ (cong (λ x → base x refl refl)
        (sym (trans (cong (λ x → scut-b x f) (scut-ax-b _)) (scut-ax-b2 _))))))
    ∙ ⊸r⋆uf (lmap ` Γ) (base (scut-b (scut-b ax-b ax-b) f) refl refl)
    ∙ uf (~
      (scut⊸r⋆ (lmap ` Γ)
        (base (scut-b ax-b ax-b) refl refl) (base f refl refl))))

