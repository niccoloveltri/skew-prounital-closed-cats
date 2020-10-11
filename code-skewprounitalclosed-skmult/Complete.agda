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

⊸l⋆ : ∀ Γ {Δ A C} (f : just A ∣ Δ ⊢ C)→ just [ Γ ∣ A ] ∣ Γ ++ Δ ⊢ C
⊸l⋆ [] f = f
⊸l⋆ (B ∷ Γ) f = ⊸l (uf ax) (⊸l⋆ Γ f)

cong⊸l⋆ : ∀ Γ {Δ A C} {f f' : just A ∣ Δ ⊢ C}
  → f ≗ f' → ⊸l⋆ Γ f ≗ ⊸l⋆ Γ f'
cong⊸l⋆ [] p = p
cong⊸l⋆ (x ∷ Γ) p = ⊸l refl (cong⊸l⋆ Γ p)

scut⊸r⋆⊸l⋆ : ∀ Γ {S Γ' Δ A C} {f : S ∣ Γ' ++ Γ ⊢ A} {g : just A ∣ Δ ⊢ C}
  → scut {_}{Γ'}{Γ ++ Δ} (⊸r⋆ Γ f) (⊸l⋆ Γ g) ≗ scut {_}{Γ' ++ Γ}{Δ} f g
scut⊸r⋆⊸l⋆ [] = refl
scut⊸r⋆⊸l⋆ (_ ∷ Γ) {Γ' = Γ'} {f = f}{g} =
  ~ (ccut-ass-scut Γ' (uf ax) (⊸r⋆ {_}{Γ' ++ _ ∷ []} Γ f) _ refl)
  ∙ ≡-to-≗ (ccut-uf Γ' ax (scut (⊸r⋆ {_}{Γ' ++ _ ∷ []} Γ f) _) refl)
  ∙ ccut-unit Γ' (scut (⊸r⋆ {_}{Γ' ++ _ ∷ []} Γ f) _) refl
  ∙ scut⊸r⋆⊸l⋆ Γ

[_∣cmplt]f : ∀ Γ {A C} {f : just A ⇒ C}
  → cmplt [ Γ ∣ f ]f ≗ ⊸r⋆ Γ (⊸l⋆ Γ (cmplt f))
[ [] ∣cmplt]f = refl
[ _ ∷ Γ ∣cmplt]f = ⊸r (⊸l refl [ Γ ∣cmplt]f ∙ ~ ⊸r⋆⊸l Γ _ _)

ccut⊸r⋆ : {S T : Stp} → {Γ Δ : Cxt} → (Δ₀ Λ : Cxt) → {Δ' : Cxt} → {A C : Fma} → 
             (f : S ∣ Γ ⊢ A)  (g : T ∣ Δ ++ Λ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') (s : Δ ++ Λ ≡ Δ₀ ++ A ∷ Δ' ++ Λ) →  
                                        ccut Δ₀ f (⊸r⋆ Λ g) r ≗ ⊸r⋆ Λ (ccut Δ₀ {Δ' ++ Λ} f g s)
ccut⊸r⋆ Δ₀ [] f g refl refl = refl
ccut⊸r⋆ Δ₀ (A ∷ Λ) {Δ'} {B} f g refl refl = ⊸r (ccut⊸r⋆ {Δ = Δ₀ ++ B ∷ Δ' ++ A ∷ []} Δ₀ Λ f g refl refl )

cmplt-L⋆ : (Δ : Cxt) {A C : Fma}
  → cmplt (L⋆ Δ {A}{C}) ≗ ⊸r {Γ = []} (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax))
cmplt-L⋆ [] = refl
cmplt-L⋆ (B ∷ Δ) =
  proof≗
    scut (cmplt (L⋆ Δ)) (⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax)))
  ≗〈 cong-scut1 (cmplt-L⋆ Δ) 〉
    ⊸r (⊸r (scut (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl) ax))  
  ≗〈 ⊸r (⊸r (scut-unit2 (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl))) 〉 
    ⊸r (⊸r (ccut [] (uf (⊸l (uf ax) ax)) (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ ax)) ax)) refl))  
  ≗〈 ⊸r (⊸r (ccut⊸r⋆ [] Δ  (uf (⊸l (uf ax) ax)) (⊸l (uf (⊸r⋆-1 Δ ax)) ax) refl refl)) 〉 
    ⊸r (⊸r (⊸r⋆ Δ (ccut [] (uf (⊸l (uf ax) ax)) (⊸l (uf (⊸r⋆-1 Δ ax)) ax) refl)))
  ≗〈 ⊸r (⊸r (cong⊸r⋆ Δ (⊸l (uf (~ (⊸r⋆-1⊸l Δ (uf ax) ax ∙ ⊸l refl (~ scut-unit _)))) refl))) 〉
    ⊸r (⊸r (⊸r⋆ Δ (⊸l (uf (⊸r⋆-1 Δ (⊸l (uf ax) ax))) ax)))
  qed≗

scut⊸r-1 : {S : Stp} {Γ Δ : Cxt} {B C D : Fma}
  → (f : S ∣ Γ ⊢ B)
  → (g : just B ∣ Δ ⊢ C ⊸ D)
  → scut f (⊸r-1 g) ≡ ⊸r-1 {Γ = Γ ++ Δ} (scut f g)
scut⊸r-1 (base f refl refl) (⊸r g) = refl  
scut⊸r-1 (base {Γ = Γ} f refl refl) (⊸c Δ₀ g g') =
  cong (⊸c (lmap ` Γ ++ Δ₀) g) (scut⊸r-1 (base f refl refl) g')  
scut⊸r-1 (uf f) g = cong uf (scut⊸r-1 f g)
scut⊸r-1 (⊸r f) (⊸r g) = refl
scut⊸r-1 {Γ = Γ} (⊸r f) (⊸c Δ₀ g g') =
  cong (⊸c (Γ ++ Δ₀) g) (scut⊸r-1 (⊸r f) g')
scut⊸r-1 {Γ = Γ} (⊸r f) (⊸l g g') = scut⊸r-1 (ccut Γ g f refl) g'
scut⊸r-1 (⊸l f f') g = cong (⊸l f) (scut⊸r-1 f' g)
scut⊸r-1 (⊸c Δ₀ f f') g = cong (⊸c Δ₀ f) (scut⊸r-1 f' g)

scut⊸r⋆-1 : {S : Stp} {Γ Γ' : Cxt} (Δ : Cxt) {A C : Fma}
  → (f : S ∣ Γ ⊢ A)
  → (g : just A ∣ Γ' ⊢ [ Δ ∣ C ])
  → scut f (⊸r⋆-1 Δ g) ≡ ⊸r⋆-1 {Γ = Γ ++ Γ'} Δ (scut f g)
scut⊸r⋆-1 [] f g = refl
scut⊸r⋆-1 {Γ = Γ}{Γ'} (A' ∷ Δ) f g =
  trans (scut⊸r⋆-1 {Γ' = Γ' ++ A' ∷ []} Δ f (⊸r-1 g))
        (cong (⊸r⋆-1 {Γ = Γ ++ Γ' ++ A' ∷ []} Δ) (scut⊸r-1 f g))

cong⊸r⋆-1 : ∀{S}{Γ} Δ {C}{f g : S ∣ Γ ⊢ [ Δ ∣ C ]} → f ≗ g → ⊸r⋆-1 Δ f ≗ ⊸r⋆-1 Δ g
cong⊸r⋆-1 [] p = p
cong⊸r⋆-1 {Γ = Γ} (A ∷ Δ) p = cong⊸r⋆-1 {Γ = Γ ++ A ∷ []} Δ (cong⊸r-1 p)

scut⊸r⋆⊸r⋆-1 : ∀{S}{Γ} Δ {C}(f : S ∣ Γ ++ Δ ⊢ C)
  → scut (⊸r⋆ Δ f) (⊸r⋆-1 Δ ax) ≗ f
scut⊸r⋆⊸r⋆-1 Δ f =
  ≡-to-≗ (scut⊸r⋆-1 Δ (⊸r⋆ Δ f) ax)
  ∙ (cong⊸r⋆-1 Δ (scut-unit2 _)
  ∙ ≡-to-≗ (⊸r⋆-iso2 Δ f))


ccut-base-eq : ∀{T Γ Δ₀ Δ₁ X Y}
  → (f : nothing ∣ Γ ⊢b X) (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
  → ccut (lmap ` Δ₀) (base f refl refl) (base g refl refl) refl ≡ base (ccut-b Δ₀ f g) refl refl
ccut-base-eq {Δ₀ = Δ₀} {Δ₁} {X} f g rewrite cases++-lmap-refl ` Δ₀ (X ∷ Δ₁) = refl


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

≐cmplt≗ (basescut {Γ = Γ} {Δ} {f = f} {g}) =
  ⊸r⋆ass (lmap ` Γ) (lmap ` Δ) (base (scut-b f g) refl refl)
  ∙ cong⊸r⋆ (lmap ` Γ) (~ (scut⊸r⋆ (lmap ` Δ) (base f refl refl) (base g refl refl)) ∙ ~ (scut⊸r⋆⊸l⋆ (lmap ` Γ)))
  ∙ ~ (scut⊸r⋆ (lmap ` Γ) (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸l⋆ (lmap ` Γ) (⊸r⋆ (lmap ` Δ) (base g refl refl))))
  ∙ ~ cong-scut2 (⊸r⋆ (lmap ` Γ) (base f refl refl)) [ lmap ` Γ ∣cmplt]f
≐cmplt≗ (baseccut {Γ = Γ} {Δ₀} {Δ₁} {X = X} {f = f} {g}) =
  ⊸r⋆ass (lmap ` Δ₀) (lmap ` (Γ ++ Δ₁)) (base (ccut-b Δ₀ f g) refl refl)
  ∙ cong⊸r⋆ (lmap ` Δ₀)
      (⊸r⋆ass (lmap ` Γ) (lmap ` Δ₁) (base (ccut-b Δ₀ f g) refl refl)
       ∙ cong⊸r⋆ (lmap ` Γ)
           (cong⊸r⋆ (lmap ` Δ₁)
              (~ (≡-to-≗ (ccut-base-eq f g))
               ∙ ~ (cong-ccut1 (lmap ` Δ₀) (base g refl refl) refl (scut⊸r⋆⊸r⋆-1 (lmap ` Γ) (base f refl refl))))
            ∙ ~ ccut⊸r⋆ (lmap ` Δ₀) (lmap ` Δ₁) (scut (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸r⋆-1 (lmap ` Γ) ax)) _ refl refl
            ∙ ~ (scut-unit2 (ccut (lmap ` Δ₀) (scut (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸r⋆-1 (lmap ` Γ) ax)) (⊸r⋆ (lmap ` Δ₁) _) refl)))
       ∙ ~ scut⊸r⋆ (lmap ` Γ) (⊸r (⊸r⋆ (lmap ` Δ₁) (base g refl refl))) (⊸l (scut (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸r⋆-1 (lmap ` Γ) ax)) ax)
       ∙ cong-scut2 (⊸r (⊸r⋆ (lmap ` Δ₁) (base g refl refl)))
           (~ (ccut⊸r⋆ [] (lmap ` Γ) (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸l (uf (⊸r⋆-1 (lmap ` Γ) ax)) ax) refl refl)
            ∙ ~ scut-unit2 (ccut [] (⊸r⋆ (lmap ` Γ) (base f refl refl)) (⊸r⋆ (lmap ` Γ) (⊸l (uf (⊸r⋆-1 (lmap ` Γ) ax)) ax)) refl)
            ∙ cong-scut1 {h = ⊸l (⊸r⋆ (lmap ` Γ) (base f refl refl)) ax} (~ cmplt-L⋆ (lmap ` Γ))) 
       ∙ ~ scut⊸r⋆⊸l⋆ (lmap ` Δ₀)
       ∙ ~ cong-scut1 (⊸r⋆ass (lmap ` Δ₀) (_ ∷ lmap ` Δ₁) (base g refl refl)))
  ∙ ~ (scut⊸r⋆ (lmap ` Δ₀) (⊸r⋆ (lmap ` Δ₀ ++ _ ∷ lmap ` Δ₁) (base g refl refl)) (⊸l⋆ (lmap ` Δ₀) (scut (cmplt (L⋆ (lmap ` Γ))) (⊸l (⊸r⋆ (lmap ` Γ) (base f refl refl)) ax))))
  ∙ ~ cong-scut2 (⊸r⋆ (lmap ` Δ₀ ++ _ ∷ lmap ` Δ₁) (base g refl refl))  [ lmap ` Δ₀ ∣cmplt]f

