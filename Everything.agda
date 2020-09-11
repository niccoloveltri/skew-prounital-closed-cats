{-# OPTIONS --rewriting #-}

module Everything where

open import Utilities

open import Formulae

open import FreeSkewClosed

open import SeqCalc

open import SeqCalcNoStp

open import MulticatLaws

open import Sound

open import Complete

open import SoundComplete
open import CompleteSound

-- open import Focusing
-- open import NBEUnit

-- -- An indirect (i.e. via sequent calculus) proof of left normality

-- open import Data.Maybe
-- open import Data.List
-- open import Relation.Binary.PropositionalEquality hiding (_≗_)

-- ln : ∀{A}{B} → I ⇒ A ⊸ B → A ⇒ B
-- ln f = sound (uf-1 (Il-1 (⊸r-1 (cmplt f))))

-- ln-1 : ∀{A}{B} → A ⇒ B → I ⇒ A ⊸ B
-- ln-1 f = f ⊸ id ∘ j

-- ln-iso : ∀{A}{B} (f : I ⇒ A ⊸ B) → ln-1 (ln f) ≐ f
-- ln-iso {A}{B} f = 
--   proof≐
--     sound (uf-1 (Il-1 (⊸r-1 (cmplt f)))) ⊸ id ∘ j
--   ≐〈 sym≐ (soundcmplt _) 〉
--     sound (cmplt (sound (uf-1 (Il-1 (⊸r-1 (cmplt f)))) ⊸ id ∘ j))
--   ≐〈 refl≐ 〉
--     sound {_}{[]} (⊸r (Il (uf (scut (scut (cmplt (sound (uf-1 (Il-1 (⊸r-1 (cmplt f)))))) ax) ax))))
--   ≐〈 ≗sound≐ {_}{[]} (cong⊸r (congIl (conguf (≡-to-≗ (trans (scut-ax _) (scut-ax (cmplt (sound (uf-1 (Il-1 (⊸r-1 (cmplt f)))))))))))) 〉
--     sound {_}{[]} (⊸r (Il (uf (cmplt (sound (uf-1 (Il-1 (⊸r-1 (cmplt f)))))))))
--   ≐〈 ≗sound≐ {_}{[]} (cong⊸r (congIl (conguf (cmpltsound (uf-1 (Il-1 (⊸r-1 (cmplt f)))))))) 〉
--     sound {_}{[]} (⊸r (Il (uf (uf-1 (Il-1 (⊸r-1 (cmplt f)))))))
--   ≐〈 ≗sound≐ {_}{[]} (cong⊸r (congIl (uf-iso (Il-1 (⊸r-1 (cmplt f)))))) 〉
--     sound {_}{[]} (⊸r (Il (Il-1 (⊸r-1 (cmplt f)))))
--   ≐〈 ≗sound≐ {_}{[]} (cong⊸r (Il-iso (⊸r-1 (cmplt f)))) 〉
--     sound {_}{[]} (⊸r (⊸r-1 (cmplt f)))
--   ≐〈 ≗sound≐ (⊸r-iso (cmplt f)) 〉
--     sound (cmplt f)
--   ≐〈 soundcmplt f 〉
--     f
--   qed≐

-- ln-iso2 : ∀{A}{B} (f : A ⇒ B) → ln (ln-1 f) ≐ f
-- ln-iso2 f = trans≐ (≗sound≐ (≡-to-≗ (trans (scut-ax (scut (cmplt f) ax)) (scut-ax (cmplt f))))) (soundcmplt f)

-- open import Data.Empty
-- open import Data.Product
-- open import Data.Sum

-- -- at-stp-⊥ : ∀ {X Γ₀ Γ₁ Δ A C}
-- --   → Δ SeqCalcNoStp.⊢ C
-- --   → Δ ≡ ` X ∷ Γ₀ ++ A ∷ Γ₁
-- --   → ⊥
-- -- at-stp-⊥ {Γ₀ = Γ₀} ax eq = []disj∷ Γ₀ (inj∷ eq .proj₂)
-- -- at-stp-⊥ (⊸r f) refl = at-stp-⊥ f refl

-- gen⊸l : ∀ {Γ Δ} Δ₀ {Δ₁ A B C}
--   → Γ SeqCalcNoStp.⊢ A → Δ SeqCalcNoStp.⊢ C
--   → Δ ≡ Δ₀ ++ B ∷ Δ₁
--   → Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ SeqCalcNoStp.⊢ C
-- gen⊸l Δ₀ f ax eq with cases∷ Δ₀ eq
-- gen⊸l .[] f ax eq | inj₁ (refl , refl , refl) = ⊸l f ax
-- gen⊸l Δ₀ f ax eq | inj₂ (Γ₀ , q , r) = ⊥-elim ([]disj∷ Γ₀ q)
-- gen⊸l Δ₀ f Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
-- gen⊸l Δ₀ f (⊸r g) refl = ⊸r (gen⊸l Δ₀ f g refl)
-- gen⊸l Δ₀ f (Il g) eq with cases∷ Δ₀ eq
-- gen⊸l .[] f (Il g) eq | inj₁ (refl , refl , refl) = ⊸l f (Il g)
-- gen⊸l .(I ∷ Γ₀) f (Il g) refl | inj₂ (Γ₀ , refl , refl) = Il (gen⊸l Γ₀ f g refl)
-- gen⊸l Δ₀ f (⊸l g g₁) eq with cases∷ Δ₀ eq
-- gen⊸l .[] f (⊸l g g₁) eq | inj₁ (refl , refl , refl) = ⊸l f (⊸l g g₁)
-- gen⊸l .(_ ⊸ _ ∷ Δ₀) {Δ₁} f (⊸l {Γ} {Δ} g g₁) eq | inj₂ (Δ₀ , q , refl) with cases++ Δ₀ Γ Δ₁ Δ q
-- gen⊸l .(_ ∷ Δ₀) f (⊸l g g₁) eq | inj₂ (Δ₀ , q , refl) | inj₁ (Γ₀ , refl , refl) = ⊸l (gen⊸l Δ₀ f g refl) g₁
-- gen⊸l ._ f (⊸l g g₁) eq | inj₂ (._ , q , refl) | inj₂ (Γ₀ , refl , refl) = ⊸l g (gen⊸l (_ ∷ Γ₀) f g₁ refl)



-- [_∣int] : (Γ : Cxt) {A C : Fma} → A ⊸ C ⇒ [ Γ ∣ A ] ⊸ [ Γ ∣ C ]
-- [ [] ∣int] = id
-- [ B ∷ Γ ∣int] = L ∘ [ Γ ∣int]

-- test' : {Γ Δ₀ Δ₁ : Cxt} {D A B C : Fma} → I ⇒ [ Γ ∣ A ]  → [ Δ₀ ++ B ∷ Δ₁ ∣ C ] ⇒ [ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ∣ C ]
-- test' {Γ}{Δ₀} f = [ Δ₀ ∣ id ⊸ (i ∘ f ⊸ id ∘ [ Γ ∣int]) ∘ L  ]f

-- ⊸C' : {S : Stp} (Δ₀ : Cxt) {Γ Δ₁ Γ' : Cxt} {A B C : Fma}
--   → nothing ∣ Γ ⊢ A → S ∣ Γ' ⊢ C → Γ' ≡ Δ₀ ++ B ∷ Δ₁
--   → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢ C
-- ⊸C' Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
-- ⊸C' Δ₀ f (uf g) eq with cases∷ Δ₀ eq
-- ⊸C' .[] f (uf g) eq | inj₁ (refl , refl , refl) = uf (⊸l f g)
-- ⊸C' .(_ ∷ Γ₀) f (uf g) eq | inj₂ (Γ₀ , refl , refl) = uf (⊸C' Γ₀ f g refl)
-- ⊸C' Δ₀ f Ir eq =  ⊥-elim ([]disj∷ Δ₀ eq)
-- ⊸C' Δ₀ f (⊸r g) refl = ⊸r (⊸C' Δ₀ f g refl )
-- ⊸C' Δ₀ f (Il g) eq = Il (⊸C' Δ₀ f g eq)
-- ⊸C' Δ₀ {Δ₁ = Δ₁} f (⊸l {Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ₁ Δ eq
-- ⊸C' Δ₀ {Δ₁ = .(Γ₀ ++ Δ)} f (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g') eq | inj₁ (Γ₀ , refl , refl) = ⊸l (⊸C' Δ₀ f g refl) g'
-- ⊸C' .(Γ ++ Γ₀) {Δ₁ = Δ₁} f (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} g g') eq | inj₂ (Γ₀ , refl , refl) = ⊸l g (⊸C' Γ₀ f g' refl)


-- ⊸C : {S : Stp} (Δ₀ : Cxt) {Γ Δ₁ : Cxt} {A B C : Fma}
--   → nothing ∣ Γ ⊢ A → S ∣ Δ₀ ++ B ∷ Δ₁ ⊢ C
--   → S ∣ Δ₀ ++ A ⊸ B ∷ Γ ++ Δ₁ ⊢ C
-- ⊸C Δ₀ f g = ccut Δ₀ (uf (⊸l f ax)) g refl
