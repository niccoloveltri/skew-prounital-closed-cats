{-# OPTIONS --rewriting #-}

module Complete where

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

-- ====================================================================

-- completeness

cmplt : ∀{S B} → S ⇒ B → S ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊸ g) = ⊸r (⊸l (uf (cmplt f)) (cmplt g))
cmplt (i e) = ⊸l (cmplt e) ax
cmplt j = ⊸r (uf ax) 
cmplt L = ⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax))


-- ====================================================================

-- cmplt preserves equality

≐cmplt≗ : ∀{S B} {f g : S ⇒ B} → f ≐ g → cmplt f ≗ cmplt g
≐cmplt≗ refl = refl
≐cmplt≗ (~ p) = ~ (≐cmplt≗ p)
≐cmplt≗ (p ∙ q) = (≐cmplt≗ p) ∙ (≐cmplt≗ q)
≐cmplt≗ (_∘_ {f = f}{k = k} p q) =
  scut≗ (≐cmplt≗ q) (cmplt f) ∙ scut≗2 (cmplt k) (≐cmplt≗ p)
≐cmplt≗ (p ⊸ q) = ⊸r (⊸l (uf (≐cmplt≗ p)) (≐cmplt≗ q))
≐cmplt≗ (lid {f = f}) = ≡-to-≗ (scut-ax (cmplt f))
≐cmplt≗ rid = refl
≐cmplt≗ (ass {f = f}{g}{h}) = ≡-to-≗ (sym (scut-scut-ass (cmplt h) (cmplt g) (cmplt f)))
≐cmplt≗ f⊸id = ~ ax⊸
≐cmplt≗ f⊸∘ = refl
≐cmplt≗ (i p) = ⊸l (≐cmplt≗ p) refl
≐cmplt≗ (ni {e = e}) =
  ⊸l (~ (≡-to-≗ (scut-ax _))) (~ (≡-to-≗ (scut-ax _)))
≐cmplt≗ (nj {f = f}) =
  proof≗
    ⊸r (uf (scut (scut (cmplt f) ax) ax))
  ≗〈 ⊸r (uf (≡-to-≗ (scut-ax (scut (cmplt f) ax)))) 〉
    ⊸r (uf (scut (cmplt f) ax))
  ≗〈 ⊸r (uf (≡-to-≗ (scut-ax (cmplt f)))) 〉
    ⊸r (uf (cmplt f))
  qed≗
≐cmplt≗ (nL {f = f}{g}{h}) =
  proof≗
    ⊸r (⊸r (⊸l (uf (⊸l (uf (cmplt f)) (scut (cmplt g) ax))) (cmplt h)))
  ≗〈 ⊸r (⊸r (⊸l (uf (⊸l refl (≡-to-≗ (scut-ax (cmplt g))))) refl)) 〉 
    ⊸r (⊸r (⊸l (uf (⊸l (uf (cmplt f)) (cmplt g))) (cmplt h)))
  ≗〈 ⊸r (⊸r (⊸l (uf (⊸l (uf (~ (≡-to-≗ (scut-ax (cmplt f))))) refl)) (~ (≡-to-≗ (scut-ax (cmplt h)))))) 〉 
    ⊸r (⊸r (⊸l (uf (⊸l (uf (scut (cmplt f) ax)) (cmplt g))) (scut (cmplt h) ax)))
  qed≗
≐cmplt≗ LLL = refl
≐cmplt≗ ijL = ~ ax⊸
≐cmplt≗ Lj = 
  proof≗
    ⊸r (⊸r (uf (⊸l (uf ax) ax)))
  ≗〈 ⊸r ⊸ruf 〉
    ⊸r (uf (⊸r (⊸l (uf ax) ax)))
  ≗〈 ~ (⊸r (uf ax⊸)) 〉
    ⊸r (uf ax)
  qed≗
≐cmplt≗ iL =
  ⊸r (⊸l (uf (⊸l (≡-to-≗ (scut-ax _)) refl)) refl)
≐cmplt≗ ij = ≡-to-≗ (scut-ax _) ∙ ≡-to-≗ (scut-ax _)

