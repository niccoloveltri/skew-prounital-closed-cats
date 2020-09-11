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
open import FreeSkewClosed
open import SeqCalc
open import MulticatLaws

-- ====================================================================

-- completeness

cmplt : {A B : Fma} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊸ g) = ⊸r (⊸l (uf (cmplt f)) (cmplt g))
cmplt i = ⊸l Ir ax
cmplt j = ⊸r (Il (uf ax))
cmplt L = ⊸r (⊸r (⊸l (uf (⊸l (uf ax) ax)) ax))


-- ====================================================================

-- cmplt preserves equality

≐cmplt≗ : {A B : Fma} {f g : A ⇒ B} → f ≐ g → cmplt f ≗ cmplt g
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
≐cmplt≗ (ni {f = f}) = ⊸l refl (~ (≡-to-≗ (scut-ax (cmplt f))))
≐cmplt≗ (nj {f = f}) =
  proof≗
    ⊸r (Il (uf (scut (scut (cmplt f) ax) ax)))
  ≗〈 ⊸r (Il (uf (≡-to-≗ (scut-ax (scut (cmplt f) ax))))) 〉
    ⊸r (Il (uf (scut (cmplt f) ax)))
  ≗〈 ⊸r (Il (uf (≡-to-≗ (scut-ax (cmplt f))))) 〉
    ⊸r (Il (uf (cmplt f)))
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
    ⊸r (⊸r (Il (uf (⊸l (uf ax) ax))))
  ≗〈 ⊸r ⊸rIl 〉
    ⊸r (Il (⊸r (uf (⊸l (uf ax) ax))))
  ≗〈 ⊸r (Il ⊸ruf) 〉
    ⊸r (Il (uf (⊸r (⊸l (uf ax) ax))))
  ≗〈 ~ (⊸r (Il (uf ax⊸))) 〉
    ⊸r (Il (uf ax))
  qed≗
≐cmplt≗ iL = refl
≐cmplt≗ ij = ~ axI

