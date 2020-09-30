{-# OPTIONS --rewriting #-}

module Compare where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Maybe renaming (map to mmap)
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Data.Unit 
open import Formulae
open import Sound

-- ==============================================================

-- Connecting focused sequent calculus and βη-long normal forms

-- ==============================================================

-- Focused sequent calculus (with more relaxed ax rule)

data _∣_⊢L_ : Stp → Cxt → Fma → Set
data _∣_⊢R_ : Fma → Cxt → Fma → Set

data _∣_⊢L_ where
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
            (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
  uf : {Γ : Cxt} → {A : Fma} {X : At} → 
            (f : just A ∣ Γ ⊢L ` X) →
            nothing ∣ A ∷ Γ ⊢L ` X
  switch :  {A : Fma} → 
            {Γ : Cxt} → {X : At} →
            (f : A ∣ Γ ⊢R ` X) → just A ∣ Γ ⊢L ` X 

data _∣_⊢R_ where
  ax : {A : Fma} → A ∣ [] ⊢R A
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
            (f : nothing ∣ Γ ⊢L A) → (g : B ∣ Δ ⊢R C) →
            A ⊸ B ∣ Γ ++ Δ ⊢R C

-- βη-long normal forms

data _∣_⊢nf_ : Stp → Cxt → Fma → Set
data _∣_⊢ne_ : Fma → Cxt → Fma → Set

data _∣_⊢nf_ where
  ⊸i : {S : Stp} {Γ : Cxt} {A B : Fma}
    → S ∣ Γ ++ A ∷ [] ⊢nf B → S ∣ Γ ⊢nf A ⊸ B
  uf : {Γ : Cxt} {A : Fma} {X : At}
    → just A ∣ Γ ⊢nf ` X → nothing ∣ A ∷ Γ ⊢nf ` X
  ne` : {A : Fma} {Γ : Cxt} {X : At}
    → A ∣ Γ ⊢ne ` X → just A ∣ Γ ⊢nf ` X

data _∣_⊢ne_ where
  ax : {A : Fma} → A ∣ [] ⊢ne A     
  ⊸e : {S : Fma} {Γ Δ : Cxt} {A B : Fma}
    → S ∣ Γ ⊢ne A ⊸ B → nothing ∣ Δ ⊢nf A
    → S ∣ Γ ++ Δ ⊢ne B

-- Substitutions in focused sequent calculus

data Sub-foc : Cxt → Cxt → Set where
  [] : Sub-foc [] []
  _∷_ : ∀{Γ Δ As A}
    → (t : nothing ∣ Γ ⊢L A) → (s : Sub-foc Δ As)
    → Sub-foc (Γ ++ Δ) (A ∷ As)

_∷f_ : ∀{Γ Δ As A}
    → (s : Sub-foc Γ As) → (t : nothing ∣ Δ ⊢L A)
    → Sub-foc (Γ ++ Δ) (As ++ A ∷ [])
[] ∷f t = t ∷ []
(t' ∷ s) ∷f t = t' ∷ (s ∷f t)

_++f_ : ∀{Γ Γ' As As'}
    → (s : Sub-foc Γ As) (s' : Sub-foc Γ' As')
    → Sub-foc (Γ ++ Γ') (As ++ As')
[] ++f s' = s'
(t ∷ s) ++f s' = t ∷ (s ++f s')    

ru++f : ∀{Γ As}
    → (s : Sub-foc Γ As)
    → s ++f [] ≡ s
ru++f [] = refl
ru++f (t ∷ s) = cong (t ∷_) (ru++f s)

∷f++f : ∀{Γ Γ' Δ As As' A}
    → (s : Sub-foc Γ As)
    → (u : nothing ∣ Δ ⊢L A)
    → (s' : Sub-foc Γ' As')
    → s ++f (u ∷ s') ≡ (s ∷f u) ++f s'
∷f++f [] u s' = refl
∷f++f (t ∷ s) u s' = cong (t ∷_) (∷f++f s u s')

-- Substitutions in normal forms

data Sub-nf : Cxt → Cxt → Set where
  [] : Sub-nf [] []
  _∷ₛ_ : ∀{Γ Δ As A}
    → (s : Sub-nf Γ As) → (t : nothing ∣ Δ ⊢nf A)
    → Sub-nf (Γ ++ Δ) (As ++ A ∷ [])

_∷n_ : ∀{Γ Δ As A}
    → (t : nothing ∣ Γ ⊢nf A) → (s : Sub-nf Δ As)
    → Sub-nf (Γ ++ Δ) (A ∷ As)
t ∷n [] = [] ∷ₛ t
t ∷n (s ∷ₛ t₁) = (t ∷n s) ∷ₛ t₁

_++n_ : ∀{Γ Γ' As As'}
    → (s : Sub-nf Γ As) (s' : Sub-nf Γ' As')
    → Sub-nf (Γ ++ Γ') (As ++ As')
s ++n [] = s
_++n_ {As = As} s (_∷ₛ_  {As = As₁} {A} s' t) =
  _∷ₛ_ {As = As ++ As₁} (s ++n s') t

lu++n : ∀{Γ As}
    → (s : Sub-nf Γ As)
    → [] ++n s ≡ s
lu++n [] = refl
lu++n (s ∷ₛ t) = cong (_∷ₛ t) (lu++n s)

++n∷n : ∀{Γ Γ' Δ As As' A}
    → (s : Sub-nf Γ As) (s' : Sub-nf Γ' As') (t : nothing ∣ Δ ⊢nf A)
    → ((s ∷ₛ t) ++n s') ≡ (s ++n (t ∷n s'))
++n∷n s [] t = refl
++n∷n {Γ} {Δ = Δ} {As} s (_∷ₛ_ {Γ₁} {As = As₁} s' t₁) t =
  cong (λ x → _∷ₛ_ {Γ = Γ ++ Δ ++ Γ₁} {As = As ++ _ ∷ As₁} x t₁)
    (++n∷n s s' t)

-- Repeated applications of ⊸l rule

⊸l⋆ : ∀ {Γ Δ As B C}
  → Sub-foc Γ As
  → B ∣ Δ ⊢R C
  → [ As ∣ B ] ∣ Γ ++ Δ ⊢R C
⊸l⋆ [] u = u
⊸l⋆ (t ∷ s) u = ⊸l t (⊸l⋆ s u)

-- Repeated applications of ⊸e rule

⊸e⋆ : ∀ {Γ As C}
  → Sub-nf Γ As
  → [ As ∣ C ] ∣ Γ ⊢ne C
⊸e⋆ [] = ax
⊸e⋆ (s ∷ₛ t) = ⊸e (⊸e⋆ s) t

⊸e⋆gen : ∀ {S Γ Δ As C} (f : S ∣ Γ ⊢ne [ As ∣ C ]) (s : Sub-nf Δ As)
  → S ∣ Γ ++ Δ ⊢ne C
⊸e⋆gen ax s = ⊸e⋆ s
⊸e⋆gen (⊸e f t) s = ⊸e⋆gen f (t ∷n s)

-- Translations between the two calculi

nf2focL : ∀ {S Γ C} → S ∣ Γ ⊢nf C → S ∣ Γ ⊢L C
ne2focR : ∀ {S Γ Δ As B} → S ∣ Γ ⊢ne [ As ∣ B ] → Sub-foc Δ As
  → S ∣ Γ ++ Δ ⊢R B

nf2focL (⊸i f) = ⊸r (nf2focL f)
nf2focL (uf f) = uf (nf2focL f)
nf2focL (ne` f) = switch (ne2focR f [])


ne2focR ax s = ⊸l⋆ s ax
ne2focR (⊸e f t) s = ne2focR f (nf2focL t ∷ s)


focL2nf : ∀ {S Γ C} → S ∣ Γ ⊢L C → S ∣ Γ ⊢nf C
focR2ne : ∀ {Γ Δ As B C} → Sub-nf Γ As → B ∣ Δ ⊢R C
  → [ As ∣ B ] ∣ Γ ++ Δ ⊢ne C

focL2nf (⊸r f) = ⊸i (focL2nf f)
focL2nf (uf f) = uf (focL2nf f)
focL2nf {just A} (switch f) = ne` (focR2ne [] f)

focR2ne s ax = ⊸e⋆ s
focR2ne s (⊸l f t) = focR2ne (s ∷ₛ focL2nf f) t

-- Translations between substitutions

sub-nf2focL : ∀ {Γ As} → Sub-nf Γ As
  → Sub-foc Γ As
sub-nf2focL [] = []
sub-nf2focL (s ∷ₛ t) = sub-nf2focL s ∷f nf2focL t

sub-foc2nf : ∀ {Γ As} → Sub-foc Γ As
  → Sub-nf Γ As
sub-foc2nf [] = []
sub-foc2nf (t ∷ s) = (focL2nf t) ∷n (sub-foc2nf s)

-- Interaction between ⊸l⋆ and _∷f_

⊸l⋆∷f : ∀ {Γ Γ' Δ As A B C}
  → (s : Sub-foc Γ As)
  → (u : nothing ∣ Γ' ⊢L A)
  → (t : B ∣ Δ ⊢R C)
  → ⊸l⋆ (s ∷f u) t ≡ ⊸l⋆ s (⊸l u t)
⊸l⋆∷f [] f t = refl
⊸l⋆∷f (t₁ ∷ s) f t = cong (⊸l t₁) (⊸l⋆∷f s f t)

-- The function ⊸e⋆gen is defined by pattern-matching on its first
-- argument, we need to explain how it beheaves when the second
-- argument is of the form [] and _∷ₛ_

⊸e⋆gen∷ₛ : ∀ {S Γ Δ Δ' As A C} (f : S ∣ Γ ⊢ne [ As ∣ A ⊸ C ])
  → (s : Sub-nf Δ As) (t : nothing ∣ Δ' ⊢nf A)
  → ⊸e⋆gen f (s ∷ₛ t) ≡ ⊸e (⊸e⋆gen f s) t
⊸e⋆gen∷ₛ ax s t = refl
⊸e⋆gen∷ₛ (⊸e f u) s t = ⊸e⋆gen∷ₛ f (u ∷n s) t  

⊸e⋆gen[] : ∀ {S Γ C} (f : S ∣ Γ ⊢ne C)
  → ⊸e⋆gen f [] ≡ f
⊸e⋆gen[] ax = refl
⊸e⋆gen[] (⊸e f t) =
  trans (⊸e⋆gen∷ₛ f [] t)
    (cong (λ x → ⊸e x t) (⊸e⋆gen[] f))

-- Action of the translation ne2focR on ⊸e⋆

ne2focR⊸e⋆ : ∀ {Γ Γ' As As' C}
  → (s : Sub-nf Γ As)
  → (s' : Sub-foc Γ' As')
  → ne2focR (⊸e⋆ {C = [ As' ∣ C ]} s) s'
           ≡ ⊸l⋆ (sub-nf2focL s ++f s') ax
ne2focR⊸e⋆ [] [] = refl
ne2focR⊸e⋆ [] (t ∷ s') =
  cong (⊸l t) (ne2focR⊸e⋆ [] s')
ne2focR⊸e⋆ (s ∷ₛ t) s' =
  trans (ne2focR⊸e⋆ s (nf2focL t ∷ s'))
    (cong (λ x → ⊸l⋆ x ax) (∷f++f (sub-nf2focL s) (nf2focL t) s'))

-- Action of the translation focR2nf on ⊸l⋆

focRnf⊸l⋆ : ∀ {Γ As Γ' As' C}
  → (s : Sub-foc Γ As) (s' : Sub-nf Γ' As') 
  → focR2ne s' (⊸l⋆ s ax)
       ≡ ⊸e⋆ {C = C} (s' ++n (sub-foc2nf s))
focRnf⊸l⋆ [] s' = refl
focRnf⊸l⋆ (t ∷ s) s' =
  trans (focRnf⊸l⋆ s (s' ∷ₛ focL2nf t))
    (cong ⊸e⋆ (++n∷n s' (sub-foc2nf s) (focL2nf t)))

-- The translations form an isomorphism

focL2nf2focL : ∀ {S Γ C} (f : S ∣ Γ ⊢L C)
  → nf2focL (focL2nf f) ≡ f
focR2nf2focR : ∀ {Γ Δ As B X}
  → (s : Sub-nf Γ As) (f : B ∣ Δ ⊢R ` X)
  → ne2focR (focR2ne s f) [] ≡ ⊸l⋆ (sub-nf2focL s) f


focL2nf2focL (⊸r f) = cong ⊸r (focL2nf2focL f)
focL2nf2focL (uf f) = cong uf (focL2nf2focL f)
focL2nf2focL {just A} (switch f) = cong switch (focR2nf2focR [] f)

focR2nf2focR s ax =
  trans (ne2focR⊸e⋆ s [])
    (cong (λ x → ⊸l⋆ x ax) (ru++f (sub-nf2focL s)))
focR2nf2focR s (⊸l f t) =
  trans (focR2nf2focR (s ∷ₛ focL2nf f) t)
    (trans (cong (λ x → ⊸l⋆ (sub-nf2focL s ∷f x) t) (focL2nf2focL f))
      (⊸l⋆∷f (sub-nf2focL s) f t))


nf2focL2nf : ∀ {S Γ C} (f : S ∣ Γ ⊢nf C)
  → focL2nf (nf2focL f) ≡ f
ne2focR2ne : ∀ {S Γ Δ As X}
  → (t : S ∣ Δ ⊢ne [ As ∣ ` X ]) (s : Sub-foc Γ As)
  → focR2ne [] (ne2focR t s) ≡
       ⊸e⋆gen {C = ` X} t (sub-foc2nf s)

ne2focR2ne ax s =
  trans (focRnf⊸l⋆ s []) (cong ⊸e⋆ (lu++n _))
ne2focR2ne (⊸e t u) s =
  trans (ne2focR2ne t (nf2focL u ∷ s))
    (cong (λ x → ⊸e⋆gen t (x ∷n sub-foc2nf s)) (nf2focL2nf u))

nf2focL2nf (⊸i f) = cong ⊸i (nf2focL2nf f)
nf2focL2nf (uf f) = cong uf (nf2focL2nf f)
nf2focL2nf (ne` f) =
  cong ne` (trans (ne2focR2ne  f []) (⊸e⋆gen[] f))

-- ==================================================================

-- To conclude, we connect the two formulations of focused sequent
-- calculus (with different ax rules)

open import Focusing renaming (_∣_⊢L_ to _∣_⊢L'_
                             ; _∣_⊢R_ to _∣_⊢R'_
                             ; ⊸l-focus to ⊸l-focus')

L2L' : ∀{S Γ A} → S ∣ Γ ⊢L A → S ∣ Γ ⊢L' A
R2L' : ∀{Γ A C} → A ∣ Γ ⊢R C → just A ∣ Γ ⊢L' C

L2L' (⊸r f) = ⊸r (L2L' f)
L2L' (uf f) = uf tt (L2L' f)
L2L' (switch f) = R2L' f

R2L' ax = ax-focus
R2L' (⊸l f g) = ⊸l-focus' (L2L' f) (R2L' g)

L'2L : ∀{S Γ A} → S ∣ Γ ⊢L' A → S ∣ Γ ⊢L A
R'2R : ∀{Γ A C} → just A ∣ Γ ⊢R' C → A ∣ Γ ⊢R C

L'2L (⊸r f) = ⊸r (L'2L f)
L'2L {A = ` X} (uf p f) = uf (L'2L f)
L'2L {just A} {A = ` X} (switch q f) = switch (R'2R f)

R'2R ax = ax
R'2R (⊸l f g) = ⊸l (L'2L f) (R'2R g)

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (switch g) = switch (⊸l f g)

L'2L⊸l-focus : ∀{Γ Δ A B C}
  → (f : nothing ∣ Γ ⊢L' A) (g : just B ∣ Δ ⊢L' C)
  → L'2L (⊸l-focus' f g) ≡ ⊸l-focus (L'2L f) (L'2L g)
L'2L⊸l-focus f (⊸r g) = cong ⊸r (L'2L⊸l-focus f g)
L'2L⊸l-focus {C = ` X} f (switch q g) = refl

L2L'2L : ∀{S Γ A} (f : S ∣ Γ ⊢L A) → L'2L (L2L' f) ≡ f
R2L'2L : ∀{S Γ X} (f : S ∣ Γ ⊢R ` X) → L'2L (R2L' f) ≡ switch f

L2L'2L (⊸r f) = cong ⊸r (L2L'2L f)
L2L'2L (uf f) = cong uf (L2L'2L f)
L2L'2L (switch f) = R2L'2L f

R2L'2L ax = refl
R2L'2L (⊸l f g) =
  trans (L'2L⊸l-focus (L2L' f) (R2L' g))
    (cong₂ ⊸l-focus (L2L'2L f) (R2L'2L g))

L'2L2L' : ∀{S Γ A} (f : S ∣ Γ ⊢L' A) → L2L' (L'2L f) ≡ f
R'2R2R' : ∀{Γ A X} (f : just A ∣ Γ ⊢R' ` X) → R2L' (R'2R f) ≡ switch tt f

L'2L2L' (⊸r f) = cong ⊸r (L'2L2L' f)
L'2L2L' {A = ` X} (uf tt f) = cong (uf tt) (L'2L2L' f)
L'2L2L' {just A} {A = ` X} (switch tt f) = R'2R2R' f

R'2R2R' ax = refl
R'2R2R' (⊸l f g) = cong₂ ⊸l-focus' (L'2L2L' f) (R'2R2R' g)
