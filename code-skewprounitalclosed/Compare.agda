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

data _∣_⊢L_ : Stp → Cxt → Fma → Set
data _∣_⊢R_ : Stp → Cxt → Fma → Set

data _∣_⊢L_ where
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
            (f : S ∣ Γ ++ A ∷ [] ⊢L B) → S ∣ Γ ⊢L A ⊸ B
  uf : {Γ : Cxt} → {A : Fma} {X : At} → 
            (f : just A ∣ Γ ⊢L ` X) →
            nothing ∣ A ∷ Γ ⊢L ` X
  switch :  {S : Stp} → 
            {Γ : Cxt} → {X : At} →
            (f : S ∣ Γ ⊢R ` X) → S ∣ Γ ⊢L ` X 

data _∣_⊢R_ where
  ax : {X : At} → just (` X) ∣ [] ⊢R ` X
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
            (f : nothing ∣ Γ ⊢L A) → (g : just B ∣ Δ ⊢R C) →
            just (A ⊸ B) ∣ Γ ++ Δ ⊢R C


data _∣_⊢nf_ : Stp → Cxt → Fma → Set 
data _∣_⊢ne_ : Stp → Cxt → Fma → Set 

data _∣_⊢nf_ where
  ⊸i : {S : Stp} {Γ : Cxt} {A B : Fma}
      → S ∣ Γ ++ A ∷ [] ⊢nf B → S ∣ Γ ⊢nf A ⊸ B
  uf : {Γ : Cxt} {A : Fma} {X : At}
      → just A ∣ Γ ⊢nf ` X → nothing ∣ A ∷ Γ ⊢nf ` X
  ne` : {S : Stp} {Γ : Cxt} {X : At}
      → S ∣ Γ ⊢ne ` X → S ∣ Γ ⊢nf ` X

data _∣_⊢ne_ where
  ax : {A : Fma} → just A ∣ [] ⊢ne A     
  ⊸e : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
    → S ∣ Γ ⊢ne A ⊸ B → nothing ∣ Δ ⊢nf A
    → S ∣ Γ ++ Δ ⊢ne B

uf-focus : {Γ : Cxt} → {A C : Fma} →
          just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
uf-focus (⊸r f) = ⊸r (uf-focus f)
uf-focus (switch f) = uf (switch f)

⊸l-focus : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢L A → just B ∣ Δ ⊢L C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢L C
⊸l-focus f (⊸r g) = ⊸r (⊸l-focus f g)
⊸l-focus f (switch g) = switch (⊸l f g)

ax-focus : {A : Fma} → just A ∣ [] ⊢L A
ax-focus {` X} = switch ax
ax-focus {A ⊸ B} = ⊸r (⊸l-focus (uf-focus (ax-focus {A})) (ax-focus {B}))

data Sub-foc : Cxt → Cxt → Set where
  [] : Sub-foc [] []
  _∷_ : ∀{Γ Δ As A}
    → (t : nothing ∣ Γ ⊢L A) → (s : Sub-foc Δ As)
    → Sub-foc (Γ ++ Δ) (A ∷ As)

nf2foc : ∀ {S Γ C} → S ∣ Γ ⊢nf C → S ∣ Γ ⊢L C
ne2foc : ∀ {S Γ Δ As B} → S ∣ Γ ⊢ne [ As ∣ B ] → Sub-foc Δ As
  → S ∣ Γ ++ Δ ⊢L B

nf2foc (⊸i f) = ⊸r (nf2foc f)
nf2foc (uf f) = uf (nf2foc f)
nf2foc (ne` f) = ne2foc f []

ne2foc ax [] = ax-focus
ne2foc ax (t ∷ s) = ⊸l-focus t (ne2foc ax s)
ne2foc (⊸e f t) s = ne2foc f (nf2foc t ∷ s)

data Sub-nf : Cxt → Cxt → Set where
  [] : Sub-nf [] []
  _∷ₛ_ : ∀{Γ Δ As A}
    → (s : Sub-nf Γ As) → (t : nothing ∣ Δ ⊢nf A)
    → Sub-nf (Γ ++ Δ) (As ++ A ∷ [])

⊸e-sub : ∀ {Γ As C}
  → Sub-nf Γ As
  → just [ As ∣ C ] ∣ Γ ⊢ne C
⊸e-sub [] = ax
⊸e-sub ([] ∷ₛ t) = ⊸e ax t
⊸e-sub ((s ∷ₛ u) ∷ₛ t) = ⊸e (⊸e-sub (s ∷ₛ u)) t

focL2nf : ∀ {S Γ C} → S ∣ Γ ⊢L C → S ∣ Γ ⊢nf C
focR2nf : ∀ {Γ Δ As B C} → Sub-nf Γ As → just B ∣ Δ ⊢R C
  → just [ As ∣ B ] ∣ Γ ++ Δ ⊢ne C

focL2nf (⊸r f) = ⊸i (focL2nf f)
focL2nf (uf f) = uf (focL2nf f)
focL2nf {just A} (switch f) = ne` (focR2nf [] f)

focR2nf s ax = ⊸e-sub s
focR2nf s (⊸l f t) = focR2nf (s ∷ₛ focL2nf f) t



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

sub-nf2foc : ∀ {Γ As} → Sub-nf Γ As
  → Sub-foc Γ As
sub-nf2foc [] = []
sub-nf2foc (s ∷ₛ t) = sub-nf2foc s ∷f nf2foc t

⊸l-sub : ∀ {Γ Δ As B C}
  → Sub-foc Γ As
  → just B ∣ Δ ⊢R C
  → just [ As ∣ B ] ∣ Γ ++ Δ ⊢R C
⊸l-sub [] u = u
⊸l-sub (t ∷ s) u = ⊸l t (⊸l-sub s u)

⊸l-sub-∷f : ∀ {Γ Γ' Δ As A B C}
  → (s : Sub-foc Γ As)
  → (u : nothing ∣ Γ' ⊢L A)
  → (t : just B ∣ Δ ⊢R C)
  → ⊸l-sub (s ∷f u) t ≡ ⊸l-sub s (⊸l u t)
⊸l-sub-∷f [] f t = refl
⊸l-sub-∷f (t₁ ∷ s) f t = cong (⊸l t₁) (⊸l-sub-∷f s f t)

ne2foc-⊸e-sub : ∀ {Γ Γ' As As' X}
  → (s : Sub-nf Γ As)
  → (s' : Sub-foc Γ' As')
  → ne2foc (⊸e-sub {C = [ As' ∣ ` X ]} s) s'
           ≡ switch (⊸l-sub (sub-nf2foc s ++f s') ax)
ne2foc-⊸e-sub [] [] = refl
ne2foc-⊸e-sub [] (t ∷ s') =
  cong (⊸l-focus t) (ne2foc-⊸e-sub [] s')
ne2foc-⊸e-sub ([] ∷ₛ t) s' =
  cong (⊸l-focus (nf2foc t)) (ne2foc-⊸e-sub [] s')
ne2foc-⊸e-sub ((s ∷ₛ t) ∷ₛ u) s' =
  trans (ne2foc-⊸e-sub (s ∷ₛ t) (nf2foc u ∷ s'))
    (cong (λ x → switch (⊸l-sub x ax)) (∷f++f (sub-nf2foc s ∷f nf2foc t) _ _))

foc2nf2focL : ∀ {S Γ C} (f : S ∣ Γ ⊢L C)
  → nf2foc (focL2nf f) ≡ f
foc2nf2focR : ∀ {Γ Δ As B X}
  → (s : Sub-nf Γ As) (f : just B ∣ Δ ⊢R ` X)
  → ne2foc (focR2nf s f) [] ≡ switch (⊸l-sub (sub-nf2foc s) f)


foc2nf2focL (⊸r f) = cong ⊸r (foc2nf2focL f)
foc2nf2focL (uf f) = cong uf (foc2nf2focL f)
foc2nf2focL {just A} (switch f) = foc2nf2focR [] f

foc2nf2focR s ax =
  trans (ne2foc-⊸e-sub s [])
    (cong (λ x → switch (⊸l-sub x ax)) (ru++f _))
foc2nf2focR s (⊸l f t) =
  trans (foc2nf2focR (s ∷ₛ focL2nf f) t)
    (cong switch
      (trans (cong (λ x → ⊸l-sub (sub-nf2foc s ∷f x) t) (foc2nf2focL f))
        (⊸l-sub-∷f (sub-nf2foc s) f t)))

