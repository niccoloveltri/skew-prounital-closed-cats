module UniversalProperty where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Formulae
open import FreeSkewProunitalClosed

-- The type of skew prounital closed categories
record SkPClCat : Set₁ where
  field
    Obj : Set
    Lo₀ : Obj → Obj → Obj
   
    Hom : Maybe Obj → Obj → Set
    Id : {B : Obj} → Hom (just B) B
    Comp : ∀{S}{B C : Obj} → Hom (just B) C → Hom S B → Hom S C
    Lo₁ : {E B C D : Obj} → Hom (just B) E → Hom (just C) D
      → Hom (just (Lo₀ E C)) (Lo₀ B D)
    jj : ∀{A} → Hom nothing (Lo₀ A A)
    ii : ∀{A B} → Hom nothing A → Hom (just (Lo₀ A B)) B
    LL : ∀{A B C} → Hom (just (Lo₀ B C)) (Lo₀ (Lo₀ A B) (Lo₀ A C))

    Eq : ∀ {S}{B : Obj} → Hom S B → Hom S B → Set
    Refl : ∀{S}{B : Obj} {f : Hom S B} → Eq f f
    Sym : ∀{S}{B : Obj} {f g : Hom S B} → Eq f g → Eq g f
    Trans : ∀{S}{B : Obj} {f g h : Hom S B} → Eq f g → Eq g h → Eq f h
    CompEq : ∀{S}{B C : Obj} {f g : Hom (just B) C} {h k : Hom S B} →
           Eq f g → Eq h k → Eq (Comp f h) (Comp g k)
    LoEq : {E B C D : Obj} {f g : Hom (just E) C} {h k : Hom (just B) D} →
                           Eq f g → Eq h k → Eq (Lo₁ f h) (Lo₁ g k)
    Lid : ∀{S}{B : Obj} {f : Hom S B} → Eq (Comp Id f) f
    Rid : {C B : Obj} {f : Hom (just C) B} → Eq f (Comp f Id)
    Ass : ∀{S}{B C D : Obj}
        → {f : Hom (just C) D} {g : Hom (just B) C} {h : Hom S B}
         → Eq (Comp (Comp f g) h) (Comp f (Comp g h))
    fLo₁Id : {C B : Obj} → Eq (Lo₁ (Id {C}) (Id {B})) (Id {Lo₀ C B})
    fLo₁Comp : {G B C D E F : Obj}
          → {f : Hom (just G) C} {g : Hom (just B) D}
          → {h : Hom (just C) E} {k : Hom (just D) F} →  
                Eq (Lo₁ (Comp h f) (Comp k g)) (Comp (Lo₁ f k) (Lo₁ h g))

    iCong : ∀{A B} {f g : Hom nothing A} → Eq f g
      → Eq (ii {A}{B} f) (ii {A}{B} g)
  
    Ni : ∀{A B C D}
      → {e : Hom nothing A} {g : Hom (just B) C} {h : Hom (just A) D}
      → Eq (Comp (Comp g (ii e)) (Lo₁ h Id)) (Comp (ii (Comp h e)) (Lo₁ Id g))
    Nj : ∀{A B} {f : Hom (just A) B}
      → Eq (Comp (Lo₁ f Id) jj) (Comp (Lo₁ Id f) jj)
    NL : ∀{A B C D E F}
      → {f : Hom (just A) D} {g : Hom (just E) B} {h : Hom (just C) F}
      → Eq (Comp (Lo₁ (Lo₁ f g) (Lo₁ Id h)) LL)
            (Comp (Comp (Lo₁ Id (Lo₁ f Id)) LL) (Lo₁ g h))


    LLLEq : ∀{A B C D} → Eq (Comp (Lo₁ Id (LL {A})) (LL {B}{C}{D}))
                         (Comp (Comp (Lo₁ (LL {A}{B}{C}) Id) LL) (LL {A}{C}{D}))
    ijLEq : ∀{A C} → Eq (Comp (ii (jj {A})) (LL {A}{A}{C})) (Id {Lo₀ A C})
    LjEq : ∀{A B} → Eq (Comp LL jj) (jj {Lo₀ A B})
    iLEq : ∀{A B C} {e : Hom nothing A}
      → Eq (Comp (Lo₁ Id (ii e)) (LL {A} {B} {C})) (Lo₁ (ii e) Id)
    ijEq : ∀{A} {e : Hom nothing A} → Eq (Comp (ii e) jj) e
open SkPClCat

-- the categorical calculus defines a skew prounital closed category
FSkPCl : SkPClCat
FSkPCl = record
           { Obj = Fma
           ; Lo₀ = _⊸_
           ; Hom = _⇒_
           ; Id = id
           ; Comp = _∘_
           ; Lo₁ = _⊸_
           ; jj = j
           ; ii = i
           ; LL = L
           ; Eq = _≐_
           ; Refl = refl
           ; Sym = ~_
           ; Trans = _∙_
           ; CompEq = _∘_
           ; LoEq = _⊸_
           ; Lid = lid
           ; Rid = rid
           ; Ass = ass
           ; fLo₁Id = f⊸id
           ; fLo₁Comp = f⊸∘
           ; iCong = i
           ; Ni = ni
           ; Nj = nj
           ; NL = nL
           ; LLLEq = LLL
           ; ijLEq = ijL
           ; LjEq = Lj
           ; iLEq = iL
           ; ijEq = ij
           }

-- The type of strict prounital closed functors
record StrPClFun (ℂ 𝔻 : SkPClCat) : Set where
  field
    F₀ : ℂ .Obj → 𝔻 .Obj
    F₁ : ∀{S B} → ℂ .Hom S B → 𝔻 .Hom (map F₀ S) (F₀ B)
    FEq : ∀{S C} {f g : Hom ℂ S C} → Eq ℂ f g → Eq 𝔻 (F₁ f) (F₁ g)
    FId : ∀{A} → 𝔻 .Eq (F₁ (ℂ .Id {A})) (𝔻 .Id {F₀ A})
    FComp : ∀{S C D} {g : Hom ℂ (just C) D} {f : Hom ℂ S C} →
           Eq 𝔻 (F₁ (Comp ℂ g f)) (Comp 𝔻 (F₁ g) (F₁ f))
    FLo : ∀{A B} → F₀ (Lo₀ ℂ A B) ≡ Lo₀ 𝔻 (F₀ A) (F₀ B)
    FLo₁ : ∀{A B C D} {f : Hom ℂ (just A) B} {g : Hom ℂ (just C) D}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just FLo) FLo (F₁ (Lo₁ ℂ f g)))
               (Lo₁ 𝔻 (F₁ f) (F₁ g))
               
    Fj : ∀{A} → Eq 𝔻 (F₁ (jj ℂ {A})) (subst (Hom 𝔻 nothing) (sym FLo) (jj 𝔻))
    Fi : ∀{A B} {e : Hom ℂ nothing A}
      → Eq 𝔻 (F₁ (ii ℂ {A}{B} e))
              (subst (λ x → Hom 𝔻 (just x) (F₀ B)) (sym FLo) (ii 𝔻 (F₁ e))) 
    FL : ∀{A B C}
      → Eq 𝔻 (F₁ (LL ℂ {A}{B}{C}))
              (subst₂ (Hom 𝔻) (cong just (sym FLo))
                               (sym (trans FLo (cong₂ (Lo₀ 𝔻) FLo FLo)))
                               (LL 𝔻))
open StrPClFun

-- existence of a strict prounital closed functor between FSkPCl and
-- any other skew prounital closed category D with γ : At → 𝔻
module Exists (𝔻 : SkPClCat) (γ : At → Obj 𝔻) where

  𝔽₀ : Fma → Obj 𝔻
  𝔽₀ (` X) = γ X
  𝔽₀ (A ⊸ B) = Lo₀ 𝔻 (𝔽₀ A) (𝔽₀ B)

  𝔽₁ : ∀{S}{C : Fma} → S ⇒ C → Hom 𝔻 (map 𝔽₀ S) (𝔽₀ C)
  𝔽₁ id = Id 𝔻
  𝔽₁ (f ∘ f₁) = Comp 𝔻 (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (f ⊸ f₁) = Lo₁ 𝔻 (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ j = jj 𝔻
  𝔽₁ (i f) = ii 𝔻 (𝔽₁ f)
  𝔽₁ L = LL 𝔻

  𝔽Eq : ∀{S}{C : Fma} {f g : S ⇒ C} →
        f ≐ g → Eq 𝔻 (𝔽₁ f) (𝔽₁ g)
  𝔽Eq refl = Refl 𝔻
  𝔽Eq (~ p) = Sym 𝔻 (𝔽Eq p)
  𝔽Eq (p ∙ p₁) = Trans 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq (p ∘ p₁) = CompEq 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq (p ⊸ p₁) = LoEq 𝔻 (𝔽Eq p) (𝔽Eq p₁)
  𝔽Eq lid = Lid 𝔻
  𝔽Eq rid = Rid 𝔻
  𝔽Eq ass = Ass 𝔻
  𝔽Eq f⊸id = fLo₁Id 𝔻
  𝔽Eq f⊸∘ = fLo₁Comp 𝔻
  𝔽Eq (i p) = iCong 𝔻 (𝔽Eq p)
  𝔽Eq ni = Ni 𝔻
  𝔽Eq nj = Nj 𝔻
  𝔽Eq nL = NL 𝔻
  𝔽Eq LLL = LLLEq 𝔻
  𝔽Eq ijL = ijLEq 𝔻
  𝔽Eq Lj = LjEq 𝔻
  𝔽Eq iL = iLEq 𝔻
  𝔽Eq ij = ijEq 𝔻

  𝔽 : StrPClFun FSkPCl 𝔻
  𝔽 = record
        { F₀ = 𝔽₀
        ; F₁ = 𝔽₁
        ; FEq = 𝔽Eq
        ; FId = Refl 𝔻
        ; FComp = Refl 𝔻
        ; FLo = refl
        ; FLo₁ = Refl 𝔻
        ; Fj = Refl 𝔻
        ; Fi = Refl 𝔻
        ; FL = Refl 𝔻
        }

-- uniqueness of such strict prounital closed functor
module Unique (𝔻 : SkPClCat)
              (γ : At → Obj 𝔻)
              (G : StrPClFun FSkPCl 𝔻)
              (p : {X : At} → F₀ G (` X) ≡ γ X)
              where

  open Exists 𝔻 γ

  𝔽Eq₀ : (B : Fma) → F₀ G B ≡ 𝔽₀ B
  𝔽Eq₀ (` X) = p
  𝔽Eq₀ (B ⊸ C) = trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))

{-

NB: Notice that we have only proved an equality between the action on
objects of the two functors, which is generally not enough to conclude
that G is equal to 𝔽. But in the current case it is enough: one can
show that the two action on morphisms are also equal (more precisely
related by Eq 𝔻). We do not give a formal Agda proof of this fact,
since this requires a lot of boring lemmata involving subst and
subst₂...

Instead we give an informal sketch of the proof, where we write =D for
Eq 𝔻:

Given f : S ⇒ B, show that F₁ G f =D 𝔽₁ f
(which type-checks since F₀ G B = 𝔽₀ B for all objects B, that we
treat as a judgemental equality)

- case f = id_B
  F₁ G id_B =D id_{F₀ G B} = id_{𝔽₀ B} = 𝔽₁ id_B 

- case f = g ∘ f
  F₁ G (g ∘ f) =D F₁ G g ∘ F₁ G f =D 𝔽₁ g ∘ 𝔽₁ f = 𝔽₁ (g ∘ f)

- case f = j_B
  F₁ G j_B =D j_{F₀ G B} = j_{𝔽₀ B} = 𝔽₁ j_B

etc.
-}

