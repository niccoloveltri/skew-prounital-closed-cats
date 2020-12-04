module UniversalProperty where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Formulae
open import Utilities
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
               
    Fj : ∀{A} → Eq 𝔻 (subst₂ (Hom 𝔻) refl FLo (F₁ (jj ℂ {A}))) (jj 𝔻)
    Fi : ∀{A B} {e : Hom ℂ nothing A}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just FLo) refl (F₁ (ii ℂ {A}{B} e)))
               (ii 𝔻 (F₁ e))              
    FL : ∀{A B C}
      → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just FLo) (trans FLo (cong₂ (Lo₀ 𝔻) FLo FLo))
                                (F₁ (LL ℂ {A}{B}{C})))
              (LL 𝔻)
open StrPClFun

mapEq : {A B : Set}{f g : A → B}
  → (∀ x → f x ≡ g x)
  → ∀ x → map f x ≡ map g x
mapEq p nothing = refl
mapEq p (just x) = cong just (p x)

-- equality of strict prounital closed functors
--(we do not show it here, but this entails propositional equality of
-- these functors)
record EqFun {ℂ 𝔻 : SkPClCat} (F G : StrPClFun ℂ 𝔻) : Set where
  field
    Eq₀ : ∀ B → F₀ F B ≡ F₀ G B
    Eq₁ : ∀{S B} (f : ℂ .Hom S B)
      → Eq 𝔻 (subst₂ (Hom 𝔻) (mapEq Eq₀ S) (Eq₀ B) (F₁ F f))
               (F₁ G f)
open EqFun

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

  EqRefl : ∀{S B} {f g : Hom 𝔻 S B}
    → f ≡ g  → Eq 𝔻 f g
  EqRefl refl = Refl 𝔻

  EqSubst : ∀{S S' B B'} {f g : Hom 𝔻 S B}
    → (p : S ≡ S') (q : B ≡ B')
    → Eq 𝔻 f g 
    → Eq 𝔻 (subst₂ (Hom 𝔻) p q f) (subst₂ (Hom 𝔻) p q g)
  EqSubst refl refl r = r

  EqSubst₂ : ∀{S S' B B'} {f : Hom 𝔻 S B}
    → (p p' : S ≡ S') (q q' : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) p q f) (subst₂ (Hom 𝔻) p' q' f)
  EqSubst₂ refl refl refl refl = Refl 𝔻

  EqSubstId : ∀{B B'} (q : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just q) q (Id 𝔻)) (Id 𝔻)
  EqSubstId refl = Refl 𝔻

  EqSubstjj : ∀{B B'} (q : B ≡ B')
    → Eq 𝔻 (subst₂ (Hom 𝔻) refl (cong₂ (Lo₀ 𝔻) q q) (jj 𝔻)) (jj 𝔻)
  EqSubstjj refl = Refl 𝔻

  EqSubstii : ∀{A A' B B'} (p : A ≡ A') (q : B ≡ B')
    → (f : Hom 𝔻 nothing A)
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just (cong₂ (Lo₀ 𝔻) p q)) q (ii 𝔻 f))
             (ii 𝔻 (subst₂ (Hom 𝔻) refl p f))
  EqSubstii refl refl f = Refl 𝔻

  EqSubstLL : ∀{A A' B B' C C'} (p : A ≡ A') (q : B ≡ B') (r : C ≡ C')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just (cong₂ (Lo₀ 𝔻) q r)) (cong₂ (Lo₀ 𝔻) (cong₂ (Lo₀ 𝔻) p q) (cong₂ (Lo₀ 𝔻) p r)) (LL 𝔻)) (LL 𝔻)
  EqSubstLL refl refl refl = Refl 𝔻

  EqSubstComp : ∀{S S' B B' C C'} {f : Hom 𝔻 S B}{g : Hom 𝔻 (just B) C}
    → (p : S ≡ S') (q : B ≡ B') (r : C ≡ C')
    → Eq 𝔻 (subst₂ (Hom 𝔻) p r (Comp 𝔻 g f))
            (Comp 𝔻 (subst₂ (Hom 𝔻) (cong just q) r g)
                     (subst₂ (Hom 𝔻) p q f))
  EqSubstComp refl refl refl = Refl 𝔻

  EqSubstLo : ∀{A A' B B' C C' D D'} {f : Hom 𝔻 (just B) A}{g : Hom 𝔻 (just C) D}
    → (p : A ≡ A') (q : B ≡ B') (r : C ≡ C') (s : D ≡ D')
    → Eq 𝔻 (subst₂ (Hom 𝔻) (cong just (cong₂ (Lo₀ 𝔻) p r)) (cong₂ (Lo₀ 𝔻) q s) (Lo₁ 𝔻 f g))
             (Lo₁ 𝔻 (subst₂ (Hom 𝔻) (cong just q) p f) (subst₂ (Hom 𝔻) (cong just r) s g))
  EqSubstLo refl refl refl refl = Refl 𝔻

  𝔽Eq₀ : (B : Fma) → F₀ G B ≡ 𝔽₀ B
  𝔽Eq₀ (` X) = p
  𝔽Eq₀ (B ⊸ C) = trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))

  𝔽Eq₁ : ∀{S B} (f : S ⇒ B) → Eq 𝔻 (subst₂ (Hom 𝔻) (mapEq 𝔽Eq₀ S) (𝔽Eq₀ B) (F₁ G f)) (𝔽₁ f)
  𝔽Eq₁ (id {B}) =
    Trans 𝔻 (EqSubst (mapEq 𝔽Eq₀ (just B)) (𝔽Eq₀ B) (FId G))
             (EqSubstId (𝔽Eq₀ B))
  𝔽Eq₁ (_∘_ {S}{B}{C} f g) =
    Trans 𝔻 (Trans 𝔻 (EqSubst (mapEq 𝔽Eq₀ S) (𝔽Eq₀ C) (FComp G))
                       (EqSubstComp (mapEq 𝔽Eq₀ S) (𝔽Eq₀ B) (𝔽Eq₀ C)))
             (CompEq 𝔻 (𝔽Eq₁ f) (𝔽Eq₁ g))
  𝔽Eq₁ (_⊸_ {A}{B}{C}{D} f g) =
    Trans 𝔻 (Trans 𝔻 (Trans 𝔻 (subst (Eq 𝔻 _) (subst₂subst₂ (Hom 𝔻) (cong just (FLo G)) r (FLo G) r' _)
                                                               (EqSubst₂ q (trans (cong just (FLo G)) r) q' (trans (FLo G) r')))
                                 (EqSubst _ _ (FLo₁ G)))
                       (EqSubstLo (𝔽Eq₀ A) (𝔽Eq₀ B) (𝔽Eq₀ C) (𝔽Eq₀ D)))
             (LoEq 𝔻 (𝔽Eq₁ f) (𝔽Eq₁ g))
    where
      q = cong just (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C)))
      q' = trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ D))
      r = cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))
      r' = cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ D)
  𝔽Eq₁ (j {A}) =
    subst (λ x → Eq 𝔻 x (jj 𝔻)) (sym (subst₂subst₂ (Hom 𝔻) refl refl (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ A)) (F₁ G j)))
          (Trans 𝔻 (EqSubst refl (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ A)) (Fj G))
                    (EqSubstjj (𝔽Eq₀ A)))
  𝔽Eq₁ (i {A}{B} f) =
    Trans 𝔻 (Trans 𝔻 (Trans 𝔻 (subst (Eq 𝔻 _) (subst₂subst₂ (Hom 𝔻) (cong just (FLo G)) (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))) refl (𝔽Eq₀ B) _)
                                                  (EqSubst₂ (cong just (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))))
                                                            (trans (cong just (FLo G)) (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))))
                                                            (𝔽Eq₀ B)
                                                            (𝔽Eq₀ B)))
                                 (EqSubst (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))) (𝔽Eq₀ B) (Fi G)))
                       (EqSubstii (𝔽Eq₀ A) (𝔽Eq₀ B) (F₁ G f)))
             (iCong 𝔻 (𝔽Eq₁ f))
  𝔽Eq₁ (L {A}{B}{C}) =
    subst (λ x → Eq 𝔻 x (LL 𝔻))
      (trans (sym (subst₂subst₂ (Hom 𝔻) (cong just (FLo G))
                     (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))) (FLo G)
                     (cong₂ (Lo₀ 𝔻) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B)))
                      (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))))
                     _))
             (cong (λ x → subst₂ (Hom 𝔻) x
                                  (trans (FLo G)
                                         (cong₂ (Lo₀ 𝔻) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B)))
                                                         (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C)))))
                                  (F₁ G L)) (trans-cong (FLo G))))
      (Trans 𝔻 (Trans 𝔻 (subst₂ (Eq 𝔻) (subst₂subst₂ (Hom 𝔻) (cong just (FLo G))
                                                                 (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C)))
                                                                 (FLo G)
                                                                 (cong₂ (Lo₀ 𝔻) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C)))) _)
                                          (subst₂subst₂ (Hom 𝔻) (cong just (FLo G))
                                                                 (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C)))
                                                                 (trans (FLo G) (cong₂ (Lo₀ 𝔻) (FLo G) (FLo G)))
                                                                 (cong₂ (Lo₀ 𝔻) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B)) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))) _)
                                          (EqSubst₂ (trans (cong just (FLo G)) (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))))
                                                    (trans (cong just (FLo G)) (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C))))
                                                    (trans (FLo G) (cong₂ (Lo₀ 𝔻) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))) (trans (FLo G) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C)))))
                                                    (trans (trans (FLo G) (cong₂ (Lo₀ 𝔻) (FLo G) (FLo G))) (cong₂ (Lo₀ 𝔻) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B)) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))))))
                          (EqSubst (cong just (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ B) (𝔽Eq₀ C)))
                                   (cong₂ (Lo₀ 𝔻) (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ B))
                                                   (cong₂ (Lo₀ 𝔻) (𝔽Eq₀ A) (𝔽Eq₀ C))) (FL G)))
               (EqSubstLL (𝔽Eq₀ A) (𝔽Eq₀ B) (𝔽Eq₀ C)))

  𝔽-uniq : EqFun G 𝔽
  𝔽-uniq = record { Eq₀ = 𝔽Eq₀ ; Eq₁ = 𝔽Eq₁ }

-- the predicate characterizing the free skew prounital closed
-- category
record FreeSkPClCat (ℂ : SkPClCat) : Set₁ where
  field
    η : At → Obj ℂ
    F : ∀ 𝔻 (γ : At → Obj 𝔻) → StrPClFun ℂ 𝔻
    comm : ∀ 𝔻 γ {X : At} → F₀ (F 𝔻 γ) (η X) ≡ γ X
    uniq : ∀ 𝔻 γ (G : StrPClFun ℂ 𝔻) →
      ({X : At} → F₀ G (η X) ≡ γ X) → EqFun G (F 𝔻 γ)

-- Wrapping up: FSkPCl satisfies this universal property
FSkPCl-univ : FreeSkPClCat FSkPCl
FSkPCl-univ = record
  { η = `
  ; F = Exists.𝔽
  ; comm = λ _ _ → refl
  ; uniq = Unique.𝔽-uniq
  }
