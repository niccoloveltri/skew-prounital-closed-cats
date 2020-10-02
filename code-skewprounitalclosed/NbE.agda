{-# OPTIONS --rewriting #-}

-- =======================================================================
-- -- Normalization by Evaluation for Linear Lambda Calculus
-- =======================================================================

module NbE where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae
open import Compare
open import HeredSubs

-- Substitutions

data Sub : Cxt → Cxt → Set where
  [] : Sub [] []
  _∷_ : ∀{Γ}{Δ₁}{Δ₂}{A} → nothing ∣ Δ₁ ⊢ A → Sub Γ Δ₂ → Sub (A ∷ Γ) (Δ₁ ++ Δ₂)

-- -- Concatenation of substitutions

infixr 5 _++S_

_++S_ : ∀{Γ₁ Γ₂ Δ₁ Δ₂} → Sub Γ₁ Δ₁ → Sub Γ₂ Δ₂ → Sub (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)
[] ++S σ₂ = σ₂
(t ∷ σ₁) ++S σ₂ = t ∷ (σ₁ ++S σ₂)

is++S : ∀{Γ₁ Γ₂ Δ} (σ : Sub (Γ₁ ++ Γ₂) Δ)
  → Σ Cxt (λ Δ₁ → Σ Cxt (λ Δ₂ → Σ (Δ ≡ Δ₁ ++ Δ₂) (λ r →
      Σ (Sub Γ₁ Δ₁) (λ σ₁ → Σ (Sub Γ₂ Δ₂) (λ σ₂ →
        σ ≡ subst (Sub (Γ₁ ++ Γ₂)) (sym r) (σ₁ ++S σ₂))))))
is++S {[]} σ = [] , _ , refl , [] , σ , refl
is++S {A ∷ Γ₁}{Γ₂} (t ∷ σ) with is++S {_}{Γ₂} σ
is++S {A ∷ Γ₁} {Γ₂} (t ∷ _) | _ , _ , refl , σ₁ , σ₂ , refl =
  _ , _ , refl , t ∷ σ₁ , σ₂ , refl

-- -- Identity substitution
 
idS : ∀ Γ → Sub Γ Γ
idS [] = []
idS (t ∷ Γ) = uf ax ∷ idS Γ

idS++ : ∀ Γ₁ Γ₂ → idS (Γ₁ ++ Γ₂) ≡ idS Γ₁ ++S idS Γ₂
idS++ [] Γ₂ = refl
idS++ (t ∷ Γ₁) Γ₂ = cong (_∷_ (uf ax)) (idS++ Γ₁ Γ₂)

-- -- Right unit law and associativity of ++S

++Sru : ∀{Γ Δ} (σ : Sub Γ Δ) → σ ++S [] ≡ σ
++Sru [] = refl
++Sru (t ∷ σ) = cong (_∷_ t) (++Sru σ)

++Sass : ∀{Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃} (σ₁ : Sub Γ₁ Δ₁) (σ₂ : Sub Γ₂ Δ₂) (σ₃ : Sub Γ₃ Δ₃)
  → (σ₁ ++S σ₂) ++S σ₃ ≡ σ₁ ++S (σ₂ ++S σ₃)
++Sass [] σ₂ σ₃ = refl
++Sass (t ∷ σ₁) σ₂ σ₃ = cong (_∷_ t) (++Sass σ₁ σ₂ σ₃)

{-# REWRITE ++Sass #-}
{-# REWRITE ++Sru #-}

++Sis++S : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (σ₁ : Sub Γ₁ Δ₁) (σ₂ : Sub Γ₂ Δ₂)
  → is++S (σ₁ ++S σ₂) ≡ (Δ₁ , Δ₂ , refl , σ₁ , σ₂ , refl)
++Sis++S [] σ₂ = refl
++Sis++S (t ∷ σ₁) σ₂ rewrite ++Sis++S σ₁ σ₂ = refl

-- Parallel substitutions into a term

psub : ∀{S Γ Δ A} (t : S ∣ Γ ⊢ A) (σ : Sub Γ Δ) → S ∣ Δ ⊢ A
psub ax [] = ax
psub (uf t) (_∷_ {Δ₁ = Δ₁} u σ) = ssub u (psub t σ)
psub (⊸i t) σ = ⊸i (psub t (σ ++S (uf ax ∷ [])))
psub (⊸e {Γ = Γ} {Δ} t u) σ with is++S {Γ}{Δ} σ
... | _ , _ , refl , σ₁ , σ₂ , refl =
  ⊸e (psub t σ₁) (psub u σ₂)

-- Substituting with the identity psubstitution

ssub-uf : ∀{Γ Δ A' A C} (t : just A' ∣ Γ ⊢ A) (u : just A ∣ Δ ⊢ C)
  → ssub (uf t) u ≡ uf (ssub t u)
ssub-uf t u = {!!}

ssub-id : ∀{Δ A C} (u : just A ∣ Δ ⊢ C) → ssub ax u ≡ u
ssub-id t = {!!}

psub-id : ∀{S Γ A} (t : S ∣ Γ ⊢ A) → psub t (idS Γ) ≡ t
psub-id ax = refl
psub-id (uf t) =
  trans (trans (ssub-uf ax _) (cong uf (ssub-id _)))
    (cong uf (psub-id t))
psub-id {Γ = Γ} (⊸i {A = A} t) =
  cong ⊸i (trans (cong (psub t) (sym (idS++ Γ (A ∷ [])))) (psub-id t)) 
psub-id (⊸e {Γ = Γ} {Δ} t u) rewrite idS++ Γ Δ | ++Sis++S (idS Γ) (idS Δ) =
  cong₂ ⊸e (psub-id t) (psub-id u)

-- Sequential composition of substitutions

_∘S_ : ∀ {Γ Δ Λ} → Sub Δ Λ → Sub Γ Δ → Sub Γ Λ
ρ ∘S [] = ρ
ρ ∘S _∷_ {Δ₂ = Δ₂} t σ with is++S {_}{Δ₂} ρ
(_ ∘S (t ∷ σ)) | _ , _ , refl , ρ , ρ' , refl = psub t ρ ∷ (ρ' ∘S σ)

lidS : ∀ {Γ Δ} (σ : Sub Γ Δ) → idS Δ ∘S σ ≡ σ
lidS [] = refl
lidS (_∷_ {Δ₁ = Δ₁} {Δ₂} t σ) rewrite idS++ Δ₁ Δ₂ | ++Sis++S (idS Δ₁) (idS Δ₂) =
  cong₂ _∷_ (psub-id t) (lidS σ)

-- Composition preserves ++S

compS++ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Λ₁ Λ₂}
  → (σ₁ : Sub Γ₁ Δ₁) (σ₂ : Sub Γ₂ Δ₂) (ρ₁ : Sub Δ₁ Λ₁) (ρ₂ : Sub Δ₂ Λ₂) 
  → (ρ₁ ++S ρ₂) ∘S (σ₁ ++S σ₂) ≡ (ρ₁ ∘S σ₁) ++S (ρ₂ ∘S σ₂) 
compS++ [] σ₂ [] ρ₂ = refl
compS++ (_∷_ {Δ₂ = Δ₂} t σ₁) σ₂ ρ₁ ρ₂ with is++S {_}{Δ₂} ρ₁
compS++ (_∷_ {Δ₂ = Δ₂} t σ₁) σ₂ _ ρ₂ | _ , _ , refl , ρ₁ , ρ₁' , refl
  rewrite ++Sis++S ρ₁ (ρ₁' ++S ρ₂) = cong (_∷_ (psub t ρ₁)) (compS++ σ₁ σ₂ ρ₁' ρ₂)

-- Substituting with a composite psubstitution

psub-ssub : ∀{S Γ Γ' Δ Δ' A C}
  → (t : S ∣ Γ ⊢ A) (u : just A ∣ Γ' ⊢ C) (σ₁ : Sub Γ Δ) (σ₂ : Sub Γ' Δ')
  → psub (ssub t u) (σ₁ ++S σ₂) ≡ ssub (psub t σ₁) (psub u σ₂) 
psub-ssub t u σ₁ σ₂ = {!!}

psub-comp : ∀{S Γ Δ Λ}{A} (t : S ∣ Γ ⊢ A) (σ₁ : Sub Γ Δ) (σ₂ : Sub Δ Λ)
  → psub t (σ₂ ∘S σ₁) ≡ psub (psub t σ₁) σ₂
psub-comp ax [] σ₂ = refl
psub-comp (uf t) (_∷_ {Δ₁ = Δ₁} {Δ₂} u σ₁) σ₂ with is++S {Δ₁}{Δ₂} σ₂
... | (Λ₁ , Λ₂ , refl , σ₂₁ , σ₂₂ , refl) =
  trans (cong (ssub (psub u σ₂₁)) (psub-comp t σ₁ σ₂₂))
    (sym (psub-ssub u (psub t σ₁) σ₂₁ σ₂₂))
psub-comp (⊸i t) σ₁ σ₂ =
  cong ⊸i
    (trans (cong (psub t) (sym (compS++ σ₁ (uf ax ∷ []) σ₂ (uf ax ∷ []))))
           (psub-comp t (σ₁ ++S (uf ax ∷ [])) (σ₂ ++S (uf ax ∷ []))))
psub-comp (⊸e {Δ = Δ} t u) σ₁ σ₂ with is++S {_}{Δ} σ₁
psub-comp (⊸e {Δ = Δ} t u) _ σ₂ | _ , Λ , refl , σ₁ , ρ₁ , refl with is++S {_}{Λ} σ₂
psub-comp (⊸e {Δ = Δ} t u) _ _ | _ , Λ , refl , σ₁ , ρ₁ , refl | _ , _ , refl , σ₂ , ρ₂ , refl
  rewrite compS++ σ₁ ρ₁ σ₂ ρ₂ | ++Sis++S (σ₂ ∘S σ₁) (ρ₂ ∘S ρ₁) =
    cong₂ ⊸e (psub-comp t σ₁ σ₂) (psub-comp u ρ₁ ρ₂)

-- =======================================================================

-- Equational theory of terms

data _≑'_ : {S : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{t : S ∣ Γ ⊢ A} → t ≑' t
  ~_ : ∀{S}{Γ}{A}{t u : S ∣ Γ ⊢ A} → t ≑' u → u ≑' t
  _∙_ : ∀{S}{Γ}{A}{t u v : S ∣ Γ ⊢ A} → t ≑' u → u ≑' v → t ≑' v
  ⊸i : ∀{S}{Γ}{A}{B}{t u : S ∣ Γ ++ A ∷ [] ⊢ B} → t ≑' u → ⊸i t ≑' ⊸i u
  ⊸e : ∀{S}{Γ}{Δ}{A}{B}{t t' : S ∣ Γ ⊢ A ⊸ B}{u u' : nothing ∣ Δ ⊢ A}
    → t ≑' t' → u ≑' u' → ⊸e t u ≑' ⊸e t' u'
  uf : ∀{Γ}{A}{C}{t u : just A ∣ Γ ⊢ C} → t ≑' u → uf t ≑' uf u
  beta : ∀{S}{Γ}{Δ}{A}{B} {t : S ∣  Γ ++ A ∷ [] ⊢ B} {u : nothing ∣ Δ ⊢ A}
    → ⊸e (⊸i t) u ≑' psub t (idS Γ ++S u ∷ [])
  eta : ∀{S}{Γ}{A}{B} {t : S ∣ Γ ⊢ A ⊸ B} → t ≑' ⊸i (⊸e t (uf ax))
  ⊸euf : ∀{Γ}{Δ}{A}{A'}{B}{t : just A' ∣ Γ ⊢ A ⊸ B}{u : nothing ∣ Δ ⊢ A}
    → ⊸e (uf t) u ≑' uf (⊸e t u)
  ⊸iuf : ∀{Γ}{A}{A'}{B}{t : just A' ∣ Γ ++ A ∷ [] ⊢ B}
    → ⊸i (uf t) ≑' uf (⊸i t)

≡-to-≑' : ∀{S Γ A} {t u : S ∣ Γ ⊢ A} → t ≡ u → t ≑' u
≡-to-≑' refl = refl


-- =======================================================================

-- Embedding normal forms into terms

nf2nd : ∀ {S Γ C} → S ∣ Γ ⊢nf C → S ∣ Γ ⊢ C
ne2nd : ∀ {S Γ C} → S ∣ Γ ⊢ne C → just S ∣ Γ ⊢ C

nf2nd (⊸i f) = ⊸i (nf2nd f)
nf2nd (uf f) = uf (nf2nd f)
nf2nd (switch f) = ne2nd f

ne2nd ax = ax
ne2nd (⊸e f t) = ⊸e (ne2nd f) (nf2nd t)

-- =======================================================================

-- Interpretation of formulae into presehaves over stoups and contexts

⟦_⟧ : Fma → Stp → Cxt → Set
⟦ ` X ⟧ S Γ = S ∣ Γ ⊢nf ` X
⟦ A ⊸ B ⟧ S Γ = ∀ {Δ} → ⟦ A ⟧ nothing Δ → ⟦ B ⟧ S (Γ ++ Δ) 

-- =======================================================================

shift : ∀{Γ A C} → ⟦ C ⟧ (just A) Γ → ⟦ C ⟧ nothing (A ∷ Γ)
shift {C = ` X} c = uf c
shift {C = A ⊸ B} c a = shift {C = B} (c a)

-- Reflection and reification

reflect : ∀{Γ A C} → A ∣ Γ ⊢ne C → ⟦ C ⟧ (just A) Γ
reify : ∀{S Γ C} → ⟦ C ⟧ S Γ → S ∣ Γ ⊢nf C

reflect {C = ` X} n = switch n
reflect {C = A ⊸ B} n a = reflect (⊸e n (reify a))

reify {C = ` X} a = a
reify {C = A ⊸ B} a = ⊸i (reify (a (shift (reflect ax))))

-- =======================================================================

-- Interpretation of contexts (environments)

⟦_⟧C : Cxt → Cxt → Set
⟦ [] ⟧C Δ = Δ ≡ []
⟦ A ∷ Γ ⟧C Δ = ∃₂ λ Δ₁ Δ₂ → Δ ≡ Δ₁ ++ Δ₂ × ⟦ A ⟧ nothing Δ₁ × ⟦ Γ ⟧C Δ₂

⟦_∣_⟧ : Stp → Cxt → Stp → Cxt → Set
⟦ nothing ∣ Γ ⟧ T Δ = T ≡ nothing × ⟦ Γ ⟧C Δ
⟦ just A ∣ Γ ⟧ T Δ = ∃₂ λ Δ₁ Δ₂ → Δ ≡ Δ₁ ++ Δ₂ × ⟦ A ⟧ T Δ₁ × ⟦ Γ ⟧C Δ₂

infixr 5 _⟦++⟧C_

_⟦++⟧C_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → ⟦ Γ₁ ⟧C Δ₁ → ⟦ Γ₂ ⟧C Δ₂
  → ⟦ Γ₁ ++ Γ₂ ⟧C (Δ₁ ++ Δ₂)
_⟦++⟧C_ {[]} refl γ = γ
_⟦++⟧C_ {A ∷ Γ₁} (_ , _ , refl , γ₁ , γ₁') γ₂ =
  _ , _ , refl , γ₁ , γ₁' ⟦++⟧C γ₂

_⟦++⟧_ : ∀ {S T Γ₁ Γ₂ Δ₁ Δ₂} → ⟦ S ∣ Γ₁ ⟧ T Δ₁ → ⟦ Γ₂ ⟧C Δ₂
  → ⟦ S ∣ Γ₁ ++ Γ₂ ⟧ T (Δ₁ ++ Δ₂)
_⟦++⟧_ {nothing} (refl , γ₁) γ₂ = refl , γ₁ ⟦++⟧C γ₂
_⟦++⟧_ {just A} (Δ₁₁ , Δ₁₂ , refl , a , γ₁) γ₂ =
  _ , _ , refl , a , γ₁ ⟦++⟧C γ₂


-- -- The identity environment

⟦id⟧C : ∀ Γ → ⟦ Γ ⟧C Γ
⟦id⟧C [] = refl
⟦id⟧C (A ∷ Γ) = _ , _ , refl , shift (reflect ax) , ⟦id⟧C Γ

⟦id⟧ : ∀ S Γ → ⟦ S ∣ Γ ⟧ S Γ
⟦id⟧ nothing Γ = refl , ⟦id⟧C Γ
⟦id⟧ (just A) Γ = [] , Γ , refl , reflect ax , ⟦id⟧C Γ

-- -- Concatenation of environments


is⟦++⟧C : ∀ {Γ₁ Γ₂ Δ} (γ : ⟦ Γ₁ ++ Γ₂ ⟧C Δ)
  → Σ Cxt (λ Δ₁ → Σ Cxt (λ Δ₂ → Σ (Δ ≡ Δ₁ ++ Δ₂) (λ r →
      Σ (⟦ Γ₁ ⟧C Δ₁) (λ γ₁ → Σ (⟦ Γ₂ ⟧C Δ₂) (λ γ₂ →
        γ ≡ subst (⟦_⟧C (Γ₁ ++ Γ₂)) (sym r) (γ₁ ⟦++⟧C γ₂))))))
is⟦++⟧C {[]} γ = _ , _ , refl , refl , γ , refl
is⟦++⟧C {A ∷ Γ₁}{Γ₂} (_ , _ , refl , γ₁ , γ₂) with is⟦++⟧C {_}{Γ₂} γ₂
is⟦++⟧C {A ∷ Γ₁} (_ , _ , refl , γ₁ , _) | _ , _ , refl , γ₂ , γ₂' , refl =
  _ , _ , refl , (_ , _ , refl , γ₁ , γ₂) , γ₂' , refl

is⟦++⟧ : ∀ {S Γ₁ Γ₂ T Δ} (sγ : ⟦ S ∣ Γ₁ ++ Γ₂ ⟧ T Δ)
  → Σ Cxt (λ Δ₁ → Σ Cxt (λ Δ₂ → Σ (Δ ≡ Δ₁ ++ Δ₂) (λ r →
      Σ (⟦ S ∣ Γ₁ ⟧ T Δ₁) (λ sγ₁ → Σ (⟦ Γ₂ ⟧C Δ₂) (λ γ₂ →
        sγ ≡ subst (⟦ S ∣ Γ₁ ++ Γ₂ ⟧ T) (sym r) (sγ₁ ⟦++⟧ γ₂))))))
is⟦++⟧ {nothing} {Γ₁} {Γ₂} {Δ = Δ} (refl , γ) with is⟦++⟧C {Γ₁}{Γ₂}{Δ} γ
... | (Δ₁ , Δ₂ , refl , γ₁ , γ₂ , refl) =
  Δ₁ , Δ₂ , refl , (refl , γ₁) , γ₂ , refl
is⟦++⟧ {just A} {Γ₁} {Γ₂} (Δ₁ , Δ₂ , refl , a , γ) with is⟦++⟧C {Γ₁}{Γ₂}{Δ₂} γ
... | (Δ₂₁ , Δ₂₂ , refl , γ₁ , γ₂ , refl) =
  Δ₁ ++ Δ₂₁ , Δ₂₂ , refl , (_ , _ , refl , a , γ₁) , γ₂ , refl

⟦++⟧Cis⟦++⟧C : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (γ₁ : ⟦ Γ₁ ⟧C Δ₁) (γ₂ : ⟦ Γ₂ ⟧C Δ₂)
  → is⟦++⟧C (γ₁ ⟦++⟧C γ₂) ≡ (Δ₁ , Δ₂ , refl , γ₁ , γ₂ , refl)
⟦++⟧Cis⟦++⟧C {[]} refl γ₂ = refl
⟦++⟧Cis⟦++⟧C {A ∷ Γ₁} (_ , _ , refl , γ₁ , γ₁') γ₂
  rewrite ⟦++⟧Cis⟦++⟧C γ₁' γ₂ = refl  

⟦++⟧is⟦++⟧ : ∀ {S T Γ₁ Γ₂ Δ₁ Δ₂} (γ₁ : ⟦ S ∣ Γ₁ ⟧ T Δ₁) (γ₂ : ⟦ Γ₂ ⟧C Δ₂)
  → is⟦++⟧ (γ₁ ⟦++⟧ γ₂) ≡ (Δ₁ , Δ₂ , refl , γ₁ , γ₂ , refl)
⟦++⟧is⟦++⟧ {nothing} (refl , γ₁) γ₂
  rewrite ⟦++⟧Cis⟦++⟧C γ₁ γ₂ = refl
⟦++⟧is⟦++⟧ {just A} (Δ₁ , Δ₂ , refl , a , γ₁) γ₂
  rewrite ⟦++⟧Cis⟦++⟧C γ₁ γ₂ = refl

⟦id⟧C++ : ∀ Γ₁ Γ₂ → ⟦id⟧C (Γ₁ ++ Γ₂) ≡ ⟦id⟧C Γ₁ ⟦++⟧C ⟦id⟧C Γ₂
⟦id⟧C++ [] _ = refl
⟦id⟧C++ (A ∷ Γ₁) Γ₂ = cong (λ x → A ∷ [] , Γ₁ ++ Γ₂ , refl , shift _ , x) (⟦id⟧C++ Γ₁ Γ₂)

⟦id⟧++ : ∀ S Γ₁ Γ₂ → ⟦id⟧ S (Γ₁ ++ Γ₂) ≡ ⟦id⟧ S Γ₁ ⟦++⟧ ⟦id⟧C Γ₂
⟦id⟧++ nothing Γ₁ Γ₂ = cong (refl ,_) (⟦id⟧C++ Γ₁ Γ₂)
⟦id⟧++ (just A) Γ₁ Γ₂ = cong (λ x → ([] , Γ₁ ++ Γ₂ , refl , reflect ax , x)) (⟦id⟧C++ Γ₁ Γ₂)

-- -- Associativity and unit laws for ⟦++⟧C

⟦++⟧Cass : ∀ {Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃}
  → (γ₁ : ⟦ Γ₁ ⟧C Δ₁) (γ₂ : ⟦ Γ₂ ⟧C Δ₂) (γ₃ : ⟦ Γ₃ ⟧C Δ₃)
  → (γ₁ ⟦++⟧C γ₂) ⟦++⟧C γ₃ ≡ γ₁ ⟦++⟧C (γ₂ ⟦++⟧C γ₃)
⟦++⟧Cass {[]} refl γ₂ γ₃ = refl
⟦++⟧Cass {A ∷ Γ₁} {Δ₂ = Δ₂} {Δ₃} (Λ₁ , Λ₂ , refl , γ₁ , γ₁') γ₂ γ₃ =
  cong (λ x → Λ₁ , Λ₂ ++ Δ₂ ++ Δ₃ , refl , γ₁ , x) (⟦++⟧Cass γ₁' γ₂ γ₃)

⟦++⟧Cru : ∀ {Γ Δ} (γ : ⟦ Γ ⟧C Δ) → _⟦++⟧C_ {Γ}{[]} γ refl ≡ γ 
⟦++⟧Cru {[]} refl = refl
⟦++⟧Cru {A ∷ Γ} (_ , _ , refl , γ , γ') =
  cong (λ x → _ , _ , refl , γ , x) (⟦++⟧Cru γ')

{-# REWRITE ⟦++⟧Cass #-}
{-# REWRITE ⟦++⟧Cru #-}

eval : ∀{S Γ C T Δ} → S ∣ Γ ⊢ C → ⟦ S ∣ Γ ⟧ T Δ → ⟦ C ⟧ T Δ
eval ax (_ , _ , refl , c , refl) = c
eval (uf f) (refl , Δ₁ , Δ₂ , refl , a , γ) =
  eval f (Δ₁ , Δ₂ , refl , a , γ)
eval (⊸i f) sγ a = eval f (sγ ⟦++⟧ (_ , _ , refl , a , refl))
eval (⊸e {Γ = Γ} {Δ} f t) sγ with is⟦++⟧ {Γ₁ = Γ}{Δ} sγ
... | (Λ₁ , Λ₂ , refl , sγ₁ , γ₂ , refl) =
  eval f sγ₁ (eval t (refl , γ₂))

-- =======================================================================

-- The normalization function

norm : ∀{S Γ A} → S ∣ Γ ⊢ A → S ∣ Γ ⊢nf A
norm f = reify (eval f (⟦id⟧ _ _))

-- =======================================================================

⟦emb⟧ : ∀ {S Γ Δ} → ⟦ Γ ⟧C Δ → ⟦ S ∣ Γ ⟧ S Δ
⟦emb⟧ {nothing} γ = refl , γ
⟦emb⟧ {just A} γ = _ , _ , refl , reflect ax , γ

⟦emb⟧id : ∀ S Γ → ⟦emb⟧ {S} (⟦id⟧C Γ) ≡ ⟦id⟧ S Γ
⟦emb⟧id nothing Γ = refl
⟦emb⟧id (just A) Γ = refl

⟦emb⟧++ : ∀ {S Γ Δ Γ' Δ'} (γ : ⟦ Γ ⟧C Δ) (γ' : ⟦ Γ' ⟧C Δ')
  → ⟦emb⟧ {S} (γ ⟦++⟧C γ') ≡ ⟦emb⟧ γ ⟦++⟧ γ'
⟦emb⟧++ {nothing} γ γ' = refl
⟦emb⟧++ {just A} γ γ' = refl

-- Evaluation of substitutions

evalC : ∀{Γ}{Δ}{Λ} → Sub Γ Δ → ⟦ Δ ⟧C Λ → ⟦ Γ ⟧C Λ
evalC [] δ = δ
evalC (_∷_ {Δ₂ = Δ₂} t σ) δ with is⟦++⟧C {_}{Δ₂} δ
evalC (t ∷ σ) ._ | _ , _ , refl , δ₁ , δ₂ , refl =
  _ , _ , refl , eval t (refl , δ₁) , evalC σ δ₂ 

evalSC : ∀{S}{T}{Γ}{Δ}{Λ} → Sub Γ Δ → ⟦ S ∣ Δ ⟧ T Λ → ⟦ S ∣ Γ ⟧ T Λ
evalSC {nothing} σ (refl , δ) = refl , evalC σ δ
evalSC {just A} σ (Λ₁ , Λ₂ , refl , a , δ) = _ , _ , refl , a , evalC σ δ

-- Evaluating the identity substitution

evalCid : ∀ Γ {Λ} (γ : ⟦ Γ ⟧C Λ) → evalC (idS Γ) γ ≡ γ
evalCid [] γ = refl
evalCid (A ∷ Γ) (_ , _ , refl , a , γ) =
  cong (λ x → _ , _ , refl , a , x) (evalCid Γ γ)

-- Evaluation preserves ⟦++⟧C

evalC++ : ∀{Γ₁ Γ₂ Δ₁ Δ₂ Λ₁ Λ₂}
  → (σ₁ : Sub Γ₁ Δ₁) (σ₂ : Sub Γ₂ Δ₂)
  → (δ₁ : ⟦ Δ₁ ⟧C Λ₁) (δ₂ : ⟦ Δ₂ ⟧C Λ₂)
  → evalC (σ₁ ++S σ₂) (δ₁ ⟦++⟧C δ₂) ≡ evalC σ₁ δ₁ ⟦++⟧C evalC σ₂ δ₂
evalC++ [] σ₂ refl δ₂ = refl
evalC++ (_∷_ {Δ₂ = Δ₂} t σ₁) σ₂ δ₁ δ₂ with is⟦++⟧C {_}{Δ₂} δ₁
evalC++ (_∷_ {Δ₂ = Δ₂} t σ₁) σ₂ _ δ₂ | _ , _ , refl , δ , δ₁ , refl rewrite ⟦++⟧Cis⟦++⟧C δ (δ₁ ⟦++⟧C δ₂) =
  cong (λ x → _ , _ , refl , eval t (refl , δ) , x) (evalC++ σ₁ σ₂ δ₁ δ₂)

-- Evaluating a substituted term


eval-psub : ∀{S}{Γ}{Δ}{T}{Λ}{A} (t : S ∣ Γ ⊢ A) (σ : Sub Γ Δ) (δ : ⟦ S ∣ Δ ⟧ T Λ) 
  → eval (psub t σ) δ ≡ eval t (evalSC {S} σ δ) --(evalC ? ?)
eval-psub t σ δ = {!!}
{-  
eval-psub ax (t ∷ []) δ rewrite ⟦++⟧Cis⟦++⟧C δ refl = refl
eval-psub (⊸i t) σ δ =
  ifunext (λ _ → ifunext (λ _ → funext (λ { refl → funext (λ a →
    trans (eval-psub t (σ ++S (ax ∷ [])) (δ ⟦++⟧C (_ , [] , refl , a , refl)))
          (cong (eval t) (evalC++ σ (ax ∷ []) δ (_ , [] , refl , a , refl)))) })))
eval-psub (⊸e {Δ = Δ} t u) σ δ with is++S {_}{Δ} σ
eval-psub (⊸e {Δ = Δ} t u) _ δ | _ , Λ , refl , σ₁ , σ₂ , refl with is⟦++⟧C {_}{Λ} δ
eval-psub (⊸e {Δ = Δ} t u) _ _ | _ , Λ , refl , σ₁ , σ₂ , refl | _ , _ , refl , δ₁ , δ₂ , refl
  rewrite evalC++ σ₁ σ₂ δ₁ δ₂ | ⟦++⟧Cis⟦++⟧C (evalC σ₁ δ₁) (evalC σ₂ δ₂) =
  trans (cong (eval (psub t σ₁) δ₁ refl) (eval-psub u σ₂ δ₂))
        (cong (λ f → f refl (eval u (evalC σ₂ δ₂))) (eval-psub t σ₁ δ₁))
-}


-- =======================================================================

-- The evaluation function is equationally sound

eq-sound-eval : ∀{S T Γ Δ C} {t t' : S ∣ Γ ⊢ C} (sγ : ⟦ S ∣ Γ ⟧ T Δ)
  → t ≑' t' → eval t sγ ≡ eval t' sγ
eq-sound-eval sγ refl = refl
eq-sound-eval sγ (~ eq) = sym (eq-sound-eval sγ  eq)
eq-sound-eval sγ (eq ∙ eq₁) =
  trans (eq-sound-eval sγ  eq) (eq-sound-eval sγ  eq₁)
eq-sound-eval (refl , Δ₁ , Δ₂ , refl , a , γ) (uf eq) =
  eq-sound-eval (Δ₁ , Δ₂ , refl , a , γ) eq
eq-sound-eval sγ (⊸i eq) =
  ifunext (λ _ → funext (λ a →
    eq-sound-eval (sγ ⟦++⟧ (_ , [] , refl , a , refl)) eq))
eq-sound-eval sγ (⊸e {Γ = Γ} {Δ} {t = t}{t'}{u}{u'} eq eq₁)
  with is⟦++⟧ {Γ₁ = Γ}{Δ} sγ
... | (Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl) =
  trans (cong (eval t γ₁) (eq-sound-eval (refl , γ₂) eq₁))
    (cong (λ x → x (eval u' (refl , γ₂))) (eq-sound-eval γ₁ eq))
eq-sound-eval sγ (beta {Γ = Γ} {Δ}) with is⟦++⟧ {Γ₁ = Γ}{Δ} sγ
... | (Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl) = {!!}
eq-sound-eval {T = T} {Δ = Δ} sγ (eta {S}{Γ}{A}{B}) =
  ifunext (λ Λ → funext (lem refl))
  where
    lem : {t : S ∣ Γ ⊢ A ⊸ B} {γ : ⟦ S ∣ Γ ⟧ T Δ} {Δ₁ Δ₂ : Cxt}
      → (r : Δ₂ ≡ Δ ++ Δ₁) (a : ⟦ A ⟧ nothing Δ₁)
      → eval t γ a ≡ eval (⊸i (⊸e t (uf ax))) γ a
    lem {_}{γ}{Δ₁} refl a
      rewrite ⟦++⟧is⟦++⟧ {Γ₂ = A ∷ []} γ (Δ₁ , [] , refl , a , refl) = refl
eq-sound-eval (refl , Δ₁ , Δ₂ , refl , a , sγ) (⊸euf {Γ} {Δ})
  with is⟦++⟧C {Γ}{Δ} sγ
... | (Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl) = refl
eq-sound-eval (refl , Δ₁ , Δ₂ , refl , a , γ) ⊸iuf = refl

{-
eq-sound-eval {γ = γ} (beta {Γ} {Δ}) with is⟦++⟧C {Γ} {Δ} γ
eq-sound-eval (beta {Γ} {t = t} {u}) | _ , _ , refl , γ₁ , γ₂ , refl with evalC++ (idS Γ) (u ∷ []) γ₁ γ₂
... | p rewrite ⟦++⟧Cis⟦++⟧C γ₂ refl =
  sym (trans (eval-psub t (idS Γ ++S (u ∷ [])) (γ₁ ⟦++⟧C γ₂))
             (cong (eval t) (trans p (cong (λ z → z ⟦++⟧C (_ , _ , refl , eval u γ₂ , refl)) (evalCid Γ γ₁)))))

-}

-- =======================================================================

-- The normalization function is equationally sound

eq-sound-norm : ∀{S Γ A} {t t' : S ∣ Γ ⊢ A} → t ≑' t' → norm t ≡ norm t'
eq-sound-norm p = cong reify (eq-sound-eval _ p)

-- =======================================================================

shift' : ∀{S Γ A Δ} → ⟦ S ∣ Γ ⟧ (just A) Δ → ⟦ S ∣ Γ ⟧ nothing (A ∷ Δ)
shift' {just A} (Δ₁ , Δ₂ , refl , a , γ) = _ , _ , refl , shift a , γ

eval-shift : ∀{S Γ A C Δ} (t : S ∣ Γ ⊢ C) (γ : ⟦ S ∣ Γ ⟧ (just A) Δ)
  → shift (eval t γ) ≡ eval t (shift' γ)
eval-shift {just A} ax (Δ₁ , .[] , refl , a , refl) = refl
eval-shift {just A} (⊸i t) (Δ₁ , Δ₂ , refl , a , γ) =
  ifunext (λ Δ₃ → funext (λ a' → eval-shift t _))
eval-shift {just A} (⊸e {Γ = Γ} {Δ} t t₁) (Δ₁ , Δ₂ , refl , a , γ)
  with is⟦++⟧C {Γ}{Δ} γ
... | (Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl) =
  cong (λ x → x (eval t₁ (refl , γ₂))) (eval-shift t (Δ₁ , Λ₁ , refl , a , γ₁))

-- Normalizing a normal form

nf-is-norm : ∀ {S Γ A} (t : S ∣ Γ ⊢nf A) → t ≡ norm (nf2nd t)
ne-is-norm : ∀ {S Γ A} (t : S ∣ Γ ⊢ne A) → reflect t ≡ eval (ne2nd t) (⟦id⟧ (just S) Γ)

nf-is-norm (⊸i {S}{Γ} {A} n)
  rewrite sym (⟦id⟧++ S Γ (A ∷ [])) = cong ⊸i (nf-is-norm n)
nf-is-norm (uf {Γ}{A} n) =
  trans (cong uf (nf-is-norm n))
    (eval-shift (nf2nd n) ([] , Γ , refl , reflect ax , ⟦id⟧C Γ))
nf-is-norm (switch n) = ne-is-norm n

ne-is-norm ax = refl
ne-is-norm (⊸e {S}{Γ} {Δ} n m)
  rewrite ⟦id⟧C++ Γ Δ | ⟦++⟧Cis⟦++⟧C (⟦id⟧C Γ) (⟦id⟧C Δ) = 
    trans (cong (λ x → reflect (⊸e n x)) (nf-is-norm m))
      (cong (λ f → f (eval (nf2nd m) (refl , ⟦id⟧C Δ))) (ne-is-norm n))

-- =======================================================================

-- Correctness of normalization via logical relations

-- -- The logical relation R

R : ∀{S Γ A} → S ∣ Γ ⊢ A → ⟦ A ⟧ S Γ → Set
R {A = ` X} t n = t ≑' nf2nd n
R {A = A ⊸ B} t v = ∀ {Δ} {u : nothing ∣ Δ ⊢ A}{x : ⟦ A ⟧ nothing Δ}
      → R u x → R (⊸e t u) (v x)

-- The logical relation is invariant under ≗

subst-R : ∀{S Γ A} {t u : S ∣ Γ ⊢ A} {v : ⟦ A ⟧ S Γ} → t ≑' u → R u v → R t v
subst-R {A = ` X} p r = p ∙ r
subst-R {A = A ⊸ B} p r r' = subst-R (⊸e p refl) (r r')

corr-shift : ∀{Γ A C} {t : just A ∣ Γ ⊢ C} {c : ⟦ C ⟧ (just A) Γ}
  → R t c → R (uf t) (shift c)
corr-shift {C = ` X} r = uf r
corr-shift {C = A ⊸ B} r r' = subst-R ⊸euf (corr-shift (r r'))

-- Correcteness of reflection and reification

corr-reflect : ∀{Γ A C} {n : A ∣ Γ ⊢ne C}
  → R (ne2nd n) (reflect n) 
corr-reify : ∀{S Γ C} {t : S ∣ Γ ⊢ C} {v : ⟦ C ⟧ S Γ}
  → R t v → t ≑' nf2nd (reify v)

corr-reflect {C = ` X} = refl
corr-reflect {C = A ⊸ B} r =
  subst-R (⊸e refl (corr-reify r)) corr-reflect

corr-reify {C = ` X} r = r
corr-reify {C = A ⊸ B} r =
  eta ∙ (⊸i (corr-reify (r (corr-shift corr-reflect))))

-- The lifting of the logical relation to substitutions

data RC : ∀{Γ}{Δ} → Sub Γ Δ → ⟦ Γ ⟧C Δ → Set where
  [] : RC [] refl
  _∷_ : ∀{Γ}{Δ₁}{Δ₂}{A} {t : nothing ∣ Δ₁ ⊢ A} {σ : Sub Δ₂ Γ} {x : ⟦ A ⟧ nothing Δ₁} {δ : ⟦ Δ₂ ⟧C Γ}
    → R t x → RC σ δ → RC (t ∷ σ) (Δ₁ , Γ , refl , x , δ)

idR : ∀ Γ → RC (idS Γ) (⟦id⟧C Γ)
idR [] = []
idR (A ∷ Γ) = corr-shift corr-reflect ∷ idR Γ

_++R_ : ∀{Γ₁}{Γ₂}{Δ₁}{Δ₂} {σ₁ : Sub Δ₁ Γ₁} {σ₂ : Sub Δ₂ Γ₂} {δ₁ : ⟦ Δ₁ ⟧C Γ₁} {δ₂ : ⟦ Δ₂ ⟧C Γ₂}
    → RC σ₁ δ₁ → RC σ₂ δ₂ → RC (σ₁ ++S σ₂) (δ₁ ⟦++⟧C δ₂)
[] ++R rs = rs
(r ∷ rs) ++R rs' = r ∷ (rs ++R rs')

is++R : ∀{Γ₁}{Γ₂}{Δ₁}{Δ₂} (σ₁ : Sub Δ₁ Γ₁) (σ₂ : Sub Δ₂ Γ₂) (δ : ⟦ Δ₁ ++ Δ₂ ⟧C (Γ₁ ++ Γ₂)) (rs : RC (σ₁ ++S σ₂) δ)
  → Σ (⟦ Δ₁ ⟧C Γ₁) (λ δ₁ → Σ (⟦ Δ₂ ⟧C Γ₂) (λ δ₂ → Σ (δ ≡ δ₁ ⟦++⟧C δ₂) (λ r →
      Σ (RC σ₁ δ₁) (λ rs₁ → Σ (RC σ₂ δ₂) (λ rs₂ → rs ≡ subst (RC (σ₁ ++S σ₂)) (sym r) (rs₁ ++R rs₂))))))
is++R [] σ₂ δ rs = refl , δ , refl , [] , rs , refl
is++R (t ∷ σ₁) σ₂ (_ , _ , .refl , a , δ) (r ∷ rs) with is++R σ₁ σ₂ δ rs
is++R (t ∷ σ₁) σ₂ (_ , _ , .refl , a , _) (r ∷ _) | δ₁ , δ₂ , refl , rs₁ , rs₂ , refl =
  (_ , _ , refl , a , δ₁) , δ₂ , refl , r ∷ rs₁ , rs₂ , refl

-- Correcteness of evaluation


corr-eval2 : ∀{S}{Γ}{Δ}{A}{C} (t : S ∣ Γ ⊢ A) (u : just A ∣ Δ ⊢ C) (c :  ⟦ C ⟧ (just A) Δ) 
  → R u c → R (ssub t u) (eval u (Γ , Δ , refl , eval t (⟦id⟧ S Γ) , ⟦id⟧C Δ))
corr-eval2 t u c r = {!!}

corr-eval : ∀{S}{Γ}{Δ}{A} (t : S ∣ Γ ⊢ A) (σ : Sub Γ Δ) (γ : ⟦ Γ ⟧C Δ)
  → RC σ γ → R (psub t σ) (eval t (⟦emb⟧ γ)) 
corr-eval ax [] _ [] = corr-reflect
corr-eval (uf t) (u ∷ σ) (Δ₁ , Δ₂ , .refl , a , γ) (r ∷ rs) = {!!}
--   subst (R (ssub u (psub t σ)))
--     (trans (eval-psub t σ _) {!cong₂ (λ x y → eval t (Δ₁ , Δ₂ , refl , x , y)) !})
--     (corr-eval2 u (psub t σ) _ (corr-eval t σ γ rs))
corr-eval {Δ = Δ} (⊸i t) σ γ rs {_}{u} {a} r =
  subst-R
    (beta ∙ ≡-to-≑' (sym (trans (cong (psub t) (sym (trans (compS++ σ (uf ax ∷ []) (idS Δ) (u ∷ []))
                                                           (cong (λ x → x ++S ((u ∷ []) ∘S (uf ax ∷ []))) (lidS σ)))))
                                (psub-comp t _ _))))
    (subst (λ x → R (psub t (σ ++S (u ∷ []))) (eval t x)) (⟦emb⟧++ γ _)
      (corr-eval t (σ ++S (u ∷ [])) _ (rs ++R (r ∷ []))))
corr-eval (⊸e {Δ = Δ} t u) σ γ rs with is++S {_}{Δ} σ 
corr-eval (⊸e {Δ = Δ} t u) _ γ rs | _ , _ , refl , σ₁ , σ₂ , refl with is++R σ₁ σ₂ γ rs
corr-eval (⊸e {S} {Δ = Δ} t u) _ _ _ | _ , _ , refl , σ₁ , σ₂ , refl | γ₁ , γ₂ , refl , rs₁ , rs₂ , refl
  rewrite ⟦emb⟧++ {S} γ₁ γ₂ | ⟦++⟧is⟦++⟧ (⟦emb⟧ {S} γ₁) γ₂ = corr-eval t σ₁ γ₁ rs₁ (corr-eval u σ₂ γ₂ rs₂)


-- Correctness of normalization

corr-norm : ∀{S Γ A} (t : S ∣ Γ ⊢ A) → t ≑' nf2nd (norm t)
corr-norm {S}{Γ}{A} t =
  corr-reify (subst-R (≡-to-≑' (sym (psub-id t)))
    (subst (λ x → R (psub t (idS Γ)) (eval t x)) (⟦emb⟧id S Γ)
      (corr-eval t (idS Γ) (⟦id⟧C Γ) (idR Γ)))) 
