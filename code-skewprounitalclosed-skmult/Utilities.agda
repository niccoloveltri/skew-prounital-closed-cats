{-# OPTIONS --rewriting #-}

module Utilities where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum 
open import Data.List hiding (map)
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public


-- uniqueness of identity proofs

uip : {A : Set} → {a a' : A} → {p p' : a ≡ a'} → p ≡ p' 
uip {_} {.a} {a} {refl} {refl} = refl

-- Some lemmata about lists for reasoning about contexts

++ru : {X : Set} → (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)

{-# REWRITE ++ass #-}
{-# REWRITE ++ru #-}

-- We used Agda rewriting feature to turn the propositional equalities
-- ++ass and ++ru into judgemental equalities. This is not necessary,
-- but it makes much easier expressing and proving e.g. the
-- generalized multicategory laws in MulticatLaws.agda.

inj∷ : {X : Set} → {x y : X} → {xs ys : List X} → 
           x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
inj∷ refl = refl , refl

[]disj∷ : {X : Set} → (xs : List X) → {ys : List X} → {x : X} →  
             [] ≡ xs ++ x ∷ ys → ⊥
[]disj∷ [] ()
[]disj∷ (x ∷ xs) ()

cases∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
cases∷ [] refl = inj₁ (refl , refl , refl)
cases∷ (x₀ ∷ xs) {ys} {.(xs ++ x ∷ ys)} {x} {.x₀} refl = inj₂ (xs , refl , refl)

cases++ : {X : Set} → (xs xs' ys ys' : List X) → {x : X} → 
   xs' ++ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ ys')  
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ xs₀) 
cases++ xs [] _ _ refl = inj₂ (xs , refl , refl)
cases++ [] (x' ∷ xs') _ _ refl = inj₁ (xs' , refl , refl)
cases++ (x₀ ∷ xs) (x' ∷ xs') ys ys' {x} p with inj∷ p
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q with cases++ xs xs' ys ys' q 
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₁ (xs₀ , r , r') = inj₁ (xs₀ , cong₂ _∷_ refl r , r')
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₂ (xs₀ , r , r') = inj₂ (xs₀ , r , cong₂ _∷_ refl r')

canc⊥ : {A : Set}{x : A}(xs ys : List A)
  → ys ≡ x ∷ xs ++ ys → ⊥
canc⊥ _ [] ()
canc⊥ [] (y ∷ ys) ()
canc⊥ (x ∷ xs) (y ∷ ys) p with inj∷ p
... | (refl , q) = canc⊥ (xs ++ y ∷ []) ys q

canc⊥2 : {A : Set}{x : A}(xs : List A){ys : List A}
  → xs ≡ xs ++ x ∷ ys → ⊥
canc⊥2 [] ()
canc⊥2 (x ∷ xs) p = canc⊥2 xs (proj₂ (inj∷ p))

canc⊥3 : {A : Set}{x : A}(xs ys zs : List A)
  → ys ≡ zs ++ x ∷ xs ++ ys → ⊥
canc⊥3 xs ys [] p = canc⊥ xs ys p
canc⊥3 {_} {x} xs ys (z ∷ zs) p = canc⊥ (zs ++ x ∷ xs) ys p

canc⊥4 : {A : Set}{x : A}(xs : List A){ys zs : List A}
  → xs ≡ (xs ++ zs) ++ x ∷ ys → ⊥
canc⊥4 [] {_}{zs} p = []disj∷ zs p
canc⊥4 (x ∷ xs) {zs = zs} p = canc⊥4 xs {zs = zs} (proj₂ (inj∷ p))

canc++ : {A : Set}(xs xs' : List A){ys : List A} → xs ++ ys ≡ xs' ++ ys → xs ≡ xs'
canc++ [] [] p = refl
canc++ [] (x ∷ xs') {ys} p = ⊥-elim (canc⊥ xs' ys p)
canc++ (x ∷ xs) [] {ys} p = ⊥-elim (canc⊥ xs ys (sym p))
canc++ (x ∷ xs) (x₁ ∷ xs') p with inj∷ p
canc++ (x ∷ xs) (.x ∷ xs'){ys} p | refl , q = cong (_∷_ x) (canc++ xs xs' {ys} q)

++canc : {A : Set}{xs xs' : List A}(ys : List A) → ys ++ xs ≡ ys ++ xs' → xs ≡ xs'
++canc [] p = p
++canc (x ∷ ys) p = ++canc ys (proj₂ (inj∷ p))

-- =======================================================================

-- Function extensionality

postulate
  funext : {A : Set}{B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x) → f ≡ g
  ifunext : {A : Set}{B : A → Set} {f g : {x : A} → B x}
    → (∀ x → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

cases++-inj₁ : {X : Set} → (xs ys zs : List X) → (x : X) →
  cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl ≡ inj₁ (ys , refl , refl)
cases++-inj₁ xs ys zs x with cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl
cases++-inj₁ xs ys zs x | inj₁ (xs' , p , q) with canc++ ys xs' {zs} q
cases++-inj₁ xs ys zs x | inj₁ (.ys , refl , refl) | refl = refl
cases++-inj₁ xs ys zs x | inj₂ (ys' , p , q) = ⊥-elim (canc⊥3 ys zs ys' p)

cases++-inj₂ : {X : Set} → (xs xs' ys : List X) → (x : X) → 
   cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl ≡ inj₂ (xs , refl , refl)
cases++-inj₂ xs xs' ys x with cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl
cases++-inj₂ xs xs' ys x | inj₁ (xs₀ , p , q) = ⊥-elim (canc⊥3 [] ys (xs₀ ++ xs) q)
cases++-inj₂ xs xs' ys x | inj₂ (xs₀ , p , q) with ++canc {xs = xs}{xs₀} xs' q
cases++-inj₂ xs xs' ys x | inj₂ (.xs , refl , refl) | refl = refl

asCxt : {A : Set} → Maybe A → List A → List A
asCxt (just A) Γ = A ∷ Γ
asCxt nothing Γ = Γ

asCxt++ : ∀{A}(S : Maybe A) (Γ Δ : List A)
  → asCxt S (Γ ++ Δ) ≡ asCxt S Γ ++ Δ
asCxt++ nothing Γ Δ = refl
asCxt++ (just _) Γ Δ = refl

{-# REWRITE asCxt++ #-}

lmap : {A B : Set} (f : A → B)
  → (xs : List A) → List B
lmap f [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

asCxtmap : ∀{A B} (f : A → B) (S : Maybe A) (Γ : List A)
  → asCxt (mmap f S) (lmap f Γ) ≡ lmap f (asCxt S Γ)
asCxtmap f nothing Γ = refl
asCxtmap f (just x) Γ = refl

{-# REWRITE asCxtmap #-}


lmap++ : {A B : Set} (f : A → B) (xs : List A) (ys : List A)
  → lmap f (xs ++ ys) ≡ lmap f xs ++ lmap f ys
lmap++ f [] ys = refl
lmap++ f (x ∷ xs) ys = cong (_ ∷_) (lmap++ f xs ys)

{-# REWRITE lmap++ #-}

cases++-lmap : {X Y : Set} (f : X → Y)
  → (xs : List Y) (ys : List Y) (zs : List X)
  → xs ++ ys ≡ lmap f zs
  →  Σ (List X) λ xs' → Σ (List X) λ ys' →
    xs ≡ lmap f xs' × ys ≡ lmap f ys' × zs ≡ xs' ++ ys'
cases++-lmap f [] ys zs refl = [] , _ , refl , refl , refl
cases++-lmap f (x ∷ xs) ys (z ∷ zs) eq with inj∷ eq
cases++-lmap f (x ∷ xs) ys (z ∷ zs) eq | refl , eq' with cases++-lmap f xs ys zs eq'
... | (xs' , ys' , p , q , r) =
  z ∷ xs' , ys' , cong (_ ∷_) p , q , cong (_ ∷_) r


cases++-lmap-help : {X Y : Set} (f : X → Y)
  → (xs ys xs' ys' : List X)
  → xs ++ ys ≡ xs' ++ ys' → lmap f xs ≡ lmap f xs'
  → xs ≡ xs'
cases++-lmap-help f [] ys [] ys' eq eq2 = refl
cases++-lmap-help f (x ∷ xs) ys (x' ∷ xs') ys' eq eq2 =
  cong₂ _∷_ (inj∷ eq .proj₁) (cases++-lmap-help f xs ys xs' ys' (inj∷ eq .proj₂) (inj∷ eq2 .proj₂))  

cases++-lmap-refl : {X Y : Set} (f : X → Y)
  → (xs ys : List X)
  → cases++-lmap f (lmap f xs) (lmap f ys) (xs ++ ys) refl ≡ (xs , ys , refl , refl , refl) 
cases++-lmap-refl f  [] ys = refl
cases++-lmap-refl f (x ∷ xs) ys with cases++-lmap f (lmap f xs) (lmap f ys) (xs ++ ys) refl
cases++-lmap-refl f (x ∷ xs) ys | (xs' , ys' , p , q , r) with cases++-lmap-help f xs ys xs' ys' r p
cases++-lmap-refl f (x ∷ xs) ys | .xs , ys' , p , q , r | refl with ++canc {xs = ys}{ys'} xs r
cases++-lmap-refl f (x ∷ xs) ys | .xs , .ys , refl , refl , refl | refl | refl = refl

{-
cases++-lmap-refl' : {X Y : Set} (f : X → Y)
  → (xs ys : List X) (p : lmap f xs ++ lmap f ys ≡ lmap f (xs ++ ys))
  → cases++-lmap (lmap f xs) (lmap f ys) (xs ++ ys) p ≡ (xs , ys , refl , refl , refl) 
cases++-lmap-refl' f [] ys refl = refl
cases++-lmap-refl' f (x ∷ xs) ys p with inj∷ p
cases++-lmap-refl' f (x ∷ xs) ys p | refl , eq with cases++-lmap (lmap f xs) (lmap f ys) (xs ++ ys) eq
cases++-lmap-refl' f (x ∷ xs) ys p | refl , eq | (xs' , ys' , p' , q , r) with cases++-lmap-help xs ys xs' ys' r p'
cases++-lmap-refl' f (x ∷ xs) ys p | refl , eq | .xs , ys' , p' , q , r | refl with ++canc {xs = ys}{ys'} xs r
cases++-lmap-refl' f (x ∷ xs) ys p | refl , eq | .xs , .ys , refl , refl , refl | refl | refl = refl
-}


-- lmap++-refl : {A B : Set} (f : A → B) (xs ys : List A)
--   → lmap++ f xs ys ≡ refl
-- lmap++-refl f [] ys = refl
-- lmap++-refl f (x ∷ xs) ys rewrite lmap++-refl f xs ys = refl


