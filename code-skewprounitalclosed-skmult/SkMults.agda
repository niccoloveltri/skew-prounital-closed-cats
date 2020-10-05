{-# OPTIONS --rewriting #-}

module SkMults where

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Utilities

infix 15 _∣_⊢b_

postulate
  At : Set
  _∣_⊢b_ : Maybe At → List At → At → Set
  ax-b : ∀ {X} → just X ∣ [] ⊢b X
  scut-b : ∀ {T Γ Δ X Y}
    → T ∣ Γ ⊢b X → just X ∣ Δ ⊢b Y → T ∣ Γ ++ Δ ⊢b Y
  ccut-b : ∀ {T Γ} Δ₀ {Δ₁ X Y}
    → nothing ∣ Γ ⊢b X → T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y
    → T ∣ Δ₀ ++ Γ ++ Δ₁ ⊢b Y
  uf-b : ∀ {Γ X Y}
    → just X ∣ Γ ⊢b Y → nothing ∣ X ∷ Γ ⊢b Y

  scut-ax-b : ∀ {T Γ Y} (f : T ∣ Γ ⊢b Y)
    → scut-b f ax-b ≡ f
  scut-ax-b2 : ∀ {Γ X Y} (f : just X ∣ Γ ⊢b Y)
    → scut-b ax-b f ≡ f
  ccut-ax-b : ∀ {T} Δ₀ {Δ₁ X Y} (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
    → ccut-b Δ₀ (uf-b ax-b) g ≡ g

  scut-scut-ass-b : ∀ {T Γ Δ Λ X Y Z}
    → (f : T ∣ Γ ⊢b X) (g : just X ∣ Δ ⊢b Y) (h : just Y ∣ Λ ⊢b Z)
    → scut-b (scut-b f g) h ≡ scut-b f (scut-b g h)
  ccut-scut-ass-b : ∀ {T Γ} Δ₀ {Δ₁ Λ X Y Z}
    → (f : nothing ∣ Γ ⊢b X) (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
    → (h : just Y ∣ Λ ⊢b Z)
    → ccut-b Δ₀ f (scut-b g h) ≡ scut-b (ccut-b Δ₀ f g) h    
  ccut-ccut-ass-b : ∀ {T Γ} Γ₀ Δ₀ {Δ₁ Γ₁ X Y Z}
    → (f : nothing ∣ Γ ⊢b X) (g : nothing ∣ Γ₀ ++ X ∷ Γ₁ ⊢b Y)
    → (h : T ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
    → ccut-b (Δ₀ ++ Γ₀) f (ccut-b Δ₀ g h) ≡ ccut-b Δ₀ (ccut-b Γ₀ f g) h

  scut-ccut-par-b : ∀ {T Γ₁ Γ₂} Δ₀ {Δ₁ X Y Z}
    → (f₁ : T ∣ Γ₁ ⊢b X) (f₂ : nothing ∣ Γ₂ ⊢b Y)
    → (g : just X ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
    → scut-b f₁ (ccut-b Δ₀ f₂ g) ≡ ccut-b (Γ₁ ++ Δ₀) f₂ (scut-b f₁ g)
  ccut-ccut-par-b : ∀ {T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ X Y Z}
    → (f₁ : nothing ∣ Γ₁ ⊢b X) (f₂ : nothing ∣ Γ₂ ⊢b Y)
    → (g : T ∣ Δ₀ ++ X ∷ Δ₁ ++ Y ∷ Δ₂ ⊢b Z)
    → ccut-b Δ₀ f₁ (ccut-b (Δ₀ ++ X ∷ Δ₁) f₂ g)
           ≡ ccut-b (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut-b Δ₀ f₁ g)

  scut-uf-b : ∀ {Γ Δ X Y Z}
    → (f : just X ∣ Γ ⊢b Y) (g : just Y ∣ Δ ⊢b Z)
    → scut-b (uf-b f) g ≡ uf-b (scut-b f g)
  ccut-uf-b : ∀ {Γ} Δ₀ {Δ₁ X Y Z}
    → (f : nothing ∣ Γ ⊢b Y) (g : just X ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
    → ccut-b (X ∷ Δ₀) f (uf-b g) ≡ uf-b (ccut-b Δ₀ f g)
  ccut-uf-b2 : ∀ {Γ Δ X Y}
    → (f : nothing ∣ Γ ⊢b X) (g : just X ∣ Δ ⊢b Y)
    → ccut-b [] f (uf-b g) ≡ scut-b f g

ccut-b-gen : ∀ {S T Γ} Δ₀ {Δ₁ X Y}
  → S ∣ Γ ⊢b X → T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y
  →  T ∣ Δ₀ ++ asCxt S Γ ++ Δ₁ ⊢b Y
ccut-b-gen {nothing} Δ₀ f g = ccut-b Δ₀ f g
ccut-b-gen {just X'} Δ₀ f g = ccut-b Δ₀ (uf-b f) g

cut-gen-uf-b : ∀ {S Γ} Δ₀ {Δ₁ X Y Z}
    → (f : S ∣ Γ ⊢b Y) (g : just X ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
    → ccut-b-gen (X ∷ Δ₀) f (uf-b g) ≡ uf-b (ccut-b-gen Δ₀ f g)
cut-gen-uf-b {nothing} Δ₀ f g = ccut-uf-b Δ₀ f g
cut-gen-uf-b {just x} Δ₀ f g = ccut-uf-b Δ₀ (uf-b f) g

{-
record SkMult : Set₁ where
  field
    At : Set
    _∣_⊢b_ : Maybe At → List At → At → Set

  infix 15 _∣_⊢b_

  field
    ax-b : ∀ {X} → just X ∣ [] ⊢b X
    scut-b : ∀ {T Γ Δ X Y}
      → T ∣ Γ ⊢b X → just X ∣ Δ ⊢b Y → T ∣ Γ ++ Δ ⊢b Y
    ccut-b : ∀ {T Γ} Δ₀ {Δ₁ X Y}
      → nothing ∣ Γ ⊢b X → T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y
      → T ∣ Δ₀ ++ Γ ++ Δ₁ ⊢b Y
    uf-b : ∀ {Γ X Y}
      → just X ∣ Γ ⊢b Y → nothing ∣ X ∷ Γ ⊢b Y

    scut-ax-b : ∀ {T Γ Y} (f : T ∣ Γ ⊢b Y)
      → scut-b f ax-b ≡ f
    scut-ax-b2 : ∀ {Γ X Y} (f : just X ∣ Γ ⊢b Y)
      → scut-b ax-b f ≡ f
    ccut-ax-b : ∀ {T} Δ₀ {Δ₁ X Y} (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
      → ccut-b Δ₀ (uf-b ax-b) g ≡ g

    scut-scut-ass-b : ∀ {T Γ Δ Λ X Y Z}
      → (f : T ∣ Γ ⊢b X) (g : just X ∣ Δ ⊢b Y) (h : just Y ∣ Λ ⊢b Z)
      → scut-b (scut-b f g) h ≡ scut-b f (scut-b g h)
    ccut-scut-ass-b : ∀ {T Γ} Δ₀ {Δ₁ Λ X Y Z}
      → (f : nothing ∣ Γ ⊢b X) (g : T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y)
      → (h : just Y ∣ Λ ⊢b Z)
      → ccut-b Δ₀ f (scut-b g h) ≡ scut-b (ccut-b Δ₀ f g) h    
    ccut-ccut-ass-b : ∀ {T Γ} Γ₀ Δ₀ {Δ₁ Γ₁ X Y Z}
      → (f : nothing ∣ Γ ⊢b X) (g : nothing ∣ Γ₀ ++ X ∷ Γ₁ ⊢b Y)
      → (h : T ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
      → ccut-b (Δ₀ ++ Γ₀) f (ccut-b Δ₀ g h) ≡ ccut-b Δ₀ (ccut-b Γ₀ f g) h

    scut-ccut-par-b : ∀ {T Γ₁ Γ₂} Δ₀ {Δ₁ X Y Z}
      → (f₁ : T ∣ Γ₁ ⊢b X) (f₂ : nothing ∣ Γ₂ ⊢b Y)
      → (g : just X ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
      → scut-b f₁ (ccut-b Δ₀ f₂ g) ≡ ccut-b (Γ₁ ++ Δ₀) f₂ (scut-b f₁ g)
    ccut-ccut-par-b : ∀ {T Γ₁ Γ₂} Δ₀ {Δ₁ Δ₂ X Y Z}
      → (f₁ : nothing ∣ Γ₁ ⊢b X) (f₂ : nothing ∣ Γ₂ ⊢b Y)
      → (g : T ∣ Δ₀ ++ X ∷ Δ₁ ++ Y ∷ Δ₂ ⊢b Z)
      → ccut-b Δ₀ f₁ (ccut-b (Δ₀ ++ X ∷ Δ₁) f₂ g)
             ≡ ccut-b (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut-b Δ₀ f₁ g)

    scut-uf-b : ∀ {Γ Δ X Y Z}
      → (f : just X ∣ Γ ⊢b Y) (g : just Y ∣ Δ ⊢b Z)
      → scut-b (uf-b f) g ≡ uf-b (scut-b f g)
    ccut-uf-b : ∀ {Γ} Δ₀ {Δ₁ X Y Z}
      → (f : nothing ∣ Γ ⊢b Y) (g : just X ∣ Δ₀ ++ Y ∷ Δ₁ ⊢b Z)
      → ccut-b (X ∷ Δ₀) f (uf-b g) ≡ uf-b (ccut-b Δ₀ f g)
    ccut-uf-b2 : ∀ {Γ Δ X Y}
      → (f : nothing ∣ Γ ⊢b X) (g : just X ∣ Δ ⊢b Y)
      → ccut-b [] f (uf-b g) ≡ scut-b f g

  ccut-b-gen : ∀ {S T Γ} Δ₀ {Δ₁ X Y}
    → S ∣ Γ ⊢b X → T ∣ Δ₀ ++ X ∷ Δ₁ ⊢b Y
    →  T ∣ Δ₀ ++ asCxt S Γ ++ Δ₁ ⊢b Y
  ccut-b-gen {nothing} Δ₀ f g = ccut-b Δ₀ f g
  ccut-b-gen {just X'} Δ₀ f g = ccut-b Δ₀ (uf-b f) g
-}
