{-# OPTIONS --without-K #-}
module Homotopies where

open import Type
open import Functions
open import DependentSum
open import Paths


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  infixr 30 _∼_
  _∼_ : ((x : X) → P x) → ((x : X) → P x) → Type (ℓ₁ ⊔ ℓ₂)
  _∼_ f g = (x : X) → f x == g x

  idh : (f : (x : X) → P x) → f ∼ f
  idh f x = refl (f x)

  !h : {f g : (x : X) → P x} → f ∼ g → g ∼ f
  !h φ x = ! (φ x)

  infixr 80 _◽_
  _◽_ : {f g h : (x : X) → P x} → f ∼ g → g ∼ h → f ∼ h
  _◽_ σ τ x = σ x ◾ τ x 


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  nat : {f g : X → Y} → (φ : f ∼ g)
        → {x y : X} → (p : x == y) → φ x ◾ ap g p == ap f p ◾ φ y
  nat φ (refl x) = ◾unitr (φ x) ◾ ! (◾unitl (φ x))


module _ {ℓ : Level} {X : Type ℓ} where

  nat-id : {f : X → X} → (φ : f ∼ id)
           → {x y : X} → (p : x == y) → φ x ◾ p == ap f p ◾ φ y
  nat-id φ {x} p = ap (φ x ◾-) (! (ap-id _)) ◾ nat φ p

  htpy-id-comm : (f : X → X) → (φ : f ∼ id) → φ ∘ f ∼ ap f ∘ φ
  htpy-id-comm f φ x =
    l₁=r₁◾r₂◾!l₂ (nat-id φ (φ x))
    ◾ ap (_ ◾-) (◾invr _)
    ◾ ◾unitr _


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  happly : {f g : (x : X) → P x} → f == g → f ∼ g
  happly (refl f) = idh f
