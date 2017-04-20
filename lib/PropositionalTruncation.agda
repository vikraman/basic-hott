{-# OPTIONS --without-K #-}
module PropositionalTruncation where

open import Type
open import Paths
open import OneTypes


module _ {ℓ₁} where

  private
    data #∥_∥ (X : Type ℓ₁) : Type ℓ₁ where
      #∣_∣ : X → #∥ X ∥

  ∥_∥ : Type ℓ₁ → Type ℓ₁
  ∥_∥ = #∥_∥

  {-# DISPLAY #∥_∥ = ∥_∥ #-}

  ∣_∣ : {X : Type ℓ₁} → X → ∥ X ∥
  ∣_∣ = #∣_∣

  {-# DISPLAY #∣_∣ = ∣_∣ #-}

  postulate
    identify : {X : Type ℓ₁} → (x y : ∥ X ∥) → x == y

  recTrunc : {ℓ₂ : Level} → {X : Type ℓ₁} → (Y : Type ℓ₂)
             → (X → Y) → is-prop Y → ∥ X ∥ → Y
  recTrunc Y f φ #∣ x ∣ = f x

  postulate
    recTrunc-β : {ℓ₂ : Level} → {X : Type ℓ₁} → (Y : Type ℓ₂)
                 → (f : X → Y) → (φ : is-prop Y)
                 → {x x' : ∥ X ∥} → ap (recTrunc Y f φ) (identify x x') ==
                                     φ (recTrunc Y f φ x) (recTrunc Y f φ x')

  indTrunc : {ℓ₂ : Level} → {X : Type ℓ₁} → (P : ∥ X ∥ → Type ℓ₂)
             → ((x : X) → P ∣ x ∣) → ((x : ∥ X ∥) → is-prop (P x))
             → (x : ∥ X ∥) → P x
  indTrunc P f φ #∣ x ∣ = f x
  
  indTrunc' : {ℓ₂ : Level} → {X : Type ℓ₁} → (P : ∥ X ∥ → Type ℓ₂)
              → (f : (x : X) → P ∣ x ∣)
              → (φ : (x y : ∥ X ∥) → {ux : P x} → {uy : P y} → tpt P (identify x y) ux == uy)
              → (x : ∥ X ∥) → P x
  indTrunc' P f φ #∣ x ∣ = f x
