{-# OPTIONS --without-K #-}
module Coproduct where

open import Type


infixr 80 _+_
data _+_ {ℓ₁ ℓ₂} (X : Type ℓ₁) (Y : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  i₁ : (x : X) → X + Y
  i₂ : (x : Y) → X + Y

open import Paths

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  i₁-inj : {x y : X} → i₁ {Y = Y} x == i₁ y → x == y
  i₁-inj (refl .(i₁ _)) = refl _

  i₂-inj : {x y : Y} → i₂ {X = X} x == i₂ y → x == y
  i₂-inj (refl .(i₂ _)) = refl _
