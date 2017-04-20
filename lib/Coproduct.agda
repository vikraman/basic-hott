{-# OPTIONS --without-K #-}
module Coproduct where

open import Type


infixr 80 _+_
data _+_ {ℓ₁ ℓ₂} (X : Type ℓ₁) (Y : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  i₁ : (x : X) → X + Y
  i₂ : (x : Y) → X + Y

