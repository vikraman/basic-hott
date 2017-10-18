{-# OPTIONS --without-K #-}
module Coproduct where

open import Type


infixr 80 _+_
data _+_ {ℓ₁ ℓ₂} (X : Type ℓ₁) (Y : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  i₁ : (x : X) → X + Y
  i₂ : (x : Y) → X + Y

open import Paths
open import Equivalences
open import DependentSum

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  i₁-is-embed : is-embed {Y = X + Y} i₁
  i₁-is-embed x y = qinv-is-equiv (g , η , ε)
    where g : i₁ x == i₁ y → x == y
          g (refl .(i₁ x)) = refl x
          η : (p : x == y) → g (ap i₁ p) == p
          η (refl x) = refl (refl x)
          ε : (p : i₁ x == i₁ y) → ap i₁ (g p) == p
          ε (refl .(i₁ x)) = refl (refl (i₁ x))

  i₂-is-embed : is-embed {Y = X + Y} i₂
  i₂-is-embed x y = qinv-is-equiv (g , η , ε)
    where g : i₂ x == i₂ y → x == y
          g (refl .(i₂ x)) = refl x
          η : (p : x == y) → g (ap i₂ p) == p
          η (refl x) = refl (refl x)
          ε : (p : i₂ x == i₂ y) → ap i₂ (g p) == p
          ε (refl .(i₂ x)) = refl (refl (i₂ x))
