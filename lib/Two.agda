{-# OPTIONS --without-K #-}
module Two where

open import Type


data 𝟚 : Type₀ where
  0₂ : 𝟚
  1₂ : 𝟚


module _ {ℓ : Level} where

  rec𝟚 : (X : Type ℓ) → X → X → 𝟚 → X
  rec𝟚 X x y 0₂ = x
  rec𝟚 X x y 1₂ = y

  ind𝟚 : (P : 𝟚 → Type ℓ) → P 0₂ → P 1₂ → (x : 𝟚) → P x
  ind𝟚 P x y 0₂ = x
  ind𝟚 P x y 1₂ = y


not : 𝟚 → 𝟚
not 0₂ = 1₂
not 1₂ = 0₂
