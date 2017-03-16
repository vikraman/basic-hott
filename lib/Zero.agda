{-# OPTIONS --without-K #-}
module Zero where

open import Type
open import Paths


data 𝟘 : Type₀ where

module _ {ℓ : Level} where

  rec𝟘 : (X : Type ℓ) → 𝟘 → X
  rec𝟘 X ()

  ind𝟘 : (P : 𝟘 → Type ℓ) → (x : 𝟘) → P x
  ind𝟘 P ()


infix 100 ¬
¬ : {ℓ : Level} → Type ℓ → Type ℓ
¬ X = X → 𝟘


module _ {ℓ : Level} {X : Type ℓ} where

  infixr 30 ≠
  ≠ : Type ℓ
  ≠ = {x y : X} → x == y → 𝟘


data 𝟘' {ℓ : Level} : Type ℓ where
