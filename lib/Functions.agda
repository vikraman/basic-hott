{-# OPTIONS --without-K #-}
module Functions where

open import Type


module _ {ℓ₁ ℓ₂} where

  Π : (X : Type ℓ₁) → (P : X → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
  Π X P = (x : X) → P x

  infixr 80 _∘_
  _∘_ : {X : Type ℓ₁} → {P : X → Type ℓ₂}
        → {ℓ₃ : Level} → {Q : {x : X} → P x → Type ℓ₃}
        → ({x : X} → (y : P x) → Q y) → (f : (x : X) → P x)
        → (x : X) → Q (f x)
  g ∘ f = λ x → g (f x)

  infixr 0 _$_
  _$_ : {X : Type ℓ₁} → {P : X → Type ℓ₂}
        → ((x : X) → P x) → (x : X) → P x
  f $ x = f x


id : {ℓ : Level} → {X : Type ℓ} → X → X
id = λ x → x
