{-# OPTIONS --without-K #-}

module _ where

open import Type public
open import Function public
open import Paths public


module _ {ℓ ℓ' : Level} where

  -- infixr 60 _,_
  -- record Σ (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  --   constructor _,_
  --   field
  --     p₁ : A
  --     p₂ : B p₁
  -- open Σ public

  -- infixr 80 _×_
  -- _×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
  -- A × B = Σ A (λ x → B)

  infixr 60 _,_
  data Σ (X : Type ℓ) (P : X → Type ℓ') : Type (ℓ ⊔ ℓ') where
    _,_ : (x : X) → (ux : P x) → Σ X P

  infixr 80 _×_
  _×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
  A × B = Σ A (λ x → B)

  p₁ : {X : Type ℓ} → {P : X → Type ℓ'} → Σ X P → X
  p₁ (x , ux) = x

  p₂ : {X : Type ℓ} → {P : X → Type ℓ'} → (w : Σ X P) → P (p₁ w)
  p₂ (x , ux) = ux


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} where

  indΣ : {X : Type ℓ₁} → {P : X → Type ℓ₂} → (Q : Σ X P → Type ℓ₃)
         → ((x : X) → (ux : P x) → Q (x , ux)) → (w : Σ X P) → Q w
  indΣ Q f (x , ux) = f x ux

  ind× : {X : Type ℓ₁} → {Y : Type ℓ₂} → (Q : X × Y → Type ℓ₃)
         → ((x : X) → (y : Y) → Q (x , y)) → (w : X × Y) → Q w
  ind× Q f (x , y) = f x y
  
  Σ-unv-prp : {X : Type ℓ₁} → {P : X → Type ℓ₂} → {Y : Type ℓ₃}
               → Σ (Y → X) (λ f → (y : Y) → P ∘ f $ y) → Y → Σ X P
  Σ-unv-prp (f , g) y = f y , g y

  ×-unv-prp : {X : Type ℓ₁} → {Y : Type ℓ₂} → {Z : Type ℓ₃}
               → (Z → X) × (Z → Y) → Z → X × Y
  ×-unv-prp (f , g) z = f z , g z


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where

  dpair→ : {X : Type ℓ₁} → {P : X → Type ℓ₂} → {X' : Type ℓ₃} → {P' : X' → Type ℓ₄}
            → Σ (X → X') (λ f → (w : Σ X P) → P' ∘ f $ p₁ w)
            → Σ X P → Σ X' P'
  dpair→ (f , f') (x , x') = f x , f' (x , x')

  pair→ : {X : Type ℓ₁} → {Y : Type ℓ₂} → {X' : Type ℓ₃} → {Y' : Type ℓ₄}
           → (X → X') × (Y → Y') → X × Y → X' × Y'
  pair→ (f , f') (x , x') = f x , f' x'


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} {Y : Type ℓ₃} where

  curry : (Σ X P → Y) → ((x : X) → (ux : P x) → Y)
  curry f x ux = f (x , ux)

  -- recΣ
  uncurry : ((x : X) → (ux : P x) → Y) → (Σ X P → Y)
  uncurry f (x , ux) = f x ux
