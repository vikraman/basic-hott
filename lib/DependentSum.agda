{-# OPTIONS --without-K #-}
module DependentSum where

open import Type
open import Functions


module _ {ℓ₁ ℓ₂} where

  infixr 60 _,_
  record Σ (X : Type ℓ₁) (P : X → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
      p₁ : X
      p₂ : P p₁
  open Σ public

  infixr 80 _×_
  _×_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
  X × Y = Σ X (λ x → Y)


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  indΣ : (Q : Σ X P → Type ℓ₃) → ((x : X) → (ux : P x) → Q (x , ux))
         → (w : Σ X P) → Q w
  indΣ Q f (x , ux) = f x ux

  Σ-unv-prp : {Y : Type ℓ₃}
              → Σ (Y → X) (λ f → (y : Y) → P (f y)) → Y → Σ X P
  Σ-unv-prp (f , g) y = f y , g y


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂}
         {Q : (x : X) → P x → Type ℓ₃} where

  Σ-unv-prp' : Σ ((x : X) → P x) (λ f → (x : X) → Q x (f x))
               → (x : X) → Σ (P x) (Q x)
  Σ-unv-prp' (f , g) x = f x , g x


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ind× : (Q : X × Y → Type ℓ₃)
         → ((x : X) → (y : Y) → Q (x , y)) → (w : X × Y) → Q w
  ind× Q f (x , y) = f x y
  
  ×-unv-prp : {Z : Type ℓ₃} → (Z → X) × (Z → Y) → Z → X × Y
  ×-unv-prp (f , g) z = f z , g z


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where

  dpair→ : {X : Type ℓ₁} → {P : X → Type ℓ₂} → {X' : Type ℓ₃} → {P' : X' → Type ℓ₄}
            → Σ (X → X') (λ f → ((x : X) → P x → P' ∘ f $ x))
            → Σ X P → Σ X' P'
  dpair→ (f , f') (x , x') = f x , f' x x'

  pair→ : {X : Type ℓ₁} → {Y : Type ℓ₂} → {X' : Type ℓ₃} → {Y' : Type ℓ₄}
           → (X → X') × (Y → Y') → X × Y → X' × Y'
  pair→ (f , f') (x , x') = f x , f' x'


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂} {Y : Type ℓ₃} where

  curry : (Σ X P → Y) → ((x : X) → (ux : P x) → Y)
  curry f x ux = f (x , ux)

  -- recΣ
  uncurry : ((x : X) → (ux : P x) → Y) → (Σ X P → Y)
  uncurry f (x , ux) = f x ux
