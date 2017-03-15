{-# OPTIONS --without-K #-}
module FunctionExtensionality where

open import IntensionalTypeTheory


postulate
  happly-is-equiv : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {P : X → Type ℓ₂}
                    → (f g : (x : X) → P x) → is-equiv (happly {f = f} {g})

module _ {ℓ ℓ₂ : Level} {X : Type ℓ} {P : X → Type ℓ₂} {f g : (x : X) → P x} where

  funext : f ∼ g → f == g 
  funext = p₁ (happly-is-equiv f g)

  funext-β : happly ∘ funext ∼ id
  funext-β = p₁ (p₂ (p₂ (happly-is-equiv f g)))

  funext-η : funext ∘ happly ∼ id
  funext-η = p₁ (p₂ (happly-is-equiv f g))


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  ind∼ : (Q : {f g : (x : X) → P x} → (φ : f ∼ g) → Type ℓ₃)
         → ((f : (x : X) → P x) → Q (idh f))
         → {f g : (x : X) → P x} → (φ : f ∼ g) → Q φ
  ind∼ Q f = (λ {φ} → tpt Q (funext-β φ)) ∘ ind= (Q ∘ happly) f ∘ funext


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  funext-idh : (f : (x : X) → P x) → funext (idh f) == refl f
  funext-idh f = funext-η (refl f)
