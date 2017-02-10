{-# OPTIONS --without-K #-}
module theorems.IsnTypeIsProp where

open import IntensionalTypeTheory
open import FunctionExtensionality


module _ {ℓ : Level} where

  is-contr-is-prop : (X : Type ℓ) → is-prop (is-contr X)
  is-contr-is-prop X (x , φ) (y , ψ) =
    dpair= (φ y , funext (λ z → contr-is-set (x , φ) _ _ _ _))
  
  is-prop-is-prop : (X : Type ℓ) → is-prop (is-prop X)
  is-prop-is-prop X φ ψ = funext (λ x →
                          funext (λ y →
                          prop-is-set φ _ _ _ _))

  is-prop-is-set : (X : Type ℓ) → is-prop (is-set X)
  is-prop-is-set X φ ψ = funext (λ x →
                         funext (λ y →
                         funext (λ p →
                         funext (λ q →
                         set-is-1type φ _ _ _ _ _ _))))



