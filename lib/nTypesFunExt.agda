{-# OPTIONS --without-K #-}
module nTypesFunExt where

open import Type
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import OneTypes
open import PathsInSigma

open import FunctionExtensionality
open import OneTypesFunExt
open import IsEquivIsProp


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  eqv-prsrv-prop : is-prop Y → is-prop (X ≃ Y)
  eqv-prsrv-prop φ (f , e) (f' , e') = eqv= (funext (λ x → φ (f x) (f' x)))
  
  eqv-prsrv-contr : is-contr X → is-contr Y → is-contr (X ≃ Y)
  eqv-prsrv-contr φ ψ = e₀ , eqv-prsrv-prop (contr-is-prop ψ) e₀
    where e₀ : X ≃ Y
          e₀ = (λ x → p₁ ψ) , (λ y → p₁ φ) , p₂ φ , p₂ ψ ,
               (λ x → contr-is-set ψ _ _ _ _)

  eqv-prsrv-set : is-set Y → is-set (X ≃ Y)
  eqv-prsrv-set φ (f , e) (f' , e') p q =
    ! (dpair=-η p)
    ◾ ap dpair= (dpair= (! (funext-η (ap p₁ p))
                         ◾ ap funext (funext (λ x → φ _ _ _ _))
                         ◾ funext-η (ap p₁ q) ,
                         prop-is-set (is-equiv-is-prop f') _ _ _ _))
    ◾ (dpair=-η q)
