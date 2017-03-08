{-# OPTIONS --without-K #-}
module IsEquivIsProp where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import PathsInSigma
open import OneTypes
open import FunctionExtensionality
open import nTypeClosureProperties
open import IsnTypeIsProp


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-contr' : (f : X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-contr' f = (y : Y) → is-contr (fib f y)

  is-contr'-is-prop : (f : X → Y) → is-prop (is-contr' f)
  is-contr'-is-prop f φ ψ = contr-is-prop (Π-prsrv-contr (λ y → φ y , is-contr-is-prop _ _)) φ ψ


  lem-4-2-5 : (h : X → Y) → (y : Y) → (v w : fib h y)
              → (v == w) ≃ Σ (p₁ v == p₁ w) (λ q → p₂ w == ! (ap h q) ◾ p₂ v)
  lem-4-2-5 h y (x , p) (x' , p') = {!!}



  is-equiv-is-prop : (f : X → Y) → is-prop (is-equiv f)
  is-equiv-is-prop f (g , η , ε , τ) (g' , η' , ε' , τ') = dpair= (funext α , {!!})
    where α : g ∼ g'
          α y = ! (η (g y)) ◾ ap g (ε y ◾ ! (ε' y)) ◾ η (g' y)
