{-# OPTIONS --without-K #-}
module Surjections where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import ContractibleFunctions
open import OneTypes
open import nTypes
open import PathsInSigma

open import PropositionalTruncation


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-surj : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-surj f = (y : Y) → ∥ fib f y ∥

-- module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

--   embed-fib-is-prop : (f : X → Y) → is-embed f → (y : Y) → is-prop (fib f y)
--   embed-fib-is-prop f φ y = {!!}
--     where x₀ : fib f y
--           x₀ = {!!}
--           g : (x x' : X) → f x == f x' → x == x'
--           g x x' = p₁ (φ x x') 

--   surj-embed-is-equiv : (f : X → Y) → is-surj f → is-embed f → is-equiv f
--   surj-embed-is-equiv f φ ψ = g , {!!} , {!!} , {!!}
--     where g' = λ x x' → p₁ (ψ x x')
--           g : Y → X
--           g  = λ y → {!g'!}
--           h : (y : Y) → ∥ fib f y ∥ → fib f y
--           h y = recTrunc (fib f y) id (λ v w → dpair= (g' _ _ (p₂ v ◾ ! (p₂ w)) , tpt-paths-r f (g' _ _ (p₂ v ◾ ! (p₂ w))) (p₂ v) ◾ {!!}))


-- module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

--   is-inj : is-set X → is-set Y → (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
--   is-inj φ ψ f = (x y : X) → f x == f y → x == y 

--   set-inj-is-embed : (φ : is-set X) → (ψ : is-set Y)
--                      → (f : X → Y) → is-inj φ ψ f → is-embed f
--   set-inj-is-embed φ ψ f ρ = {!!}
  
--   set-eqv : (φ : is-set X) → (ψ : is-set Y)
--             → (f : X → Y) → is-inj φ ψ f → is-surj f → X ≃ Y
--   set-eqv φ ψ f ρ σ = f , surj-embed-is-equiv f σ (set-inj-is-embed φ ψ f ρ)
