{-# OPTIONS --without-K #-}
module ContractibleFunctions where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import PathsInSigma
open import OneTypes


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-contr-fn : (f : X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-contr-fn f = (y : Y) → is-contr (fib f y)


module HaeIsContrFn {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} {f : X → Y} where

  module HaeIsProp (e : is-hae f) (y : Y) (v w : fib f y) where

    g = p₁ e
    η = p₁ (p₂ e)
    ε = p₁ (p₂ (p₂ e))
    τ = p₂ (p₂ (p₂ e))

    x = p₁ v
    p = p₂ v
  
    x' = p₁ w
    p' = p₂ w

    q : f x == f x'
    q = p ◾ ! p'

    r : x == x'
    r = ! (η x) ◾ ap g q ◾ η x'

    ap-f-r : ap f r == ! (ap f (η x)) ◾ ap f (ap g q) ◾ ap f (η x')
    ap-f-r = ap◾ _ _ _ ◾ (ap! _ _ [2,0,2] ap◾ _ _ _)

    sq₁ : ε (f x) ◾ ap id q == ap (f ∘ g) q ◾ ε (f x') 
    sq₁ = nat ε q

    sq₂ : ap f (η x) ◾ q == ap f (ap g q) ◾ ap f (η x')
    sq₂ = pad-sq (! (τ x)) (ap-id _) (ap∘ _ _ _) (! (τ x')) sq₁

    ur' : ap f r == q
    ur' = ap-f-r ◾ ! (l₂=!l₁◾r sq₂)

    ur : tpt (paths-r f y) r p == p'
    ur = tpt-paths-r f r p
         ◾ ! (! (!! _) ◾ l₁=r◾!l₂ (! (mirror ur' ◾ !◾ _ _)) ◾ _ [1,0,2] !! _)

    hae-is-prop : v == w
    hae-is-prop = dpair= (r , ur)

  open HaeIsProp

  hae-is-contr : is-hae f → is-contr-fn f
  hae-is-contr (g , η , ε , τ) y = (g y , ε y) , hae-is-prop (g , η , ε , τ) _ _

  qinv-fib-is-contr : (φ : is-qinv f) → (y : Y) → is-contr (fib f y)
  qinv-fib-is-contr φ y = hae-is-contr (qinv-is-hae φ) y

open HaeIsContrFn public using (hae-is-contr ; qinv-fib-is-contr)

