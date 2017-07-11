{-# OPTIONS --without-K #-}
module OneTypesFunExt where


open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import ContractibleFunctions
open import OneTypes
open import PathsInSigma
open import FunctionExtensionality


module _ {ℓ} where

  is-contr-is-prop : (X : Type ℓ) → is-prop (is-contr X)
  is-contr-is-prop X (x , φ) (y , ψ) =
    dpair= (φ y , funext (λ z → contr-is-set (x , φ) _ _ _ _))
  
  is-prop-is-prop : (X : Type ℓ) → is-prop (is-prop X)
  is-prop-is-prop X φ ψ = funext (λ x →
                          funext (λ y →
                          prop-is-set φ _ _ _ _))

  is-set-is-prop : (X : Type ℓ) → is-prop (is-set X)
  is-set-is-prop X φ ψ = funext (λ x →
                         funext (λ y →
                         funext (λ p →
                         funext (λ q →
                         set-is-1type φ _ _ _ _ _ _))))


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  Π-prsrv-contr : {P : X → Type ℓ₂}
                  → ((x : X) → is-contr (P x)) → is-contr (Π X P)
  Π-prsrv-contr {P} f = g , ψ
    where g : Π X P
          g x = p₁ (f x)
          ψ : (h : Π X P) → g == h
          ψ h = funext (λ x → ! (p₂ (f x) (g x)) ◾ (p₂ (f x) (h x)))

  Π-prsrv-prop : {P : X → Type ℓ₂}
                 → ((x : X) → is-prop (P x)) → is-prop (Π X P)
  Π-prsrv-prop f g h = funext (λ x → f x (g x) (h x))

  Π-prsrv-sets : {P : X → Type ℓ₂}
                 → ((x : X) → is-set (P x)) → is-set (Π X P)
  Π-prsrv-sets w f f' p p' =
    ! (funext-η p) ◾ ap funext (funext H) ◾ funext-η p'
    where h  = happly p
          h' = happly p'
          H : h ∼ h'
          H x = w x (f x) (f' x) (h x) (h' x)         


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-contr-fn-is-prop : (f : X → Y) → is-prop (is-contr-fn f)
  is-contr-fn-is-prop f φ ψ = contr-is-prop (Π-prsrv-contr ρ) φ ψ
    where ρ = (λ y → φ y , is-contr-is-prop _ _)
