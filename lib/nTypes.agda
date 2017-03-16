{-# OPTIONS --without-K #-}
module nTypes where

open import Type public
open import Functions public
open import DependentSum public
open import Paths public
open import Homotopies public
open import Equivalences public
open import NaturalNumbers public
open import OneTypes public


data ℕ₋₂ : Type₀ where
  zero-2 : ℕ₋₂
  succ-2 : ℕ₋₂ → ℕ₋₂

lvl-2 = zero-2
lvl-1 = succ-2 zero-2
lvl : ℕ → ℕ₋₂
lvl zero = succ-2 (succ-2 zero-2)
lvl (succ n) = succ-2 (lvl n)

module _ {ℓ : Level} where

  has-lvl : Type ℓ → ℕ₋₂ → Type ℓ
  has-lvl X zero-2 = is-contr X
  has-lvl X (succ-2 n) = (x y : X) → has-lvl (x == y) n


module _ {ℓ : Level} {X : Type ℓ} where

  contr-has-lvl-2 : is-contr X → has-lvl X lvl-2
  contr-has-lvl-2 w = w

  lvl-2-is-contr : has-lvl X lvl-2 → is-contr X
  lvl-2-is-contr w = w

  prop-has-lvl-1 : is-prop X → has-lvl X lvl-1
  prop-has-lvl-1 φ x y =
    φ x y , (λ q → prop-is-set φ _ _ _ _)

  lvl-1-is-prop : has-lvl X lvl-1 → is-prop X
  lvl-1-is-prop φ x y = p₁ (φ x y)

  set-has-lvl0 : is-set X → has-lvl X (lvl 0)
  set-has-lvl0 φ x y p q =
    φ x y p q , (λ α → set-is-1type φ _ _ _ _ _ _)

  lvl0-is-set : has-lvl X (lvl 0) → is-set X
  lvl0-is-set φ x y p q = p₁ (φ x y p q)


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  retract-prsrv-contr : is-retract Y X → is-contr X → is-contr Y
  retract-prsrv-contr (r , s , φ) (x , ψ) =
    r x , (λ y → ap r (ψ (s y)) ◾ φ y)

module _ {ℓ₁ ℓ₂ : Level} where

  retract-has-lvl : {X : Type ℓ₁} → {Y : Type ℓ₂} → (r : X → Y) → is-retraction r
                    → {n : ℕ₋₂} → has-lvl X n → has-lvl Y n
  retract-has-lvl r (s , φ) {zero-2} w = retract-prsrv-contr (r , s , φ) w
  retract-has-lvl {X} {Y} r (s , φ) {succ-2 n} ψ y y' = retract-has-lvl r' (s' , φ') {n} (ψ (s y) (s y')) 
    where r' : {y y' : Y} → s y == s y' → y == y'
          r' {y} {y'} p = ! (φ y) ◾ ap r p ◾ φ y'
          s' : {y y' : Y} → y == y' → s y == s y'
          s' = ap s
          φ' : {y y' : Y} → r' ∘ s' {y} {y'} ∼ id
          φ' {y} {y'} q = (! (φ y) [1,1,2] α [2,1,1] φ y')
                          ◾ (! (φ y) [1,1,2] ◾assoc _ _ _)
                          ◾ (! (φ y) [1,1,2] φ y [1,1,2] ◾assoc _ _ _)
                          ◾ (! (φ y) [1,1,2] φ y [1,1,2] q [1,1,2] ◾invl _)
                          ◾ (! (φ y) [1,1,2] φ y [1,1,2] ◾unitr _)
                          ◾ ! (◾assoc _ _ _)
                          ◾ (◾invl _ [2,1,1] q)
                          ◾ ◾unitl _
             where α = ! (ap∘ r s _) ◾ l₁=r₁◾r₂◾!l₂ (! (nat-id φ q))


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where
  
  retract-prsrv-prop : is-retract Y X → is-prop X → is-prop Y
  retract-prsrv-prop w φ = lvl-1-is-prop (retract-has-lvl (p₁ w) (p₂ w) (prop-has-lvl-1 φ))
  
  retract-prsrv-set : is-retract Y X → is-set X → is-set Y
  retract-prsrv-set w φ = lvl0-is-set (retract-has-lvl (p₁ w) (p₂ w) (set-has-lvl0 φ))
