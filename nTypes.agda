{-# OPTIONS --without-K #-}
module nTypes where

open import IntensionalTypeTheory


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

  prop-has-lvl-1 : is-prop X → has-lvl X lvl-1
  prop-has-lvl-1 φ x y =
    φ x y , (λ q → prop-is-set φ _ _ _ _)

  set-has-lvl0 : is-set X → has-lvl X (lvl 0)
  set-has-lvl0 φ x y p q =
    φ x y p q , (λ α → set-is-1type φ _ _ _ _ _ _)


module _ {ℓ₁ ℓ₂ : Level} where

  retract-has-lvl : {X : Type ℓ₁} → {Y : Type ℓ₂} → (r : X → Y) → is-retraction r
                    → {n : ℕ₋₂} → has-lvl X n → has-lvl Y n
  retract-has-lvl r (s , φ) {zero-2} w = retract-preserves-contr (r , s , φ) w
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
