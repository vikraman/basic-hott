{-# OPTIONS --without-K #-}
module OneTypes where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Equivalences
open import Zero
open import One
open import PathsInOne


module _ {ℓ : Level} where

  is-contr : Type ℓ → Type ℓ
  is-contr X = Σ X (λ x → (y : X) → (x == y))

  is-prop : Type ℓ → Type ℓ
  is-prop X = (x y : X) → x == y
  
  is-set : Type ℓ → Type ℓ
  is-set X = (x y : X) → (p q : x == y) → p == q

  is-1type : Type ℓ → Type ℓ
  is-1type X = (x y : X) → (p q : x == y) → (α β : p == q) → α == β


module _ {ℓ : Level} {X : Type ℓ} where

  contr-is-prop : is-contr X → is-prop X
  contr-is-prop (x₀ , φ) x y = ! (φ x) ◾ φ y
  
  prop-is-set : is-prop X → is-set X
  prop-is-set φ x y p q =
    α ◾ ! β
    where α = l₂=!l₁◾r (! (tpt=l x p (φ x x)) ◾ apd _ (φ x) p)
          β = l₂=!l₁◾r (! (tpt=l x q (φ x x)) ◾ apd _ (φ x) q)

  set-is-1type : is-set X → is-1type X
  set-is-1type w x y p q α β =
    A ◾ ! B
    where w' = w x y p
          A = l₂=!l₁◾r (! (tpt=l p α (w' p)) ◾ apd _ w' α)
          B = l₂=!l₁◾r (! (tpt=l p β (w' p)) ◾ apd _ w' β)

  contr-is-set = prop-is-set ∘ contr-is-prop
  contr-is-1type = set-is-1type ∘ contr-is-set
  prop-is-1type = set-is-1type ∘ prop-is-set


module _ where

  prop : (ℓ : Level) → Type (lsuc ℓ)
  prop ℓ = Σ (Type ℓ) is-prop

  prop₀ = prop lzero
  prop₁ = prop (lsuc lzero)

  set : (ℓ : Level) → Type (lsuc ℓ)
  set ℓ = Σ (Type ℓ) is-set

  set₀ = set lzero
  set₁ = set (lsuc lzero)

  1type : (ℓ : Level) → Type (lsuc ℓ)
  1type ℓ = Σ (Type ℓ) is-1type

  1type₀ = 1type lzero
  1type₁ = 1type (lsuc lzero)


---

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop ()

𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = 0₁ , 𝟙-has-one-elem _


inhab-prop≃𝟙 : {ℓ : Level} → {X : Type ℓ} → (x : X) → is-prop X → X ≃ 𝟙
inhab-prop≃𝟙 x φ =
  f , g , h , k , adj
  where f = λ z → 0₁
        g = λ z → x
        h = φ x
        k = λ z → 𝟙-has-one-elem _ _
        adj = λ z → contr-is-set 𝟙-is-contr _ _ _ _




module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  retract-preserves-contr : is-retract Y X → is-contr X → is-contr Y
  retract-preserves-contr (r , s , φ) (x , ψ) =
    r x , (λ y → ap r (ψ (s y)) ◾ φ y)


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  logical-eqv : is-prop X → is-prop Y → (X → Y) → (Y → X) → X ≃ Y
  logical-eqv φ ψ f g = f , g , h , k , adj
    where h = λ x → φ _ _
          k = λ x → ψ _ _
          adj = λ x → prop-is-set ψ _ _ _ _
