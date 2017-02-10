{-# OPTIONS --without-K #-}
module PathsInOne where

open import Type
open import Functions
open import DependentSum
open import One
open import Paths
open import Homotopies
open import Equivalences


0₁= : {x y : 𝟙} → 𝟙 → (x == y)
0₁= {0₁} {0₁} 0₁ = refl 0₁

0₁=-e : {x y : 𝟙} → (x == y) → 𝟙
0₁=-e p = 0₁

0₁=-β : {x y : 𝟙} → 0₁=-e {x} {y} ∘ 0₁= ∼ id
0₁=-β 0₁ = refl 0₁

0₁=-η : {x y : 𝟙} → 0₁= ∘ 0₁=-e {x} {y} ∼ id
0₁=-η (refl 0₁) = refl (refl 0₁)

0₁=-τ : {x y : 𝟙} → ap (0₁=-e {x} {y}) ∘ 0₁=-η ∼ 0₁=-β {x} {y} ∘ 0₁=-e
0₁=-τ (refl 0₁) = refl (refl 0₁)

0₁=-e-is-equiv : {x y : 𝟙} → (x == y) ≃ 𝟙
0₁=-e-is-equiv {x} {y} = 0₁=-e {x} {y} , 0₁= , 0₁=-η , 0₁=-β {x} {y} , 0₁=-τ


𝟙-has-one-elem : (x y : 𝟙) → x == y
𝟙-has-one-elem x y = 0₁= {x} {y} 0₁
