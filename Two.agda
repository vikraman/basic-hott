{-# OPTIONS --without-K #-}
module Two where

open import Type
open import Functions
open import DependentSum
open import Paths
open import PathsInSigma
open import Homotopies
open import Equivalences

data 𝟚 : Type₀ where
  0₂ : 𝟚
  1₂ : 𝟚

not : 𝟚 → 𝟚
not 0₂ = 1₂
not 1₂ = 0₂

not-is-equiv : is-equiv not
not-is-equiv = not , η , η , τ
  where η : not ∘ not ∼ id
        η 0₂ = refl 0₂
        η 1₂ = refl 1₂

        τ : ap not ∘ η ∼ η ∘ not
        τ 0₂ = refl (refl 1₂)
        τ 1₂ = refl (refl 0₂)

not-eqv : 𝟚 ≃ 𝟚
not-eqv = (not , not-is-equiv)
