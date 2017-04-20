{-# OPTIONS --without-K #-}
module PathsInCoproduct where

open import Type
open import Functions
open import DependentSum
open import Coproduct
open import Paths
open import Homotopies
open import Equivalences
open import Zero
open import One


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} {x₀ : X} where

  i₁=code : X + Y → Type ℓ₁
  i₁=code (i₁ x) = x₀ == x
  i₁=code (i₂ y) = 𝟘'

  i₁= : {u : X + Y} → i₁=code u → (i₁ x₀ == u)
  i₁= {(i₁ x)} = λ p → ap i₁ p
  i₁= {(i₂ y)} ()

  i₁=-e : {u : X + Y} → (i₁ x₀ == u) → i₁=code u
  i₁=-e = ind=l (λ {u} p → i₁=code u) (refl x₀)

  i₁=-β : {u : X + Y} → i₁=-e {u} ∘ i₁= {u} ∼ id
  i₁=-β {(i₁ x)} = ind=l (λ {x} p → i₁=-e {(i₁ x)} (i₁= {(i₁ x)} p) == p)
                        (refl (refl x₀))
  i₁=-β {(i₂ y)} ()

  i₁=-η : {u : X + Y} → i₁= {u} ∘ i₁=-e {u} ∼ id
  i₁=-η = ind=l (λ {u} p → i₁= {u} (i₁=-e {u} p) == p)
                (refl (refl (i₁ x₀)))

  i₁=-τ : {u : X + Y} → ap (i₁=-e {u}) ∘ i₁=-η {u} ∼ i₁=-β {u} ∘ i₁=-e {u}
  i₁=-τ = ind=l (λ {u} p → (ap (i₁=-e {u}) ∘ i₁=-η {u}) p == (i₁=-β {u} ∘ i₁=-e {u}) p)
                (refl (refl (refl x₀)))
  
  paths-in-+₁ : (u : X + Y) → (i₁ x₀ == u) ≃ i₁=code u
  paths-in-+₁ u = i₁=-e {u} , i₁= {u} , i₁=-η {u} , i₁=-β {u} , i₁=-τ {u}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} {y₀ : Y} where

  i₂=code : X + Y → Type ℓ₂
  i₂=code (i₁ x) = 𝟘'
  i₂=code (i₂ y) = y₀ == y

  i₂= : {u : X + Y} → i₂=code u → (i₂ y₀ == u)
  i₂= {(i₁ x)} ()
  i₂= {(i₂ y)} = λ p → ap i₂ p

  i₂=-e : {u : X + Y} → (i₂ y₀ == u) → i₂=code u
  i₂=-e = ind=l (λ {u} p → i₂=code u) (refl y₀)

  i₂=-β : {u : X + Y} → i₂=-e {u} ∘ i₂= {u} ∼ id
  i₂=-β {(i₁ x)} ()
  i₂=-β {(i₂ y)} = ind=l (λ {y} p → i₂=-e {(i₂ y)} (i₂= {(i₂ y)} p) == p)
                         (refl (refl y₀))

  i₂=-η : {u : X + Y} → i₂= {u} ∘ i₂=-e {u} ∼ id
  i₂=-η = ind=l (λ {u} p → i₂= {u} (i₂=-e {u} p) == p)
                (refl (refl (i₂ y₀)))

  i₂=-τ : {u : X + Y} → ap (i₂=-e {u}) ∘ i₂=-η {u} ∼ i₂=-β {u} ∘ i₂=-e {u}
  i₂=-τ = ind=l (λ {u} p → (ap (i₂=-e {u}) ∘ i₂=-η {u}) p == (i₂=-β {u} ∘ i₂=-e {u}) p)
                (refl (refl (refl y₀)))
  
  paths-in-+₂ : (u : X + Y) → (i₂ y₀ == u) ≃ i₂=code u
  paths-in-+₂ u = i₂=-e {u} , i₂= {u} , i₂=-η {u} , i₂=-β {u} , i₂=-τ {u}
