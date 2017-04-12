{-# OPTIONS --without-K #-}
module SetTruncation where

open import Type
open import Paths
open import OneTypes


-- module _ {ℓ₁} where

--   private
--     data #ParallelPair : Type ℓ₁ where
--       #0ₚ #1ₚ : #ParallelPair

--   ParallelPair : Type ℓ₁
--   ParallelPair = #ParallelPair

--   0ₚ 1ₚ : ParallelPair
--   0ₚ = #0ₚ
--   1ₚ = #1ₚ

--   postulate
--     sₚ tₚ : 0ₚ == 1ₚ



module _ {ℓ₁} where

  private
    data #∥_∥₀ (X : Type ℓ₁) : Type ℓ₁ where
      #∣_∣₀ : X → #∥ X ∥₀

  ∥_∥₀ : Type ℓ₁ → Type ℓ₁
  ∥_∥₀ = #∥_∥₀

  ∣_∣₀ : {X : Type ℓ₁} → X → ∥ X ∥₀
  ∣_∣₀ = #∣_∣₀ 

  postulate
    identify₀ : {X : Type ℓ₁} → {x y : ∥ X ∥₀} → (p q : x == y) → p == q

  recTrunc₀ : {ℓ₂ : Level} → {X : Type ℓ₁} → (Y : Type ℓ₂)
              → (X → Y) → is-set Y → ∥ X ∥₀ → Y
  recTrunc₀ Y f φ #∣ x ∣₀ = f x

  postulate
    recTrunc₀-β : {ℓ₂ : Level} → {X : Type ℓ₁} → (Y : Type ℓ₂)
                  → (f : X → Y) → (φ : is-set Y)
                  → {x x' : ∥ X ∥₀} → (p q : x == x')
                  → ap (ap (recTrunc₀ Y f φ)) (identify₀ p q) ==
                     φ _ _ (ap (recTrunc₀ Y f φ) p) (ap (recTrunc₀ Y f φ) q) 
  
  indTrunc₀ : {ℓ₂ : Level} → {X : Type ℓ₁} → (P : ∥ X ∥₀ → Type ℓ₂)
              → ((x : X) → P ∣ x ∣₀) → ((x : ∥ X ∥₀) → is-set (P x))
              → (x : ∥ X ∥₀) → P x
  indTrunc₀ P f φ #∣ x ∣₀ = f x

  postulate
    indTrunc₀-β : {ℓ₂ : Level} → {X : Type ℓ₁} → (P : ∥ X ∥₀ → Type ℓ₂)
                  → (f : (x : X) → P ∣ x ∣₀) → (φ : (x : ∥ X ∥₀) → is-set (P x))
                  → {x y : ∥ X ∥₀} → (p q : x == y)
                  → apd₂ P (indTrunc₀ P f φ) (identify₀ p q) ==
                     φ _ _ _
                       (apd P (indTrunc₀ P f φ) p)
                       (ap (λ p → tpt P p (indTrunc₀ P f φ x)) (identify₀ p q)
                        ◾ apd P (indTrunc₀ P f φ) q)

  -- TODO : Write down the fully general rec/ind principles
