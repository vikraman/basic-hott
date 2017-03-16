{-# OPTIONS --without-K #-}
module UniFibExamples where

open import UnivalentTypeTheory
open import PropositionalTruncation
open import SetTruncation


module _ {ℓ : Level} where

  Ω : (X : Type ℓ) → X → Type ℓ
  Ω X x = x == x 

module _ {ℓ : Level} where

  BAut : (X : Type ℓ) → Type (lsuc ℓ)
  BAut X = Σ (Type ℓ) (λ Y → ∥ X ≃ Y ∥)

  pr₁ : {X : Type ℓ} → BAut X → Type ℓ
  pr₁ (Y , q) = Y

  b₀ : {X : Type ℓ} → BAut X
  b₀ {X} = X , ∣ ide X ∣

  tpt-eqv-pr₁ : {X : Type ℓ} → {v w : BAut X} → (p : v == w)
                → p₁ (tpt-eqv pr₁ p) == tpt id (dpair=-e₁ p)
  tpt-eqv-pr₁ (refl v) = refl id

  is-univ-fib-pr₁ : {X : Type ℓ} → is-univ-fib (pr₁ {X})
  is-univ-fib-pr₁ (Y , q) (Y' , r) = g , η , ε , τ
    where g : Y ≃ Y' → Y , q == Y' , r
          g e = dpair= (ua e , identify _ _)
          η : g ∘ tpt-eqv pr₁ ∼ id
          η (refl w) = ap dpair= (dpair= (ua-ide Y , prop-is-set identify _ _ _ _))
          ε : tpt-eqv pr₁ ∘ g ∼ id
          ε e = eqv= (tpt-eqv-pr₁ (dpair= (ua e , identify _ _))
                      ◾ ap (tpt id) (dpair=-β₁ (ua e , identify _ _)) ◾ ua-β₁ e)
          τ : ap (tpt-eqv pr₁) ∘ η ∼ ε ∘ tpt-eqv pr₁
          τ (refl w) = {!!}

  ΩBAut≃Aut : (X : Type ℓ) → (Ω (BAut X) b₀) ≃ (X ≃ X)
  ΩBAut≃Aut X = tpt-eqv pr₁ , is-univ-fib-pr₁ b₀ b₀


module _ where
  
  [2] : Type (lsuc lzero)
  [2] = BAut 𝟚

  `𝟚 : [2]
  `𝟚 = b₀

  Ω[2]≃Aut𝟚 : (Ω [2] `𝟚) ≃ (𝟚 ≃ 𝟚)
  Ω[2]≃Aut𝟚 = ΩBAut≃Aut 𝟚


𝟚-is-set : is-set 𝟚
𝟚-is-set = retract-prsrv-set (equiv-is-retract 𝟙+𝟙≃𝟚)
                             (+-prsrv-set (contr-is-set 𝟙-is-contr)
                                          (contr-is-set 𝟙-is-contr))

module AutBoolClassification where

  data Perm₁ : Type₀ where
    idₚ : Perm₁
    notₚ : Perm₁

  Aut𝟚-is-set : is-set (𝟚 ≃ 𝟚)
  Aut𝟚-is-set = eqv-prsrv-set 𝟚-is-set

  f : Perm₁ → 𝟚 ≃ 𝟚
  f idₚ = ide 𝟚
  f notₚ = not-eqv

  thm1 : 𝟚 ≃ 𝟚 ≃ Perm₁
  thm1 = {!!}
