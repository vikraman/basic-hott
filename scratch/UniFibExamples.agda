{-# OPTIONS --without-K #-}
module UniFibExamples where

open import UnivalentTypeTheory
open import Surjections
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

  Ω[𝟚]≃Aut𝟚 : (Ω (BAut 𝟚) b₀) ≃ (𝟚 ≃ 𝟚)
  Ω[𝟚]≃Aut𝟚 = ΩBAut≃Aut 𝟚

  𝟚-is-set : is-set 𝟚
  𝟚-is-set = retract-prsrv-set (equiv-is-retract 𝟙+𝟙≃𝟚)
                               (+-prsrv-set (contr-is-set 𝟙-is-contr)
                                            (contr-is-set 𝟙-is-contr))
                                            
  Aut𝟚-is-set : is-set (𝟚 ≃ 𝟚)
  Aut𝟚-is-set = eqv-prsrv-set 𝟚-is-set


module _ where
  
  [𝟚] : Type (lsuc lzero)
  [𝟚] = Σ Type₀ (λ X → ∥ X == 𝟚 ∥)

  `𝟚 : [𝟚]
  `𝟚 = (𝟚 , ∣ refl 𝟚 ∣)

  `id : `𝟚 == `𝟚
  `id = dpair= (refl 𝟚 , identify _ _)
  
  `not : `𝟚 == `𝟚
  `not = dpair= (ua not-eqv , identify _ _)


module ModelsOfP where

  data P₀ : Type₀ where
    2ₚ : P₀

  M₀ : P₀ → ∥ [𝟚] ∥₀
  M₀ 2ₚ = ∣ `𝟚 ∣₀

  M₀-is-equiv : is-equiv M₀
  M₀-is-equiv = {!!}

  -----
  
  data P₁ : Type₀ where
    idₚ : P₀ → P₁
    notₚ : P₁
    _∘ₚ_ : P₁ → P₁ → P₁
    !ₚ : P₁ → P₁

  -- here the set truncation is unneeded as the space is already a 0-type
  M₁ : P₁ → Ω [𝟚] `𝟚
  M₁ (idₚ 2ₚ) = refl `𝟚
  M₁ notₚ = `not
  M₁ (p ∘ₚ q) = M₁ p ◾ M₁ q
  M₁ (!ₚ p) = ! (M₁ p)

  M₁-is-surj : is-surj M₁
  M₁-is-surj = {!!}

  -----
  
  data P₂ : Type₀ where
    not∘ₚnot=id : P₂
    
    ∘ₚ-unitr : (p : P₁) → P₂
    ∘ₚ-unitl : (p : P₁) → P₂
    ∘ₚ-assoc : (p q r : P₁) → P₂ 
    ∘ₚ-invr : (p : P₁) → P₂
    ∘ₚ-invl : (p : P₁) → P₂

    -- etcetera


  M₂ : P₂ → fib M₁ (refl `𝟚)
  M₂ not∘ₚnot=id = (notₚ ∘ₚ notₚ) , {!!} -- ρ : `not ◾ `not == refl `𝟚
  M₂ (∘ₚ-unitr (idₚ x)) = {!!}
  M₂ (∘ₚ-unitr notₚ) = {!!}
  M₂ (∘ₚ-unitr (p ∘ₚ p₃)) = {!!}
  M₂ (∘ₚ-unitr (!ₚ p)) = {!!} 
  M₂ = {!!}

  M₂-is-surj : is-surj M₂
  M₂-is-surj = {!!}


  -- fibers of M₁ are homotopy equivalent
