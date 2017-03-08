{-# OPTIONS --without-K #-}
module UniFibExamples where

open import UnivalentTypeTheory
open import PropositionalTruncation


module _ {ℓ : Level} where

  Ω : (X : Type ℓ) → X → Type ℓ
  Ω X x = x == x 

module _ {ℓ₁ : Level} (X : Type ℓ₁) where

  BAutX = Σ (Type ℓ₁) (λ Y → ∥ X ≃ Y ∥)

  pr₁ : BAutX → Type ℓ₁
  pr₁ (Y , q) = Y

  b₀ : BAutX
  b₀ = X , ∣ ide X ∣

  lem1 : {v w : BAutX} → (p : v == w) → p₁ (tpt-eqv pr₁ p) == tpt id (dpair=-e₁ p)
  lem1 (refl v) = refl id

  is-equiv-is-prop : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {Y : Type ℓ₂}
                     → (f : X → Y) → is-prop (is-equiv f)
  is-equiv-is-prop = {!!}

  eqv= : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {Y : Type ℓ₂}
         {e e' : X ≃ Y} → p₁ e == p₁ e' → e == e'
  eqv= {e = e} {e'} φ = dpair= (φ , is-equiv-is-prop _ _ _ )


  is-univ-fib-pr₁ : is-univ-fib pr₁
  is-univ-fib-pr₁ (Y , q) (Y' , r) = g , η , ε , τ
    where g : Y ≃ Y' → Y , q == Y' , r
          g e = dpair= (ua e , identify _ _)
          η : g ∘ tpt-eqv pr₁ ∼ id
          η (refl w) = ap dpair= (dpair= (ua-ide Y , prop-is-set identify _ _ _ _))
          ε : tpt-eqv pr₁ ∘ g ∼ id
          ε e = eqv= (lem1 (dpair= (ua e , identify _ _)) ◾ ap (tpt id) (dpair=-β₁ (ua e , identify _ _)) ◾ ua-β₁ e)
          τ : ap (tpt-eqv pr₁) ∘ η ∼ ε ∘ tpt-eqv pr₁
          τ (refl w) = refl (ap (tpt-eqv pr₁) (η (refl (Y , q)))) ◾ {!!} ◾ refl (ε (ide Y))


  easy : (Ω BAutX b₀) ≃ (X ≃ X)
  easy = tpt-eqv pr₁ , is-univ-fib-pr₁ b₀ b₀
