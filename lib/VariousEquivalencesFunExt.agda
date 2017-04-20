{-# OPTIONS --without-K #-}
module VariousEquivalencesFunExt where

open import IntensionalTypeTheory
open import FunctionExtensionality


module PiPreservesFiberwiseEquiv {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  ap-funext : {P Q : X → Type ℓ₂} → (F : (x : X) → P x → Q x)
              → {f g : (x : X) → P x} → (φ : f ∼ g)
              → ap (λ f x → F x (f x)) (funext φ) == funext (λ x → ap (F x) (φ x))
  ap-funext F = ind∼ (λ {f} {g} φ → ap (λ f x → F x (f x)) (funext φ) ==
                                     funext (λ x → ap (F x) (φ x)))
                     (λ f → (ap (λ γ → ap (λ f x → F x (f x)) γ) (funext-idh f)
                            ◾ ! (funext-idh (λ x → F x (f x)))))

  Π-fib-eqv : {P Q : X → Type ℓ₂} → ((x : X) → P x ≃ Q x) → Π X P ≃ Π X Q
  Π-fib-eqv h = f , g , η , ε , τ
    where f' = λ x → p₁ (h x)
          g' = λ x → p₁ (p₂ (h x))
          η' = λ x → p₁ (p₂ (p₂ (h x)))
          ε' = λ x → p₁ (p₂ (p₂ (p₂ (h x))))
          τ' = λ x → p₂ (p₂ (p₂ (p₂ (h x))))
          f = λ r x → f' x (r x)
          g = λ s x → g' x (s x)
          η : g ∘ f ∼ id
          η r = funext (λ x → η' x (r x))
          ε : f ∘ g ∼ id
          ε s = funext (λ x → ε' x (s x))
          τ : ap f ∘ η ∼ ε ∘ f
          τ r = (ap-funext f' (λ x → η' x (r x)) ◾
                ap funext (funext (λ x → τ' x (r x))))

open PiPreservesFiberwiseEquiv public using (Π-fib-eqv)
