{-# OPTIONS --without-K #-}
module _ where

open import Type

data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

add : ℕ → ℕ → ℕ
add zero m = m
add (succ n) m = succ (add n m)

{-# BUILTIN NATPLUS add #-}

mult : ℕ → ℕ → ℕ
mult zero m = zero
mult (succ n) m = add m (mult n m)

{-# BUILTIN NATTIMES mult #-}

indℕ : ∀ {ℓ} (P : ℕ → Type ℓ) → P 0 → ((n : ℕ) → P n → P (succ n)) → (n : ℕ) → P n
indℕ _ z _ 0 = z
indℕ P z s (succ n) = s n (indℕ P z s n)

recℕ : ∀ {ℓ} (C : Type ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C = indℕ (λ _ → C)

open import Paths
open import OneTypes
open import Coproduct

succ-inj : {x y : ℕ} → succ x == succ y → x == y
succ-inj (refl .(succ _)) = refl _

ℕ-has-dec-eq : has-dec-eq ℕ
ℕ-has-dec-eq zero zero = i₁ (refl zero)
ℕ-has-dec-eq zero (succ y) = i₂ (λ ())
ℕ-has-dec-eq (succ x) zero = i₂ (λ ())
ℕ-has-dec-eq (succ x) (succ y) with ℕ-has-dec-eq x y
... | i₁ p = i₁ (ap succ p)
... | i₂ p = i₂ (λ q → p (succ-inj q))

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ ℕ-has-dec-eq
