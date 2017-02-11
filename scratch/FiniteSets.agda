{-# OPTIONS --without-K  #-}

open import Type
open import Zero
open import One
open import NaturalNumbers


data FinSet : ℕ → Type₀ where
  fzero : (n : ℕ) → FinSet (succ n)
  fsucc : (n : ℕ) → FinSet n → FinSet (succ n)

{-# DISPLAY fzero n = 0 #-}
{-# DISPLAY fsucc n m = succ n #-}

pattern zero = fzero


FinSet-to-ℕ : {n : ℕ} → FinSet n → ℕ
FinSet-to-ℕ (fzero m) = 0
FinSet-to-ℕ (fsucc m n) = succ (FinSet-to-ℕ n)

Subset : (n : ℕ) → Type₁
Subset n = FinSet n → Type₀

_∈_ : {n : ℕ} → (x : FinSet n) → (Y : Subset n) → Type₀
x ∈ Y = Y x

_⊆_ : {n : ℕ} → (X : Subset n) → (Y : Subset n) → Type₀
_⊆_ {n} X Y = (x : FinSet n) → x ∈ X → x ∈ Y

chop : {ℓ : Level} → {X : Type ℓ}→ (ℕ → X) → (n : ℕ) → FinSet n → X 
chop f zero ()
chop f (succ n) m = f (FinSet-to-ℕ (fsucc (succ n) m))


module Example where

  X : Subset 8
  X = chop f 8
    where f : ℕ → Type₀
          f 2 = 𝟙
          f 4 = 𝟙
          f n = 𝟘

  Y : Subset 8
  Y = chop f 8
    where f : ℕ → Type₀
          f 2 = 𝟙
          f 3 = 𝟙
          f 4 = 𝟙
          f n = 𝟘

  X⊆Y : X ⊆ Y
  X⊆Y 0 ()
  X⊆Y (fsucc fzero) 0₁ = 0₁
  X⊆Y (fsucc (fsucc fzero)) ()
  X⊆Y (fsucc (fsucc (fsucc fzero))) 0₁ = 0₁
  X⊆Y (fsucc (fsucc (fsucc (fsucc fzero)))) ()
  X⊆Y (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))) ()
  X⊆Y (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))) ()
  X⊆Y (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) ()
  X⊆Y (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc ())))))))) x




-- module HomotopyStuff where
--   open import DependentSum
--   open import Paths
--   open import Equivalences
--   open import OneTypes

--   FinSet-is-set : (n : ℕ) → is-set (FinSet n)
--   FinSet-is-set n = {!!}

--   FinSet0≃𝟘 : FinSet 0 ≃ 𝟘
--   FinSet0≃𝟘 = logical-eqv (λ ()) (λ ()) (λ ()) (λ ())

--   FinSet1≃𝟙 : FinSet 1 ≃ 𝟙
--   FinSet1≃𝟙 = logical-eqv (contr-is-prop FinSet1-is-contr)
--                           (contr-is-prop 𝟙-is-contr)
--                           (λ x → 0₁) (λ x → fzero)
--     where f : (y : FinSet 1) → fzero == y
--           f fzero = refl fzero
--           f (fsucc ())
--           FinSet1-is-contr : is-contr (FinSet 1)
--           FinSet1-is-contr = fzero , f

