{-# OPTIONS --without-K #-}
module Type where

open import Agda.Primitive public using (Level ; lsuc ; lzero ; _⊔_)


Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

Type₀ = Type lzero
Type₁ = Type (lsuc lzero)

