{-# OPTIONS --without-K #-}
module _ where

open import Type


data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
