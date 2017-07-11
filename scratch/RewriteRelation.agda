{-# OPTIONS --without-K --rewriting #-} 
module RewriteRelation where

open import Type

module _ {ℓ} {X : Type ℓ} where
  infix 30 _↦_
  postulate 
    _↦_ : X → X → Type ℓ
{-# BUILTIN REWRITE _↦_ #-}
