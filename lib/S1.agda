{-# OPTIONS --without-K --rewriting #-} 
module S1 where

open import UnivalentTypeTheory
open import RewriteRelation


postulate
  S¹ : Type₀
  base : S¹
  loop : base == base


module RecS¹ {ℓ} (Y : Type ℓ)
             (base* : Y)
             (loop* : base* == base*) where
  postulate
    f : S¹ → Y
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  postulate
    loop-β : ap f loop == loop*

recS¹ = RecS¹.f


module IndS¹ {ℓ} (P : S¹ → Type ℓ)
             (base* : P base)
             (loop* : tpt P loop base* == base*) where
  postulate
    f : (x : S¹) → P x
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  postulate
    loop-β : apd P f loop == loop*

indS¹ = IndS¹.f
