{-# OPTIONS --without-K --rewriting #-} 
module Suspension where

open import UnivalentTypeTheory
open import RewriteRelation


module Suspension {ℓ} (X : Type ℓ) where

  postulate
    Susp : Type ℓ
    north : Susp
    south : Susp
    merid : (x : X) → north == south

Susp = Suspension.Susp

module _ {ℓ} {X : Type ℓ} where
  north = Suspension.north X
  south = Suspension.south X
  merid = Suspension.merid X

module RecSusp {ℓ₁ ℓ₂} {X : Type ℓ₁} (Y : Type ℓ₂)
               (north* : Y) (south* : Y)
               (merid* : (x : X) → north* == south*) where

  postulate
    f : Susp X → Y
    north-β : f north ↦ north*
    south-β : f south ↦ south*
  {-# REWRITE north-β #-}
  {-# REWRITE south-β #-}

  postulate
    merid-β : (x : X) → ap f (merid x) == merid* x

recSusp = RecSusp.f

module IndSusp {ℓ₁ ℓ₂} {X : Type ℓ₁} (P : Susp X → Type ℓ₂)
               (north* : P north) (south* : P south)
               (merid* : (x : X) → tpt P (merid x) north* == south*) where

  postulate
    f : (x : Susp X) → P x 
    north-β : f north ↦ north*
    south-β : f south ↦ south*
  {-# REWRITE north-β #-}
  {-# REWRITE south-β #-}

  postulate
    merid-β : (x : X) → apd P f (merid x) == merid* x

indSusp = IndSusp.f


open import S1
