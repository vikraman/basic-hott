{-# OPTIONS --without-K #-}
module Univalence where

open import IntensionalTypeTheory


postulate
  univalence : {ℓ : Level} → (X Y : Type ℓ) → is-equiv (path-to-eqv {ℓ} {X} {Y})


module _ {ℓ} {X Y : Type ℓ} where

  ua : X ≃ Y → X == Y
  ua = p₁ (univalence X Y)

  -- ua-e is path-to-eqv
  -- ua-e₁ is (tpt id)
  
  ua-β : path-to-eqv ∘ ua ∼ id
  ua-β = p₁ (p₂ (p₂ (univalence X Y)))

  ua-β₁ : tpt id ∘ ua ∼ p₁
  ua-β₁ = dpair=-e₁ ∘ ua-β

  ua-η : ua ∘ path-to-eqv ∼ id
  ua-η = p₁ (p₂ (univalence X Y))


ua-ide : {ℓ : Level} → (X : Type ℓ) → ua (ide X) == refl X
ua-ide X = ua-η (refl X)



module _ {ℓ ℓ'} where  
  
  ind≃ : (P : {X Y : Type ℓ} → X ≃ Y → Type ℓ')
         → (r : (X : Type ℓ) → P (ide X))
         → {X Y : Type ℓ} → (e : X ≃ Y) → P e
  ind≃ P r {X} {Y} e = φ e (f (ua e))
    where φ : {X Y : Type ℓ} → (e : X ≃ Y) → P (path-to-eqv (ua e)) → P e
          φ = coe ∘ ap P ∘ ua-β
          
          f : {X Y : Type ℓ} → (p : X == Y) → P (path-to-eqv p)
          f (refl X) = r X

  -- ind≃r : {Y : Type ℓ}
  --         → (P : {X : Type ℓ} → X ≃ Y → Type ℓ')
  --         → (r : P (ide Y))
  --         → {X : Type ℓ} → (e : X ≃ Y) → P e
  -- ind≃r = {!!}

  -- ind≃l : {X : Type ℓ}
  --         → (P : {Y : Type ℓ} → X ≃ Y → Type ℓ')
  --         → (r : P (ide X))
  --         → {Y : Type ℓ} → (e : X ≃ Y) → P e
  -- ind≃l = {!!}



module _ {ℓ} {X Y : Type ℓ} where

  ua-η-! : {X Y : Type ℓ} → (p : X == Y) → ua (!e (path-to-eqv p)) == ! p
  ua-η-! (refl X) = ua-ide X
  
  ua-!e : (e : X ≃ Y) → ua (!e e) == ! (ua e)
  ua-!e e =  ap (ua ∘ !e) (! (ua-β _)) ◾ ua-η-! _


module _ {ℓ} where

  ua-η-◾ : {X Y Z : Type ℓ} → (p : X == Y) → (q : Y == Z) → ua (path-to-eqv q ● path-to-eqv p) == p ◾ q
  ua-η-◾ p q = ap ua (! (path-to-eqv-◾ _ _)) ◾ ua-η _

  ua-● : {X Y Z : Type ℓ} → (e : Y ≃ Z) → (e' : X ≃ Y) → ua (e ● e') == ua e' ◾ ua e
  ua-● e e' = ap ua (ap (e ●-) (! (ua-β _))
              ◾ ap (-● _) (! (ua-β _)))
              ◾ ua-η-◾ _ _

