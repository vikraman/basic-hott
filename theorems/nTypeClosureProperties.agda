{-# OPTIONS --without-K #-}
module theorems.nTypeClosureProperties where

open import IntensionalTypeTheory
open import FunctionExtensionality


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  ×-preserves-sets : {Y : Type ℓ₂} → is-set X → is-set Y → is-set (X × Y)
  ×-preserves-sets f g (x , y) (x' , y') w w' =
    ! (pair=-η w) ◾ ap pair= (pair= (α , β)) ◾ pair=-η w' 
    where p  = ap p₁ w
          q  = ap p₂ w
          p' = ap p₁ w'
          q' = ap p₂ w'
          α  = f x x' p p'
          β  = g y y' q q'

  Σ-preserves-sets : {P : X → Type ℓ₂}
                     → is-set X → ((x : X) → is-set (P x)) → is-set (Σ X P)
  Σ-preserves-sets {P = P} f g (x , y) (x' , y') w w' =
    ! (dpair=-η w) ◾ ap dpair= (dpair= (α , β)) ◾ dpair=-η w'
    where p  = dpair=-e₁ w
          q  = dpair=-e₂ w
          p' = dpair=-e₁ w'
          q' = dpair=-e₂ w'
          α  = f x x' p p'
          β  = g x' (tpt P p' y) y'
                 (tpt (λ p → tpt P p y == y') α q) q'

  Π-preserves-sets : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {P : X → Type ℓ₂}
                     → ((x : X) → is-set (P x)) → is-set (Π X P)
  Π-preserves-sets w f f' p p' =
    ! (funext-η p) ◾ ap funext (funext H) ◾ funext-η p'
    where h  = happly p
          h' = happly p'
          H : h ∼ h'
          H x = w x (f x) (f' x) (h x) (h' x)         
