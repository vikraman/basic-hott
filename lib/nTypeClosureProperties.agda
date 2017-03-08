{-# OPTIONS --without-K #-}
module nTypeClosureProperties where

open import IntensionalTypeTheory
open import FunctionExtensionality


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  ×-prsrv-contr : {Y : Type ℓ₂} → is-contr X → is-contr Y → is-contr (X × Y)
  ×-prsrv-contr (x , f) (y , g) = (x , y) , (λ w → pair= (f (p₁ w) , g (p₂ w)))
  
  Σ-prsrv-contr : {P : X → Type ℓ₂}
                  → is-contr X → ((x : X) → is-contr (P x)) → is-contr (Σ X P)
  Σ-prsrv-contr {P} (x , f) g = (x , p₁ (g x)) , φ
    where φ : (w : Σ X P) → x , p₁ (g x) == w
          φ (x' , ux') = dpair= (f x' , ! (p₂ (g x') (tpt P (f x') (p₁ (g x))))
                                        ◾ (p₂ (g x')) ux')

  Π-prsrv-contr : {P : X → Type ℓ₂}
                  → ((x : X) → is-contr (P x)) → is-contr (Π X P)
  Π-prsrv-contr {P} f = g , ψ
    where g : Π X P
          g x = p₁ (f x)
          ψ : (h : Π X P) → g == h
          ψ h = funext (λ x → ! (p₂ (f x) (g x)) ◾ (p₂ (f x) (h x)))


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  ×-prsrv-prop : {Y : Type ℓ₂} → is-prop X → is-prop Y → is-prop (X × Y)
  ×-prsrv-prop f g (x , y) (x' , y') = pair= (f x x' , g y y')
  
  Σ-prsrv-prop : {P : X → Type ℓ₂}
                 → is-prop X → ((x : X) → is-prop (P x)) → is-prop (Σ X P)
  Σ-prsrv-prop f g (x , y) (x' , y') = dpair= (f x x' , g _ _ _)
  
  Π-prsrv-prop : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {P : X → Type ℓ₂}
                 → ((x : X) → is-prop (P x)) → is-prop (Π X P)
  Π-prsrv-prop f g h = funext (λ x → f x (g x) (h x))


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  ×-prsrv-sets : {Y : Type ℓ₂} → is-set X → is-set Y → is-set (X × Y)
  ×-prsrv-sets f g (x , y) (x' , y') w w' =
    ! (pair=-η w) ◾ ap pair= (pair= (α , β)) ◾ pair=-η w' 
    where p  = ap p₁ w
          q  = ap p₂ w
          p' = ap p₁ w'
          q' = ap p₂ w'
          α  = f x x' p p'
          β  = g y y' q q'

  Σ-prsrv-sets : {P : X → Type ℓ₂}
                 → is-set X → ((x : X) → is-set (P x)) → is-set (Σ X P)
  Σ-prsrv-sets {P = P} f g (x , y) (x' , y') w w' =
    ! (dpair=-η w) ◾ ap dpair= (dpair= (α , β)) ◾ dpair=-η w'
    where p  = dpair=-e₁ w
          q  = dpair=-e₂ w
          p' = dpair=-e₁ w'
          q' = dpair=-e₂ w'
          α  = f x x' p p'
          β  = g x' (tpt P p' y) y'
                 (tpt (λ p → tpt P p y == y') α q) q'

  Π-prsrv-sets : {P : X → Type ℓ₂}
                 → ((x : X) → is-set (P x)) → is-set (Π X P)
  Π-prsrv-sets w f f' p p' =
    ! (funext-η p) ◾ ap funext (funext H) ◾ funext-η p'
    where h  = happly p
          h' = happly p'
          H : h ∼ h'
          H x = w x (f x) (f' x) (h x) (h' x)         
