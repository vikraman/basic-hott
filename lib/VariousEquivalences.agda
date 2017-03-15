{-# OPTIONS --without-K #-}

module VariousEquivalences where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences
open import PathsInSigma


module _ {ℓ : Level} {X : Type ℓ} where

  !-is-equiv : {x y : X} → is-equiv (! {x = x} {y})
  !-is-equiv = ! , !! , !! , !!!


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  tpt!-is-equiv : {x y : X} → (p : x == y)
                  → (ux : P x) → (uy : P y) → is-equiv (tpt! p ux uy)
  tpt!-is-equiv (refl x) ux uy = !-is-equiv {x = uy} {ux}

  !-anticomm-tpt : {x y : X} → (p : x == y) → (ux : P x) → (uy : P y)
                   → (tpt P (! p) uy == ux) ≃ (tpt P p ux == uy)
  !-anticomm-tpt p ux uy = (tpt! p ux uy) , (tpt!-is-equiv p ux uy)


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} where

  ×-unv-prp-is-equiv : is-equiv (×-unv-prp {X = X} {Y} {Z})
  ×-unv-prp-is-equiv = (λ t → p₁ ∘ t , p₂ ∘ t) , refl , refl ,
                       (λ w → refl (refl (f w)))
    where f = ×-unv-prp {X = X} {Y} {Z}

  →-comm-× : (Z → X × Y) ≃ (Z → X) × (Z → Y)
  →-comm-× = !e (×-unv-prp {X = X} {Y} {Z} , ×-unv-prp-is-equiv)


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₃} {Z : Type ℓ₂} where

  Σ-unv-prp-is-equiv : is-equiv (Σ-unv-prp {X = X} {P} {Z})
  Σ-unv-prp-is-equiv = (λ t → p₁ ∘ t , p₂ ∘ t) , refl , refl ,
                       (λ w → refl (refl (f w)))
    where f = Σ-unv-prp {X = X} {P} {Z}

  →-comm-Σ : (Z → Σ X P) ≃ Σ (Z → X) (λ f → (y : Z) → P (f y))
  →-comm-Σ = !e (Σ-unv-prp {X = X} {P} {Z} , Σ-unv-prp-is-equiv)


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂}
         {Q : (x : X) → P x → Type ℓ₃} where

  Σ-unv-prp'-is-equiv : is-equiv (Σ-unv-prp' {X = X} {P} {Q})
  Σ-unv-prp'-is-equiv = (λ t → p₁ ∘ t , p₂ ∘ t) , refl , refl ,
                        (λ w → refl (refl (f w)))
    where f = Σ-unv-prp' {X = X} {P} {Q}

  →-comm-Σ' : ((x : X) → Σ (P x) (Q x))
               ≃ Σ ((x : X) → P x) (λ f → (x : X) → Q x (f x))
  →-comm-Σ' = !e (Σ-unv-prp' {X = X} {P} {Q} , Σ-unv-prp'-is-equiv)


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂}
         {Q : (x : X) → P x → Type ℓ₃} where

  Σ-assoc : Σ X (λ x → Σ (P x) (Q x)) ≃ Σ (Σ X P) (λ w → Q (p₁ w) (p₂ w))
  Σ-assoc = f , g , refl , refl , (λ w → refl (refl (f w)))
    where f : Σ X (λ x → Σ (P x) (Q x)) → Σ (Σ X P) (λ w → Q (p₁ w) (p₂ w))
          f (x , y , z) = (x , y) , z
          g : Σ (Σ X P) (λ w → Q (p₁ w) (p₂ w)) → Σ X (λ x → Σ (P x) (Q x))
          g ((x , y) , z) = x , y , z


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {X : Type ℓ₁}
         {P : X → Type ℓ₂} {Q : (x : X) → P x → Type ℓ₃}
         {R : (x : X) → (y : P x) → (z : Q x y) → Type ℓ₄} where

  Σ-assoc₄ : Σ X (λ x → Σ (P x) (λ y → Σ (Q x y) (λ z → R x y z)))
             ≃ Σ (Σ X P) (λ w → Σ (Q (p₁ w) (p₂ w)) (λ z → R (p₁ w) (p₂ w) z))
  Σ-assoc₄ = f , g , refl , refl , (λ w → refl (refl (f w)))
    where f : Σ X (λ x → Σ (P x) (λ y → Σ (Q x y) (λ z → R x y z)))
              → Σ (Σ X P) (λ w → Σ (Q (p₁ w) (p₂ w)) (λ z → R (p₁ w) (p₂ w) z))
          f (w , x , y , z) = (w , x) , (y , z)
          g : Σ (Σ X P) (λ w → Σ (Q (p₁ w) (p₂ w)) (λ z → R (p₁ w) (p₂ w) z))
              → Σ X (λ x → Σ (P x) (λ y → Σ (Q x y) (λ z → R x y z))) 
          g ((w , x) , (y , z)) = w , x , y , z




module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  Σ-fib-eqv : {P Q : X → Type ℓ₂} → ((x : X) → P x ≃ Q x) → Σ X P ≃ Σ X Q
  Σ-fib-eqv h = f , g , η , ε , τ
    where f' = λ x → p₁ (h x)
          g' = λ x → p₁ (p₂ (h x))
          η' = λ x → p₁ (p₂ (p₂ (h x)))
          ε' = λ x → p₁ (p₂ (p₂ (p₂ (h x))))
          τ' = λ x → p₂ (p₂ (p₂ (p₂ (h x))))
          f = dpair→ (id , f')
          g = dpair→ (id , g')
          η : g ∘ f ∼ id
          η (x , ux) = dpair= (refl x , η' x ux)
          ε : f ∘ g ∼ id
          ε (x , ux) = dpair= (refl x , ε' x ux)
          τ : ap f ∘ η ∼ ε ∘ f
          τ (x , ux) = ap-dpair' f' (refl x) (η' x ux)
                       ◾ ap dpair= (dpair= (refl (refl x) , ◾unitl _ ◾ τ' x ux))
