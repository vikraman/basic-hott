{-# OPTIONS --without-K #-}
module VariousEquivalences where


open import Type
open import Functions
open import DependentSum
open import Coproduct
open import Paths
open import Homotopies
open import Equivalences
open import Zero
open import One
open import Two
open import PathsInSigma
open import PathsInOne
open import PathsInCoproduct
open import OneTypes
open import nTypes


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

module _ where

  𝟙+𝟙≃𝟚 : 𝟙 + 𝟙 ≃ 𝟚
  𝟙+𝟙≃𝟚 = f , g , η , ε , τ
    where f : 𝟙 + 𝟙 → 𝟚
          f (i₁ x) = 0₂
          f (i₂ y) = 1₂
          g : 𝟚 → 𝟙 + 𝟙
          g 0₂ = i₁ 0₁
          g 1₂ = i₂ 0₁
          η : g ∘ f ∼ id
          η (i₁ 0₁) = refl (i₁ 0₁)
          η (i₂ 0₁) = refl (i₂ 0₁)
          ε : f ∘ g ∼ id
          ε 0₂ = refl 0₂
          ε 1₂ = refl 1₂
          τ : ap f ∘ η ∼ ε ∘ f
          τ (i₁ 0₁) = refl (refl 0₂)
          τ (i₂ 0₁) = refl (refl 1₂)

  0₂≠1₂ : 0₂ ≠ 1₂
  0₂≠1₂ p = ¬𝟘' (i₁=-e (ap (p₁ (p₂ 𝟙+𝟙≃𝟚)) p))

not-is-equiv : is-equiv not
not-is-equiv = not , η , η , τ
  where η : not ∘ not ∼ id
        η 0₂ = refl 0₂
        η 1₂ = refl 1₂
        τ : ap not ∘ η ∼ η ∘ not
        τ 0₂ = refl (refl 1₂)
        τ 1₂ = refl (refl 0₂)

not-eqv : 𝟚 ≃ 𝟚
not-eqv = (not , not-is-equiv)


module _ {ℓ : Level} {X : Type ℓ} where

  inhab-prop≃𝟙 : (x : X) → is-prop X → X ≃ 𝟙
  inhab-prop≃𝟙 x φ = f , g , η , ε , τ
    where f = λ z → 0₁
          g = λ z → x
          η = φ x
          ε = λ z → 𝟙-has-one-elem _ _
          τ = λ z → contr-is-set 𝟙-is-contr _ _ _ _


module _ {ℓ : Level} {X Y : Type ℓ} where

  coprod≃Σ𝟚 : X + Y ≃ Σ 𝟚 (rec𝟚 (Type ℓ) X Y)
  coprod≃Σ𝟚 = f , g , η , ε , τ
    where f : X + Y → Σ 𝟚 (rec𝟚 (Type ℓ) X Y)
          f (i₁ x) = 0₂ , x
          f (i₂ y) = 1₂ , y
          g : Σ 𝟚 (rec𝟚 (Type ℓ) X Y) → X + Y
          g (0₂ , x) = i₁ x
          g (1₂ , y) = i₂ y
          η : g ∘ f ∼ id
          η (i₁ x) = refl (i₁ x)
          η (i₂ y) = refl (i₂ y)
          ε : f ∘ g ∼ id
          ε (0₂ , x) = refl (0₂ , x)
          ε (1₂ , y) = refl (1₂ , y)
          τ : ap f ∘ η ∼ ε ∘ f
          τ (i₁ x) = refl (refl (0₂ , x))
          τ (i₂ y) = refl (refl (1₂ , y))
