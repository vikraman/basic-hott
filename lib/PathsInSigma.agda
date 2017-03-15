{-# OPTIONS --without-K #-}
module PathsInSigma where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies
open import Equivalences


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  -- introduction for paths of pairs
  pair= : {x x' : X} → {y y' : Y} → (x == x') × (y == y') → (x , y) == (x' , y')
  pair= (refl x , refl y) = refl (x , y)

  -- elimination for paths of pairs
  pair=-e₁ : {x x' : X} → {y y' : Y} → (x , y) == (x' , y') → x == x'
  pair=-e₁ = ap p₁
  
  pair=-e₂ : {x x' : X} → {y y' : Y} → (x , y) == (x' , y') → y == y'
  pair=-e₂ = ap p₂

  pair=-e : {x x' : X} → {y y' : Y} → (x , y) == (x' , y') → (x == x') × (y == y')
  pair=-e = ×-unv-prp (pair=-e₁ , pair=-e₂)

module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {Y : Type ℓ₂} where

  -- computation for paths of pairs
  pair=-β₁ : {x x' : X} → {y y' : Y}
         → (w : (x == x') × (y == y')) → (pair=-e₁ ∘ pair=) w == p₁ w
  pair=-β₁ (refl x , refl y) = refl (refl x)

  pair=-β₂ : {x x' : X} → {y y' : Y}
             → (w : (x == x') × (y == y')) → (pair=-e₂ ∘ pair=) w == p₂ w
  pair=-β₂ (refl x , refl y) = refl (refl y)

  pair=-β : {x x' : X} → {y y' : Y}
            → (w : (x == x') × (y == y')) → (pair=-e ∘ pair=) w == w
  pair=-β (p , q) = pair= (pair=-β₁ (p , q) , pair=-β₂ (p , q))

  -- uniqueness for paths of pairs
  pair=-η : {x x' : X} → {y y' : Y}
           → (p : (x , y) == (x' , y')) → (pair= ∘ pair=-e) p == p
  pair=-η (refl (x , y)) = refl (refl (x , y))


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
         {X : Type ℓ₁} {Y : Type ℓ₂} {X' : Type ℓ₃} {Y' : Type ℓ₄} where

  pair=ap : (f : X → Y) → (f' : X' → Y')
            → {x y : X} → (p : x == y) → {x' y' : X'} → (p' : x' == y')
            → ap (pair→ (f , f')) (pair= (p , p')) == pair= (ap f p , ap f' p')
  pair=ap f f' (refl x) (refl x') = refl (refl (f x , f' x'))


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  dpaths : (P : X → Type ℓ₂)
           → {x y : X} → (ux : P x) → (uy : P y) → Type (ℓ₁ ⊔ ℓ₂)
  dpaths P {x} {y} ux uy = Σ (x == y) (λ p → tpt P p ux == uy)


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  -- introduction for paths of dependent pairs
  dpair= : {x y : X} → {ux : P x} → {uy : P y}
           → dpaths P ux uy → (x , ux) == (y , uy)
  dpair= (refl x , refl ux) = refl (x , ux)

  -- elimination for paths of dependent pairs
  dpair=-e₁ : {x y : X} → {ux : P x} → {uy : P y} → (x , ux) == (y , uy) → x == y
  dpair=-e₁ = ap p₁

  dpair=-e₂ : {x y : X} → {ux : P x} → {uy : P y}
            → (p : (x , ux) == (y , uy)) → tpt P (dpair=-e₁ p) ux == uy
  dpair=-e₂ (refl (x , ux)) = refl ux

  dpair=-e : {x y : X} → {ux : P x} → {uy : P y}
             → (p : (x , ux) == (y , uy)) → dpaths P ux uy
  dpair=-e = Σ-unv-prp (dpair=-e₁ , dpair=-e₂)

module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  -- computation for paths of dependent pairs
  dpair=-β₁ : {x y : X} → {ux : P x} → {uy : P y}
          → (w : dpaths P ux uy) → (dpair=-e₁ ∘ dpair=) w == p₁ w
  dpair=-β₁ (refl x , refl y) = refl (refl x)

  dpair=-β₂ : {x y : X} → {ux : P x} → {uy : P y} → (w : dpaths P ux uy)
          → tpt (λ p → tpt P p ux == uy) (dpair=-β₁ w) (dpair=-e₂ (dpair= w)) == p₂ w
  dpair=-β₂ (refl x , refl y) = refl (refl y)

  dpair=-β : {x y : X} → {ux : P x} → {uy : P y}
                 → (w : dpaths P ux uy) → (dpair=-e ∘ dpair=) w == w
  dpair=-β w = dpair= (dpair=-β₁ w , dpair=-β₂ w)

  -- uniqueness principle for paths of dependent pairs
  dpair=-η : {x y : X} → {ux : P x} → {uy : P y}
            → (p : (x , ux) == (y , uy)) → (dpair= ∘ dpair=-e) p == p
  dpair=-η (refl (x , ux)) = refl (refl (x , ux))


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁} where

  paths-in-Σ : (P : X → Type ℓ₂) →
               {x x' : X} → (y : P x) → (y' : P x')
               → ((x , y) == (x' , y')) ≃ dpaths P y y'  
  paths-in-Σ P y y' = dpair=-e , dpair= , dpair=-η , dpair=-β , τ
    where τ : {x y : X} → {ux : P x} → {uy : P y}
              → (p : (x , ux) == (y , uy)) → (ap dpair=-e ∘ dpair=-η) p == (dpair=-β ∘ dpair=-e) p
          τ (refl (x , ux)) = refl (refl (refl x , refl ux))


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Type ℓ₁} {P : X → Type ℓ₂} {Q : X → Type ℓ₃} where

  ap-dpair' : (f : ((x : X) → P x → Q x)) → {x y : X} → (p : x == y)
              → {ux : P x} → {uy : P y} → (up : tpt P p ux == uy)
              → ap (dpair→ (id , f)) (dpair= (p , up)) == dpair= (p , tpt-fib-map f p ux ◾ ap (f y) up)
  ap-dpair' f (refl x) (refl ux) = refl (refl (x , f x ux))
