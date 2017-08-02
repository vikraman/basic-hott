{-# OPTIONS --without-K #-}
module OneTypes where

open import Type
open import Functions
open import DependentSum
open import Coproduct
open import Paths
open import Homotopies
open import Equivalences
open import Zero
open import One
open import PathsInOne
open import PathsInSigma
open import PathsInCoproduct


module _ {ℓ} where

  is-contr : Type ℓ → Type ℓ
  is-contr X = Σ X (λ x → (y : X) → (x == y))

  is-prop : Type ℓ → Type ℓ
  is-prop X = (x y : X) → x == y
  
  is-set : Type ℓ → Type ℓ
  is-set X = (x y : X) → (p q : x == y) → p == q

  is-1type : Type ℓ → Type ℓ
  is-1type X = (x y : X) → (p q : x == y) → (α β : p == q) → α == β


module _ {ℓ} {X : Type ℓ} where

  contr-is-prop : is-contr X → is-prop X
  contr-is-prop (x₀ , φ) x y = ! (φ x) ◾ φ y
  
  prop-is-set : is-prop X → is-set X
  prop-is-set φ x y p q =
    α ◾ ! β
    where α = l₂=!l₁◾r (! (tpt=l x p (φ x x)) ◾ apd _ (φ x) p)
          β = l₂=!l₁◾r (! (tpt=l x q (φ x x)) ◾ apd _ (φ x) q)

  set-is-1type : is-set X → is-1type X
  set-is-1type w x y p q α β =
    A ◾ ! B
    where w' = w x y p
          A = l₂=!l₁◾r (! (tpt=l p α (w' p)) ◾ apd _ w' α)
          B = l₂=!l₁◾r (! (tpt=l p β (w' p)) ◾ apd _ w' β)

  contr-is-set = prop-is-set ∘ contr-is-prop
  contr-is-1type = set-is-1type ∘ contr-is-set
  prop-is-1type = set-is-1type ∘ prop-is-set


module _ where

  prop : (ℓ : Level) → Type (lsuc ℓ)
  prop ℓ = Σ (Type ℓ) is-prop

  prop₀ = prop lzero
  prop₁ = prop (lsuc lzero)

  set : (ℓ : Level) → Type (lsuc ℓ)
  set ℓ = Σ (Type ℓ) is-set

  set₀ = set lzero
  set₁ = set (lsuc lzero)

  1type : (ℓ : Level) → Type (lsuc ℓ)
  1type ℓ = Σ (Type ℓ) is-1type

  1type₀ = 1type lzero
  1type₁ = 1type (lsuc lzero)


---

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop ()

𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = 0₁ , 𝟙-has-one-elem _


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  logical-eqv : is-prop X → is-prop Y → (X → Y) → (Y → X) → X ≃ Y
  logical-eqv φ ψ f g = f , g , h , k , adj
    where h = λ x → φ _ _
          k = λ x → ψ _ _
          adj = λ x → prop-is-set ψ _ _ _ _


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  set-eqv : is-set Y → (f : X → Y) → (g : Y → X)
            → (g ∘ f ∼ id) → (f ∘ g ∼ id) → X ≃ Y
  set-eqv φ f g η ε = f , g , η , ε , (λ x → φ _ _ (ap f (η x)) (ε (f x))) 


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  ×-prsrv-contr : {Y : Type ℓ₂} → is-contr X → is-contr Y → is-contr (X × Y)
  ×-prsrv-contr (x , f) (y , g) = (x , y) , (λ w → pair= (f (p₁ w) , g (p₂ w)))
  
  Σ-prsrv-contr : {P : X → Type ℓ₂}
                  → is-contr X → ((x : X) → is-contr (P x)) → is-contr (Σ X P)
  Σ-prsrv-contr {P} (x , f) g = (x , p₁ (g x)) , φ
    where φ : (w : Σ X P) → x , p₁ (g x) == w
          φ (x' , ux') = dpair= (f x' , ! (p₂ (g x') (tpt P (f x') (p₁ (g x))))
                                        ◾ (p₂ (g x')) ux')

  ×-prsrv-prop : {Y : Type ℓ₂} → is-prop X → is-prop Y → is-prop (X × Y)
  ×-prsrv-prop f g (x , y) (x' , y') = pair= (f x x' , g y y')
  
  Σ-prsrv-prop : {P : X → Type ℓ₂}
                 → is-prop X → ((x : X) → is-prop (P x)) → is-prop (Σ X P)
  Σ-prsrv-prop f g (x , y) (x' , y') = dpair= (f x x' , g _ _ _)

  ×-prsrv-set : {Y : Type ℓ₂} → is-set X → is-set Y → is-set (X × Y)
  ×-prsrv-set f g (x , y) (x' , y') w w' =
    ! (pair=-η w) ◾ ap pair= (pair= (α , β)) ◾ pair=-η w' 
    where p  = ap p₁ w
          q  = ap p₂ w
          p' = ap p₁ w'
          q' = ap p₂ w'
          α  = f x x' p p'
          β  = g y y' q q'

  Σ-prsrv-set : {P : X → Type ℓ₂}
                 → is-set X → ((x : X) → is-set (P x)) → is-set (Σ X P)
  Σ-prsrv-set {P = P} f g (x , y) (x' , y') w w' =
    ! (dpair=-η w) ◾ ap dpair= (dpair= (α , β)) ◾ dpair=-η w'
    where p  = dpair=-e₁ w
          q  = dpair=-e₂ w
          p' = dpair=-e₁ w'
          q' = dpair=-e₂ w'
          α  = f x x' p p'
          β  = g x' (tpt P p' y) y'
                 (tpt (λ p → tpt P p y == y') α q) q'

  +-prsrv-set : {Y : Type ℓ₂} → is-set X → is-set Y → is-set (X + Y)
  +-prsrv-set φ ψ (i₁ x) (i₁ x') p q = ! (i₁=-η p) ◾ ap i₁= (φ _ _ _ _) ◾ i₁=-η q
  +-prsrv-set φ ψ (i₁ x) (i₂ y ) ()
  +-prsrv-set φ ψ (i₂ y) (i₁ x ) ()
  +-prsrv-set φ ψ (i₂ y) (i₂ y') p q = ! (i₂=-η p) ◾ ap i₂= (ψ _ _ _ _) ◾ i₂=-η q

