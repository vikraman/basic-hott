{-# OPTIONS --without-K #-}
module Equivalences where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-qinv : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-qinv f = Σ (Y → X) λ g → (g ∘ f ∼ id) × (f ∘ g ∼ id)


id-is-qinv : {ℓ : Level} → (X : Type ℓ) → is-qinv id
id-is-qinv X = id {X = X} , idh id , idh id


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-biinv : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-biinv f = (Σ (Y → X) λ g → g ∘ f ∼ id) ×
               (Σ (Y → X) λ h → f ∘ h ∼ id)

  biinv-is-qinv : {f : X → Y} → is-biinv f → is-qinv f
  biinv-is-qinv {f = f} ((g , η) , (h , ε)) = (g' , η' , ε')
    where g' = g ∘ f ∘ h

          η' : g' ∘ f ∼ id
          η' x = ap g (ε (f x)) ◾ η x

          ε' : f ∘ g' ∼ id
          ε' y = ap f (η (h y)) ◾ ε y

  qinv-is-biinv : {f : X → Y} → is-qinv f → is-biinv f
  qinv-is-biinv (g , η , ε) = (g , η) , (g , ε)



module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-hae : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-hae f = Σ (Y → X) λ g →
             Σ (g ∘ f ∼ id) λ η →
             Σ (f ∘ g ∼ id) λ ε →
               ap f ∘ η ∼ ε ∘ f
               
  hae-τ-to-ν : (f : X → Y) → (g : Y → X)
               → (η : g ∘ f ∼ id) → (ε : f ∘ g ∼ id)
               → (τ : ap f ∘ η ∼ ε ∘ f) → η ∘ g ∼ ap g ∘ ε
  hae-τ-to-ν f g η ε τ y = nat-η-ηg ◾ (!ηgfg [1,0,2] (gτg ◾ ε-fg-comm) [2,0,1] ηg) ◾ nat-η-gε
    where gτg = ap∘ _ _ _ ◾ ap (ap g) (τ (g y))
          ε-fg-comm = ap (ap g) (htpy-id-comm (f ∘ g) ε y) ◾ ! (ap∘ _ _ _) 
          !ηgfg = ! (η (g (f (g y))))
          ηg = η (g y)
          nat-η-ηg = ! (ap-id _) ◾ l₂=!l₁◾r (nat η ηg)
          nat-η-gε = (! (η (g (f (g y)))) [1,0,2] (ap∘ (g ∘ f) g (ε y)) [2,0,1] ηg)
                     ◾ ! (l₂=!l₁◾r (nat-id η (ap g (ε y))))

                     

  module _ (f : X → Y) (e : is-qinv f) where
    private
      g = p₁ e
      η = p₁ (p₂ e)
      ε = p₂ (p₂ e)

    qinv-is-hae-ε : f ∘ g ∼ id
    qinv-is-hae-ε y = ! (ε (f (g y))) ◾ ap f (η (g y)) ◾ ε y

    qinv-is-hae-τ : ap f ∘ η ∼ qinv-is-hae-ε ∘ f
    qinv-is-hae-τ x = nat-ε-fη
                      ◾ ! (ε (f (g (f x)))) [1,0,2] η-gf-comm [2,0,1] ε (f x)
      where nat-ε-fη  = l₂=!l₁◾r (nat-id ε (ap f (η x)))
            η-gf-comm = ap∘ _ _ _
                        ◾ ap (ap f) (! (htpy-id-comm (g ∘ f) η x ◾ ap∘ _ _ _))
            
  qinv-is-hae : {f : X → Y} → is-qinv f → is-hae f
  qinv-is-hae {f = f} (g , η , ε) = g , η , ε' , τ
    where ε' = qinv-is-hae-ε f (g , η , ε)
          τ  = qinv-is-hae-τ f (g , η , ε)

  hae-is-qinv : {f : X → Y} → is-hae f → is-qinv f
  hae-is-qinv (g , η , ε , τ) = g , η , ε


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where
                        
  hae-ν-to-τ : (f : X → Y) → (g : Y → X)
               → (η : g ∘ f ∼ id) → (ε : f ∘ g ∼ id)
               → (ν : η ∘ g ∼ ap g ∘ ε) → ap f ∘ η ∼ ε ∘ f
  hae-ν-to-τ f g η ε ν = !h (hae-τ-to-ν g f ε η (!h ν))


qinv-is-equiv = qinv-is-hae
is-equiv = is-hae


infixr 30 _≃_
_≃_ : {ℓ₁ ℓ₂ : Level} → (X : Type ℓ₁) → (Y : Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
X ≃ Y = Σ (X → Y) λ f → is-equiv f

ide : {ℓ : Level} → (A : Type ℓ) → A ≃ A
ide A = id , id , idh id , idh id , idh (idh id)

infix 100 !e
!e : {ℓ₁ ℓ₂ : Level} → {X : Type ℓ₁} → {Y : Type ℓ₂} → X ≃ Y → Y ≃ X
!e (f , g , η , ε , τ) = g , f , ε , η , !h (hae-τ-to-ν f g η ε τ)

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} where

  infixr 80 _●_
  _●_ : Y ≃ Z → X ≃ Y → X ≃ Z
  (f , g , η , ε , τ) ● (f' , g' , η' , ε' , τ') = (f● , g● , η● , ε● , τ●)
    where f● = f ∘ f'
          g● = g' ∘ g
          
          η● : g● ∘ f● ∼ id
          η● x = ap g' (η (f' x)) ◾ η' x
  
          ε● : f● ∘ g● ∼ id
          ε● x = ap f (ε' (g x)) ◾ ε x
  
          τ● : ap f● ∘ η● ∼ ε● ∘ f●
          τ● x = ap◾ f● _ _
                 ◾ (! (ap∘ _ _ _) [2,0,2] ap∘ _ _ _ ◾ ap (ap f) (τ' x))
                 ◾ ! (nat (ap f ∘ ε') (η (f' x)))
                 ◾ (ap f (ε' (g (f (f' x)))) [1,0,2] τ (f' x))


  infix 120 _●-
  _●- : Y ≃ Z → X ≃ Y → X ≃ Z
  e ●- = _●_ e

  infix 100 -●_
  -●_ : X ≃ Y → Y ≃ Z → X ≃ Z
  -● e' = λ e → e ● e'


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  tpt-eqv : (P : X → Type ℓ₂) → {x y : X} → x == y → P x ≃ P y
  tpt-eqv P (refl x) = ide (P x)

  is-univ-fib : (P : X → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
  is-univ-fib P = (x y : X) → is-equiv (tpt-eqv P {x} {y})


module _ {ℓ} {X Y : Type ℓ} where

  tpt-id-is-equiv : {X Y : Type ℓ} → (p : X == Y) → is-equiv (tpt id p)
  tpt-id-is-equiv (refl A) = p₂ (ide A)

  path-to-eqv : X == Y → X ≃ Y
  path-to-eqv p = tpt id p , tpt-id-is-equiv p


module _ {ℓ} where

  path-to-eqv-refl : (X : Type ℓ) → path-to-eqv (refl X) == ide X
  path-to-eqv-refl X = refl (ide X)

  path-to-eqv-◾ : {X Y Z : Type ℓ} → (p : X == Y) → (q : Y == Z)
                  → path-to-eqv (p ◾ q) == path-to-eqv q ● path-to-eqv p
  path-to-eqv-◾ (refl Y) (refl .Y) = refl (ide Y)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-embed : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-embed f = (x y : X) → is-equiv (ap f {x} {y})


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-retraction : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-retraction r = Σ (Y → X) (λ s → r ∘ s ∼ id)

  is-section : (Y → X) → Type (ℓ₁ ⊔ ℓ₂)
  is-section s = Σ (X → Y) (λ r → r ∘ s ∼ id)

  is-split-surj : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  is-split-surj f = (y : Y) → Σ X (paths-r f y)

  -- split-surj-is-retraction
  -- retraction-is-split-surj

module _ {ℓ₁ ℓ₂} where

  is-retract : (Y : Type ℓ₁) → (X : Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
  is-retract Y X = Σ (X → Y) is-retraction


module _ {ℓ₁ ℓ₂} where

  equiv-is-retract : {X : Type ℓ₁} → {Y : Type ℓ₂} → X ≃ Y → is-retract Y X
  equiv-is-retract (f , g , η , ε , τ) = f , g , ε
