{-# OPTIONS --without-K #-}
module IsEquivIsProp where

open import IntensionalTypeTheory
open import FunctionExtensionality
open import OneTypesFunExt
open import VariousEquivalencesFunExt


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} (f : X → Y) where

  post∘-prsrv-qinv : is-qinv f → is-qinv {X = (Y → X)} (λ g → g ∘ f)
  post∘-prsrv-qinv (g , η , ε) = (λ h → h ∘ g) ,
                                 (λ h → funext (ap h ∘ ε)) ,
                                 (λ h → funext (ap h ∘ η))

  pre∘-prsrv-qinv : is-qinv f → is-qinv {X = (Y → X)} (λ g → f ∘ g)
  pre∘-prsrv-qinv (g , η , ε) = (λ h → g ∘ h) ,
                                (λ h → funext (η ∘ h)) ,
                                (λ h → funext (ε ∘ h))


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  rinv : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  rinv = is-retraction

  rinv' : (X → Y) → Type (ℓ₁ ⊔ ℓ₂)
  rinv' f = Σ (Y → X) (λ g → f ∘ g == id)

  rinv≃rinv' : (f : X → Y) → rinv f ≃ rinv' f
  rinv≃rinv' f = Σ-fib-eqv (λ g → !e (happly , (happly-is-equiv (f ∘ g) id)))

  qinv-rinv'-is-contr : (f : X → Y) → is-qinv f → is-contr (rinv' f)
  qinv-rinv'-is-contr f e = qinv-fib-is-contr (pre∘-prsrv-qinv f e) _

  qinv-rinv-is-contr : (f : X → Y) → is-qinv f → is-contr (rinv f)
  qinv-rinv-is-contr f = retract-prsrv-contr (equiv-is-retract (!e (rinv≃rinv' f)))
                         ∘ qinv-rinv'-is-contr f


module ContrFnIsHae {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  rcoh : (f : X → Y) → rinv f → Type (ℓ₁ ⊔ ℓ₂)
  rcoh f (g , ε) = Σ (g ∘ f ∼ id) (λ η → ap f ∘ η ∼ ε ∘ f)

  rcoh₁ : (f : X → Y) → rinv f → Type (ℓ₁ ⊔ ℓ₂)
  rcoh₁ f (g , ε) = (x : X) → Σ (g (f x) == x) (λ p → ap f p == ε (f x))

  rcoh₂ : (f : X → Y) → rinv f → Type (ℓ₁ ⊔ ℓ₂)
  rcoh₂ f (g , ε) = (x : X) → dpaths (paths-r f (f x)) (ε (f x)) (refl (f x))
  
  rcoh₃ : (f : X → Y) → rinv f → Type (ℓ₁ ⊔ ℓ₂)
  rcoh₃ f (g , ε) = (x : X) → ==' (fib f (f x)) (g (f x) , ε (f x)) (x , refl (f x))

  rcoh≃rcoh₁ : (f : X → Y) → (w : rinv f) → rcoh f w ≃ rcoh₁ f w
  rcoh≃rcoh₁ f w = !e →-comm-Σ'

  rcoh₁≃rcoh₂ : (f : X → Y) → (w : rinv f) → rcoh₁ f w ≃ rcoh₂ f w
  rcoh₁≃rcoh₂ f (g , ε) = Π-fib-eqv (λ x → Σ-fib-eqv (λ p → e₁ x p ● e₂ x p))
    where e₁ = λ x p → !-anticomm-tpt p (ε (f x)) (refl (f x))
          e₂ = λ x p → path-to-eqv (=-prsrv-= (ap (ap f) (! (!! p))
                                                ◾ ap! f _
                                                ◾ ! (◾unitr _)
                                                ◾ ! (tpt-paths-r _ _ _))
                                               (refl _))

  rcoh₂≃rcoh₃ : (f : X → Y) → (w : rinv f) → rcoh₂ f w ≃ rcoh₃ f w
  rcoh₂≃rcoh₃ f w = Π-fib-eqv (λ x → !e (paths-in-Σ _ _ _))

  rcoh≃rcoh₃ : (f : X → Y) → (w : rinv f) → rcoh f w ≃ rcoh₃ f w
  rcoh≃rcoh₃ f w = rcoh₂≃rcoh₃ f w ● rcoh₁≃rcoh₂ f w ● rcoh≃rcoh₁ f w

  hae-rcoh-is-contr : (f : X → Y) → is-hae f → (w : rinv f) → is-contr (rcoh f w)
  hae-rcoh-is-contr f e w = (retract-prsrv-contr (equiv-is-retract (!e (rcoh≃rcoh₃ f w)))
                                                  ∘ (λ v → φ)) w
    where σ : (x : X) → is-contr (fib f (f x))
          σ x = hae-is-contr e (f x)
          φ = Π-prsrv-contr (Σ-unv-prp' ((λ x → contr-is-prop (σ x) _ _) ,
                                         (λ x → contr-is-set (σ x) _ _ _)))

  contr-is-hae : {f : X → Y} → is-contr-fn f → is-hae f
  contr-is-hae {f} e = g , η , ε , τ
    where g : Y → X
          g y = p₁ (p₁ (e y))
          ε : f ∘ g ∼ id
          ε y = p₂ (p₁ (e y))
          η : g ∘ f ∼ id
          η x = p₁ (p₁ (p₂ (rcoh≃rcoh₃ f (g , ε))) (λ x → p₂ (e (f x)) (x , (refl (f x))))) x
          τ : ap f ∘ η ∼ ε ∘ f
          τ x = p₂ (p₁ (p₂ (rcoh≃rcoh₃ f (g , ε))) (λ x → p₂ (e (f x)) (x , (refl (f x))))) x

open ContrFnIsHae public using (rcoh ; hae-rcoh-is-contr ; contr-is-hae)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  -- Could also be proved with associative and commutative laws
  Σ-rinv-rcoh≃is-hae : (f : X → Y) → Σ (rinv f) (rcoh f) ≃ is-hae f
  Σ-rinv-rcoh≃is-hae f = f' , g' , refl , refl , (λ w → refl (refl (f' w)))
    where f' : Σ (rinv f) (rcoh f) → is-hae f
          f' ((g , ε) , (η , τ)) = g , η , ε , τ
          g' : is-hae f → Σ (rinv f) (rcoh f)
          g' (g , η , ε , τ) = (g , ε) , (η , τ)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  is-hae-is-contr : {f : X → Y} → is-hae f → is-contr (is-hae f)
  is-hae-is-contr {f} e = retract-prsrv-contr (equiv-is-retract (Σ-rinv-rcoh≃is-hae f)) φ
    where  φ : is-contr (Σ (rinv f) (rcoh f))
           φ = Σ-prsrv-contr (qinv-rinv-is-contr f (hae-is-qinv e))
                             (hae-rcoh-is-contr f e)
  
  is-hae-is-prop : (f : X → Y) → is-prop (is-hae f)
  is-hae-is-prop f e e' = ! (φ e) ◾ φ e'
    where φ = p₂ (is-hae-is-contr e)

  is-hae≃is-contr-fn : (f : X → Y) → is-hae f ≃ is-contr-fn f
  is-hae≃is-contr-fn f = logical-eqv (is-hae-is-prop f) (is-contr-fn-is-prop f) hae-is-contr contr-is-hae

  is-equiv-is-prop : (f : X → Y) → is-prop (is-equiv f)
  is-equiv-is-prop = is-hae-is-prop

  eqv= : {e e' : X ≃ Y} → p₁ e == p₁ e' → e == e'
  eqv= {e = e} {e'} φ = dpair= (φ , is-equiv-is-prop _ _ _ )
