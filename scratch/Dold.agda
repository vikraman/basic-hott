{-# OPTIONS --without-K #-}
module scratch.Dold where

open import IntensionalTypeTheory


module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}
         {P : X → Type ℓ₂} {Q : X → Type ℓ₂} where

  nt-tpt-com : (f : (x : X) → P x → Q x)
               → {x y : X} → (p : x == y)
               → f y ∘ tpt P p == tpt Q p ∘ f x
  nt-tpt-com f (refl x) = refl (f x)

  lem : ((x : X) → P x → Q x) → Σ X P → Σ X Q
  lem f (x , y) = x , f x y

  lem2 : (f : (x : X) → P x → Q x)
         → {v w : Σ X P} → (p : v == w)
         → dpair=-e₁ (ap (lem f) p) == dpair=-e₁ p
  lem2 f {(x , y)} = ind=l (λ p → dpair=-e₁ (ap (lem f) p) == dpair=-e₁ p) (refl (refl x))
  
module _ {ℓ₁ ℓ₂ : Level} {X : Type ℓ₁}
         {P : X → Type ℓ₂} {Q : X → Type ℓ₂} where

  -- indent to here

  thm : (f : (x : X) → P x → Q x) → (is-equiv (lem f)) → (x : X) → P x ≃ Q x
  thm f (g , η , ε , τ) x = fx , qinv-is-equiv (gx , ηx , εx)
    where fx : P x → Q x
          fx y = f x y
          
          x' : (y : Q x) → X
          x' y = p₁ (g (x , y))
          y' : (y : Q x) → P (x' y)
          y' y = p₂ (g (x , y))
          p : (y : Q x) → x' y == x
          p y = dpair=-e₁ (ε (x , y))

          gx : Q x → P x
          gx y = tpt P (p y) (y' y)
          
          ηx : gx ∘ fx ∼ id
          ηx y = ap (λ p → tpt P (dpair=-e₁ p) (p₂ (g (x , fx y)))) (! (τ (x , y)))
                 ◾ ap (λ p → tpt P p (p₂ (g (x , fx y)))) foo
                 ◾ uη
            where uη = dpair=-e₂ (η (x , y))
                  foo : dpair=-e₁ (((ap (lem f)) ∘ η) (x , y)) == dpair=-e₁ (η (x , y))
                  foo = lem2 f (η (x , y))

          εx : fx ∘ gx ∼ id
          εx y = happly (nt-tpt-com f (p y)) (y' y) ◾ uε
            where uε = dpair=-e₂ (ε (x , y))
