{-# OPTIONS --without-K #-}
module PathsInSigma where

open import Type
open import Functions
open import DependentSum
open import Paths
open import Homotopies


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
  dpair=-η (refl (x , y)) = refl (refl (x , y))


-- -- -- TODO: Move to exercises
-- -- -- generalization of Thm 2.6.5 to dependent sums
-- -- -- module Thm-2-6-5-Generalized where

-- -- --   lem : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
-- -- --         → {A : Type ℓ₁} → {B : Type ℓ₂} → (f : A → B)
-- -- --         → {A' : A → Type ℓ₃} → {B' : B → Type ℓ₄} → (f' : (u : Σ A A') → B' (f (p₁ u)))
-- -- --         → {v w : Σ A A'} → (p : v == w)
-- -- --         → transport (λ z → B' (f (p₁ z))) p (f' v) == (f' w)
-- -- --         → transport B' (ap f (ap p₁ p)) (f' v) == (f' w)
-- -- --   lem f f' (refl (x , x')) = id


-- -- --   dpair=ap : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
-- -- --          → {A : Type ℓ₁} → {B : Type ℓ₂} → (f : A → B)
-- -- --          → {A' : A → Type ℓ₃} → {B' : B → Type ℓ₄} → (f' : (u : Σ A A') → B' (f (p₁ u)))
-- -- --          → {v w : Σ A A'} → (p : v == w)
-- -- --          → ap (Σ→ {A' = A'} {B'} (f , f')) p == dpair= (ap f (ap p₁ p) , lem f f' p (apd f' p))
-- -- --   dpair=ap f f' (refl (x , x')) = refl (refl (f x , f' (x , x')))

-- -- -- open Thm-2-6-5-Generalized public using (dpair=ap)



-- Σ→* : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
--        → {A : Type ℓ₁} → {A' : Type ℓ₂} → (f : A → A')
--        → {B : A → Type ℓ₃} → {B' : A' → Type ℓ₄} → (g : (x : A) → B x → B' (f x))
--        → Σ A B → Σ A' B'
-- Σ→* f g (x , y) = f x , g x y

-- pair=ap*-com : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
--                → {A : Type ℓ₁} → {A' : Type ℓ₂} → (f : A → A')
--                → {B : A → Type ℓ₃} → {B' : A' → Type ℓ₄} → (g : (x : A) → B x → B' (f x))
--                → {x y : A} → (p : x == y)
--                → {ux : B x} → {uy : B y} → (up : transport B p ux == uy)
--                → transport B' (ap f p) (g x ux) == g y (transport B p ux)
-- pair=ap*-com f g (refl x) (refl ux) = refl (g x ux)

-- pair=ap* : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
--            → {A : Type ℓ₁} → {A' : Type ℓ₂} → (f : A → A')
--            → {B : A → Type ℓ₃} → {B' : A' → Type ℓ₄} → (g : (x : A) → B x → B' (f x))
--            → {x y : A} → (p : x == y)
--            → {ux : B x} → {uy : B y} → (up : transport B p ux == uy)
--            → ap (Σ→* f {B} {B'} g) (dpair= {B = B} (p , up))
--               == dpair= {B = B} (ap f p , pair=ap*-com f g p up ◾ ap (g y) up)
-- pair=ap* f g (refl x) (refl ux) = refl (refl (f x , g x ux))           

-- pair→' : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
--           → {A : Type ℓ₁} → {A' : Type ℓ₂} → (f : A → A')
--           → {B : A → Type ℓ₃} → {B' : A' → Type ℓ₄} → (g : (w : Σ A B) → B' (f (p₁ w)))
--           → Σ A B → Σ A' B'
-- pair→' f g w = f (p₁ w) , g w

-- pair=ap' : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
--            → {A : Type ℓ₁} → {A' : Type ℓ₂} → (f : A → A')
--            → {B : A → Type ℓ₃} → {B' : A' → Type ℓ₄} → (g : (w : Σ A B) → B' (f (p₁ w)))
--            → {v w : Σ A B} → (p : dpaths B (p₂ v) (p₂ w))
--            → ap (pair→' f g) (dpair= {B = B} p)
--               == dpair= {B = B} (ap (f ∘ p₁) (dpair= {B = B} p) , ! (tpt∘ B' (f ∘ p₁) (dpair= p) (g v)) ◾ apd g (dpair= p))
-- pair=ap' f g (refl x , refl ux) = refl (refl (f x , g (x , ux)))

