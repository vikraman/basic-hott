{-# OPTIONS --without-K #-}
module Cubical where

open import UnivalentTypeTheory


----------------------------------------------------------------------
--                      III. Path over a path
----------------------------------------------------------------------

----------------------------------------------------------------------
-- B. Library
----------------------------------------------------------------------

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  data PathOver (P : X → Type ℓ₂) {x : X} :
                {y : X} → (p : x == y)
                → (ux : P x) → (uy : P y) → Type (ℓ₁ ⊔ ℓ₂) where
    reflo : (ux : P x) → PathOver P (refl x) ux ux

  apdo : {P : X → Type ℓ₂} (f : (x : X) → P x)
         {x y : X} → (p : x == y) → PathOver P p (f x) (f y)
  apdo f (refl x) = reflo (f x)

  pair=o : {P : X → Type ℓ₂}
           → {x y : X} → (p : x == y)
           → {ux : P x} → {uy : P y} → PathOver P p ux uy
           → (x , ux) == (y , uy)
  pair=o (refl x) (reflo ux) = refl (x , ux)

  hom-to-over/left-eqv : {P : X → Type ℓ₂}
                         → {x y : X} → (p : x == y)
                         → {ux : P x} → {uy : P y}
                         →(tpt P p ux == uy) ≃ PathOver P p ux uy
  hom-to-over/left-eqv = {!!}

  hom-to-over-eqv : {P : X → Type ℓ₂}
                    → {x : X}
                    → {ux ux' : P x} → (ux == ux') ≃ PathOver P (refl x) ux ux'
  hom-to-over-eqv = {!!}

  PathOver-constant-eqv : {Y : Type ℓ₂} → {x x' : X} → {p : x == x'} → {y y' : Y}
                          → PathOver (λ _ → Y) p y y' ≃ y == y'
  PathOver-constant-eqv = {!!}


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} where

  over-o-ap-eqv : (P : Y → Type ℓ₃) → {f : X → Y}
                  → {x x' : X} → {p : x == x'}
                  → {ux : P (f x)} → {ux' : P (f x')}
                  → PathOver (P ∘ f) p ux ux' ≃ PathOver P (ap f p) ux ux'
  
  over-o-ap-eqv = {!!}

  -- PathOverΠ-eqv


----------------------------------------------------------------------
-- C. Example: Circle Elimination
----------------------------------------------------------------------


----------------------------------------------------------------------
--                           IV. Squares
----------------------------------------------------------------------

----------------------------------------------------------------------
-- A. Definition
----------------------------------------------------------------------

module _ {ℓ} {X : Type ℓ} where

  data Square {x00 : X} : {x01 x10 x11 : X}
                          → x00 == x01 → x00 == x10
                          → x01 == x11 → x10 == x11 → Type ℓ where
       reflsq : Square (refl x00) (refl x00) (refl x00) (refl x00)


----------------------------------------------------------------------
-- B. Library
----------------------------------------------------------------------

module _ {ℓ} {X : Type ℓ} where

  square-disc-eqv : {x00 x01 x10 x11 : X}
                    → (l : x00 == x01) → (t : x00 == x10)
                    → (b : x01 == x11) → (r : x10 == x11)
                    → Square l t b r ≃ (l ◾ b) == (t ◾ r)
  square-disc-eqv = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  PathOver-=-eqv : {f g : X → Y} → {x x' : X} → {p : x == x'}
                   → {ux : f x == g x} → {ux' : f x' == g x'}
                   → PathOver (paths f g) p ux ux' ≃ Square ux (ap f p) (ap g p) ux'
  PathOver-=-eqv = {!!}


module _ {ℓ} {X : Type ℓ} where

  hrefl-square : {x y : X} → (p : x == y) → Square p (refl x) (refl y) p
  hrefl-square = {!!}

  vrefl-square : {x y : X} → (p : x == y) → Square (refl x) p p (refl y)
  vrefl-square = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-square : (f : X → Y) → {x00 x01 x10 x11 : X}
              → (l : x00 == x01) → (t : x00 == x10)
              → (b : x01 == x11) → (r : x10 == x11)
              → Square l t b r → Square (ap f l) (ap f t) (ap f b) (ap f r)
  ap-square = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  pair-line : {x x' : X} → (p : x == x')
              → {y y' : Y} → (q : y == y')
              → (x , y) == (x' , y')
  pair-line p q = pair= (p , q)

  pair-square : {x00 x01 x10 x11 : X}
                → {lx : x00 == x01} → {tx : x00 == x10}
                → {bx : x01 == x11} → {rx : x10 == x11}
                → Square lx tx bx rx
                → {y00 y01 y10 y11 : Y}
                → {ly : y00 == y01} → {ty : y00 == y10}
                → {by : y01 == y11} → {ry : y10 == y11}
                → Square ly ty by ry
                → Square (pair-line lx ly) (pair-line tx ty) (pair-line bx by) (pair-line rx ry)
  pair-square = {!!}


module _ {ℓ} {X : Type ℓ} where

  whisker-square : {x00 x01 x10 x11 : X}
                   → {l l' : x00 == x01} → {t t' : x00 == x10}
                   → {b b' : x01 == x11} → {r r' : x10 == x11}
                   → Square l t b r
                   → l == l' → t == t' → b == b' → r == r'
                   → Square l' t' b' r'
  whisker-square = {!!}


module _ {ℓ} {X : Type ℓ} where

  _◾-square-v_ : {x00 x01 x02 x10 x11 x12 : X}
                 → {l : x00 == x01} → {l' : x01 == x02}
                 → {t : x00 == x10}
                 → {b : x01 == x11} → {b' : x02 == x12}
                 → {r : x10 == x11} → {r' : x11 == x12}
                 → Square l t b r
                 → Square l' b b' r'
                 → Square (l ◾ l') t b' (r ◾ r')
  _◾-square-v_ = {!!}

  _◾-square-h_ : {x00 x01 x10 x11 x20 x21 : X}
                 → {l : x00 == x01}
                 → {t : x00 == x10} → {t' : x10 == x20}
                 → {b : x01 == x11} → {b' : x11 == x21}
                 → {r : x10 == x11} → {r' : x20 == x21}
                 → Square l t b r
                 → Square r t' b' r'
                 → Square l (t ◾ t') (b ◾ b') r'
  _◾-square-h_ = {!!}


module _ {ℓ} {X : Type ℓ} where

  square-symmetry-eqv : {x00 x01 x10 x11 : X}
                        → {l : x00 == x01} → {t : x00 == x10}
                        → {b : x01 == x11} → {r : x10 == x11}
                        → Square l t b r ≃ Square t l r b
  square-symmetry-eqv = {!!}
  
  fill-square-right : {x00 x01 x10 x11 : X}
                      → {l : x00 == x01} → {t : x00 == x10}
                      → {b : x01 == x11}
                      → Σ (x10 == x11) (λ r → Square l t b r)
  fill-square-right = {!!}


----------------------------------------------------------------------
-- D. Square over a square
----------------------------------------------------------------------

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  data SquareOver (P : X → Type ℓ₂) {x00 : X} {ux00 : P x00} :
                  {x01 x10 x11 : X}
                  → {l : x00 == x01} → {t : x00 == x10}
                  → {b : x01 == x11} → {r : x10 == x11}
                  → Square l t b r
                  → {ux01 : P x01} → {ux10 : P x10} → {ux11 : P x11}
                  → (ul : PathOver P l ux00 ux01)
                  → (ut : PathOver P t ux00 ux10)
                  → (ub : PathOver P b ux01 ux11)
                  → (ur : PathOver P r ux10 ux11)
                  → Type (ℓ₁ ⊔ ℓ₂) where
       reflsqo : SquareOver P reflsq (reflo ux00) (reflo ux00)
                                     (reflo ux00) (reflo ux00)


----------------------------------------------------------------------
--                             V. Cubes
----------------------------------------------------------------------

-- module _ {ℓ} {X : Type ℓ} where

--   data Cube {x000 : X} : {x010 x100 x110 x001 x011 x101 x111 : X}
--                          → {p0-0 : x000 == x010}
