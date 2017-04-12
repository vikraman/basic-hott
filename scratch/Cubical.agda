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

  out-PathOver= : {f g : X → Y} → {x x' : X} → {p : x == x'}
                   → {ux : f x == g x} → {ux' : f x' == g x'}
                   → PathOver (paths f g) p ux ux' → Square ux (ap f p) (ap g p) ux'
  out-PathOver= = {!!}
  
  PathOver=-eqv : {f g : X → Y} → {x x' : X} → {p : x == x'}
                   → {ux : f x == g x} → {ux' : f x' == g x'}
                   → PathOver (paths f g) p ux ux' ≃ Square ux (ap f p) (ap g p) ux'
  PathOver=-eqv = out-PathOver= , {!!}


module _ {ℓ} {X : Type ℓ} where

  hrefl-square : {x y : X} → (p : x == y) → Square p (refl x) (refl y) p
  hrefl-square = {!!}

  vrefl-square : {x y : X} → (p : x == y) → Square (refl x) p p (refl y)
  vrefl-square = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-square : (f : X → Y) → {x00 x01 x10 x11 : X}
              → {l : x00 == x01} → {t : x00 == x10}
              → {b : x01 == x11} → {r : x10 == x11}
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

  square-symmetry : {x00 x01 x10 x11 : X}
                    → {l : x00 == x01} → {t : x00 == x10}
                    → {b : x01 == x11} → {r : x10 == x11}
                    → Square l t b r → Square t l r b
  square-symmetry = {!!}


  square-symmetry-eqv : {x00 x01 x10 x11 : X}
                        → {l : x00 == x01} → {t : x00 == x10}
                        → {b : x01 == x11} → {r : x10 == x11}
                        → Square l t b r ≃ Square t l r b
  square-symmetry-eqv = square-symmetry , {!!}
  
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

module _ {ℓ} {X : Type ℓ} where

  data Cube {x000 : X} : {x010 x100 x110 x001 x011 x101 x111 : X}
                         → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                         → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                         → Square p0-0 p-00 p-10 p1-0
                         → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
                         → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
                         → Square p0-1 p-01 p-11 p1-1
                         → {p00- : x000 == x001} → {p01- : x010 == x011}
                         → {p10- : x100 == x101} → {p11- : x110 == x111}
                         → Square p0-0 p00- p01- p0-1
                         → Square p-00 p00- p10- p-01
                         → Square p-10 p01- p11- p-11
                         → Square p1-0 p10- p11- p1-1
                         → Type ℓ where
            reflcube : Cube reflsq reflsq reflsq reflsq reflsq reflsq

  _◾-cube-h_ : {x000 x010 x100 x110 x001 x011 x101 x111 x002 x012 x102 x112 : X}
               → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
               → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
               → {left : Square p0-0 p-00 p-10 p1-0}
               → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
               → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
               → {right : Square p0-1 p-01 p-11 p1-1}
               → {p00- : x000 == x001} → {p01- : x010 == x011}
               → {p10- : x100 == x101} → {p11- : x110 == x111}
               → {back : Square p0-0 p00- p01- p0-1}
               → {top : Square p-00 p00- p10- p-01}
               → {bottom : Square p-10 p01- p11- p-11}
               → {front : Square p1-0 p10- p11- p1-1}
               → {p0-2 : x002 == x012} → {p-02 : x002 == x102}
               → {p-12 : x012 == x112} → {p1-2 : x102 == x112}
               → {right' : Square p0-2 p-02 p-12 p1-2}
               → {p00-' : x001 == x002} → {p01-' : x011 == x012}
               → {p10-' : x101 == x102} → {p11-' : x111 == x112}
               → {back' : Square p0-1 p00-' p01-' p0-2}
               → {top' : Square p-01 p00-' p10-' p-02}
               → {bottom' : Square p-11 p01-' p11-' p-12}
               → {front' : Square p1-1 p10-' p11-' p1-2}
               → Cube left right back top bottom front
               → Cube right right' back' top' bottom' front'
               → Cube left right' (back ◾-square-h back') (top ◾-square-h top')
                      (bottom ◾-square-h bottom') (front ◾-square-h front')
  _◾-cube-h_ = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-cube : (f : X → Y)
            → {x000 x010 x100 x110 x001 x011 x101 x111 : X}
            → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
            → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
            → {left : Square p0-0 p-00 p-10 p1-0}
            → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
            → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
            → {right : Square p0-1 p-01 p-11 p1-1}
            → {p00- : x000 == x001} → {p01- : x010 == x011}
            → {p10- : x100 == x101} → {p11- : x110 == x111}
            → {back : Square p0-0 p00- p01- p0-1}
            → {top : Square p-00 p00- p10- p-01}
            → {bottom : Square p-10 p01- p11- p-11}
            → {front : Square p1-0 p10- p11- p1-1}
            → Cube left right back top bottom front
            → Cube (ap-square f left) (ap-square f right)
                    (ap-square f back) (ap-square f top)
                    (ap-square f bottom) (ap-square f front)
  ap-cube = {!!}


module _ {ℓ} {X : Type ℓ} where

  cube-symmetry-left-to-top : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
            → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
            → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
            → {left : Square p0-0 p-00 p-10 p1-0}
            → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
            → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
            → {right : Square p0-1 p-01 p-11 p1-1}
            → {p00- : x000 == x001} → {p01- : x010 == x011}
            → {p10- : x100 == x101} → {p11- : x110 == x111}
            → {back : Square p0-0 p00- p01- p0-1}
            → {top : Square p-00 p00- p10- p-01}
            → {bottom : Square p-10 p01- p11- p-11}
            → {front : Square p1-0 p10- p11- p1-1}
            → Cube left right back top bottom front
            → Cube (square-symmetry back) (square-symmetry front)
                    (square-symmetry top) left
                    right (square-symmetry bottom)
  cube-symmetry-left-to-top = {!!}


module _ {ℓ} {X : Type ℓ} where

  fill-cube-left : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
                   → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                   → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                   → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
                   → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
                   → (right : Square p0-1 p-01 p-11 p1-1)
                   → {p00- : x000 == x001} → {p01- : x010 == x011}
                   → {p10- : x100 == x101} → {p11- : x110 == x111}
                   → (back : Square p0-0 p00- p01- p0-1)
                   → (top : Square p-00 p00- p10- p-01)
                   → (bottom : Square p-10 p01- p11- p-11)
                   → (front : Square p1-0 p10- p11- p1-1)
                   → Σ (Square p0-0 p-00 p-10 p1-0)
                        (λ left → Cube left right back top bottom front)
  fill-cube-left = {!!}


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  in-SquareOver= : (f g : X → Y)
                   → {x00 x01 x10 x11 : X}
                   → {l : x00 == x01} → {t : x00 == x10}
                   → {b : x01 == x11} → {r : x10 == x11}
                   → (s : Square l t b r)
                   → {ux00 : f x00 == g x00} → {ux01 : f x01 == g x01}
                   → {ux10 : f x10 == g x10} → {ux11 : f x11 == g x11}
                   → (ul : PathOver (paths f g) l ux00 ux01)
                   → (ut : PathOver (paths f g) t ux00 ux10)
                   → (ub : PathOver (paths f g) b ux01 ux11)
                   → (ur : PathOver (paths f g) r ux10 ux11)
                   → Cube (out-PathOver= ul) (out-PathOver= ur)
                           (out-PathOver= ut) (ap-square f s)
                           (ap-square g s) (out-PathOver= ub)
                   → SquareOver (paths f g) s ul ut ub ur
  in-SquareOver= = {!!}


module ThreeByThree where

  module Pushout {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} where

    private
      data #Pushout (f : X → Y) (g : X → Z) : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
        #inl : Y → #Pushout f g
        #inr : Z → #Pushout f g

    Pushout : (f : X → Y) → (g : X → Z) → Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
    Pushout = #Pushout

    inl : {f : X → Y} → {g : X → Z} → Y → Pushout f g
    inl = #inl

    inr : {f : X → Y} → {g : X → Z} → Z → Pushout f g
    inr = #inr

    postulate
      push : {f : X → Y} → {g : X → Z}
             → (x : X) → inl {f} {g} (f x) == inr (g x)

    recPushout : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                 → {C : Type ℓ₄} → (cl : Y → C) → (cr : Z → C)
                 → ((x : X) → cl (f x) == cr (g x))
                 → Pushout f g → C
    recPushout cl cr φ (#inl y) = cl y
    recPushout cl cr φ (#inr z) = cr z

    postulate
      recPushoutβ : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                    → {C : Type ℓ₄} → (cl : Y → C) → (cr : Z → C)
                    → (φ : (x : X) → cl (f x) == cr (g x))
                    → (x : X) → ap (recPushout cl cr φ) (push x) == φ x

    indPushout : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                 → {P : Pushout f g → Type ℓ₄}
                 → (cl : (y : Y) → P (inl y)) → (cr : (z : Z) → P (inr z))
                 → ((x : X) → tpt P (push x) (cl (f x)) == cr (g x))
                 → (w : Pushout f g) → P w
    indPushout cl cr φ (#inl y) = cl y
    indPushout cl cr φ (#inr z) = cr z

    postulate
      indPushoutβ : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                    → {P : Pushout f g → Type ℓ₄}
                    → (cl : (y : Y) → P (inl y)) → (cr : (z : Z) → P (inr z))
                    → (φ : (x : X) → tpt P (push x) (cl (f x)) == cr (g x))
                    → (x : X) → apd P (indPushout cl cr φ) (push x) == φ x

    indPushouto : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                  → {P : Pushout f g → Type ℓ₄}
                  → (cl : (y : Y) → P (inl y)) → (cr : (z : Z) → P (inr z))
                  → ((x : X) → PathOver P (push x) (cl (f x)) (cr (g x)))
                  → (w : Pushout f g) → P w
    indPushouto cl cr φ (#inl y) = cl y
    indPushouto cl cr φ (#inr z) = cr z

    postulate
      indPushoutoβ : {ℓ₄ : Level} → {f : X → Y} → {g : X → Z}
                     → {P : Pushout f g → Type ℓ₄}
                     → (cl : (y : Y) → P (inl y)) → (cr : (z : Z) → P (inr z))
                     → (φ : (x : X) → PathOver P (push x) (cl (f x)) (cr (g x)))
                     → (x : X) → apdo (indPushouto cl cr φ) (push x) == φ x
  
  module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉}
           {X00 : Type ℓ₁} {X20 : Type ℓ₂} {X40 : Type ℓ₃}
           {X02 : Type ℓ₄} {X22 : Type ℓ₅} {X42 : Type ℓ₆}
           {X04 : Type ℓ₇} {X24 : Type ℓ₈} {X44 : Type ℓ₉}
           {f10 : X20 → X00} {f30 : X20 → X40}
           {f12 : X22 → X02} {f32 : X22 → X42}
           {f14 : X24 → X04} {f34 : X24 → X44}
           {f01 : X02 → X00} {f03 : X02 → X04}
           {f21 : X22 → X20} {f23 : X22 → X24}
           {f41 : X42 → X40} {f43 : X42 → X44}
           {s11 : (x : X22) → f01 (f12 x) == f10 (f21 x)}
           {s13 : (x : X22) → f03 (f12 x) == f14 (f23 x)}
           {s31 : (x : X22) → f41 (f32 x) == f30 (f21 x)}
           {s33 : (x : X22) → f43 (f32 x) == f34 (f23 x)} where
           

         
