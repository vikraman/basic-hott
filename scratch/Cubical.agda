-- {-# OPTIONS --allow-unsolved-metas #-}
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

  data =↓ (P : X → Type ℓ₂) : {x : X} → {y : X} → (p : x == y)
          → (ux : P x) → (uy : P y) → Type (ℓ₁ ⊔ ℓ₂) where
    reflo : {x : X} → (ux : P x) → =↓ P (refl x) ux ux

  apdo : {P : X → Type ℓ₂} (f : (x : X) → P x)
         {x y : X} → (p : x == y) → =↓ P p (f x) (f y)
  apdo f (refl x) = reflo (f x)

  pair=o : {P : X → Type ℓ₂}
           → {x y : X} → (p : x == y)
           → {ux : P x} → {uy : P y} → =↓ P p ux uy
           → (x , ux) == (y , uy)
  pair=o (refl x) (reflo ux) = refl (x , ux)

  glb-=↓-in : {P : X → Type ℓ₂} → {x : X}
              → {ux ux' : P x} → (ux == ux') → =↓ P (refl x) ux ux'
  glb-=↓-in (refl ux) = reflo ux
                     
  glb-=↓-out : {P : X → Type ℓ₂} → {x : X} → {ux ux' : P x}
               → =↓ P (refl x) ux ux' → (ux == ux')
  glb-=↓-out (reflo ux) = refl ux

  glb-=↓-η : {P : X → Type ℓ₂} → {x : X} → {ux ux' : P x}
             → glb-=↓-out ∘ glb-=↓-in {P} {x} {ux} {ux'} ∼ id
  glb-=↓-η (refl ux) = refl (refl ux)

  glb-=↓-β : {P : X → Type ℓ₂} → {x : X} → {ux ux' : P x}
             → glb-=↓-in ∘ glb-=↓-out {P} {x} {ux} {ux'} ∼ id
  glb-=↓-β (reflo ux) = refl (reflo ux)

  glb-=↓-τ : {P : X → Type ℓ₂} → {x : X} → {ux ux' : P x}
             → ap glb-=↓-in ∘ glb-=↓-η {P} {x} {ux} {ux'}
                ∼ glb-=↓-β ∘ glb-=↓-in
  glb-=↓-τ (refl ux) = refl (refl (reflo ux))

  glb-=↓-eqv : {P : X → Type ℓ₂} → {x : X}
               → (ux ux' : P x) → (ux == ux') ≃ =↓ P (refl x) ux ux'
  glb-=↓-eqv ux ux' = glb-=↓-in , glb-=↓-out ,
                      glb-=↓-η , glb-=↓-β , glb-=↓-τ

  glb-=↓-tpt-eqv : {P : X → Type ℓ₂}
                   → {x y : X} → (p : x == y) → (ux : P x) → (uy : P y)
                   →(tpt P p ux == uy) ≃ =↓ P p ux uy
  glb-=↓-tpt-eqv (refl x) ux uy = glb-=↓-eqv ux uy

  glb-=↓-const-eqv : {Y : Type ℓ₂} → {x x' : X} → (p : x == x')
                     → (y y' : Y) → (y == y') ≃ =↓ (λ _ → Y) p y y'
  glb-=↓-const-eqv (refl x) y y' = glb-=↓-eqv y y'


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} where

  =↓∘-eqv : (P : Y → Type ℓ₃) → (f : X → Y)
            → {x x' : X} → (p : x == x')
            → (ux : P (f x)) → (ux' : P (f x'))
            → =↓ (P ∘ f) p ux ux' ≃ =↓ P (ap f p) ux ux'
  =↓∘-eqv P f (refl x) ux ux' = glb-=↓-eqv ux ux' ● !e (glb-=↓-eqv ux ux')

  -- =↓Π-eqv


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

  data Square : {x00 x01 x10 x11 : X}
                → x00 == x01 → x00 == x10
                → x01 == x11 → x10 == x11 → Type ℓ where
       reflsq : {x00 : X} → Square (refl x00) (refl x00) (refl x00) (refl x00)


----------------------------------------------------------------------
-- B. Library
----------------------------------------------------------------------

module _ {ℓ} {X : Type ℓ} where

  whisker-sq : {x00 x01 x10 x11 : X}
               → {l l' : x00 == x01} → {t t' : x00 == x10}
               → {b b' : x01 == x11} → {r r' : x10 == x11}
               → l == l' → t == t' → b == b' → r == r'
               → Square l t b r
               → Square l' t' b' r'
  whisker-sq (refl l) (refl t) (refl b) (refl r) s = s

  whisker-sq-eqv : {x00 x01 x10 x11 : X}
                   → {l l' : x00 == x01} → {t t' : x00 == x10}
                   → {b b' : x01 == x11} → {r r' : x10 == x11}
                   → l == l' → t == t' → b == b' → r == r'
                   → Square l t b r ≃ Square l' t' b' r'
  whisker-sq-eqv (refl l) (refl t) (refl b) (refl r) = ide _



module _ {ℓ} {X : Type ℓ} where

  pillow : {x00 x01 x10 x11 : X}
           → {l l' : x00 == x01} → {t t' : x00 == x10}
           → {b b' : x01 == x11} → {r r' : x10 == x11}
           → {α-l : l == l'} → {α-t : t == t'} → {α-b : b == b'} → {α-r : r == r'}
           → (s : Square l t b r) → (s' : Square l' t' b' r')
           → Type ℓ
  pillow {α-l = α-l} {α-t} {α-b} {α-r} s s' = whisker-sq α-l α-t α-b α-r s == s'


module _ {ℓ} {X : Type ℓ} where

  hrefl-sq : {x y : X} → (p : x == y) → Square p (refl x) (refl y) p
  hrefl-sq (refl x) = reflsq

  vrefl-sq : {x y : X} → (p : x == y) → Square (refl x) p p (refl y)
  vrefl-sq (refl x) = reflsq

module _ {ℓ} {X : Type ℓ} where

  sq-from-glb-h : {x y : X} → {p q : x == y} → p == q
                  → Square p (refl x) (refl y) q
  sq-from-glb-h (refl (refl x)) = reflsq

  glb-from-sq-h : {x y : X} → {p q : x == y}
               → Square p (refl x) (refl y) q → p == q
  glb-from-sq-h reflsq = refl (refl _)

  sq-from-glb-h-η : {x y : X} → {p q : x == y}
             → glb-from-sq-h ∘ sq-from-glb-h {p = p} {q} ∼ id
  sq-from-glb-h-η (refl (refl x)) = refl (refl (refl x))

  sq-from-glb-h-ε : {x y : X} → {p q : x == y}
             → sq-from-glb-h ∘ glb-from-sq-h {p = p} {q} ∼ id
  sq-from-glb-h-ε reflsq = refl reflsq

  sq-from-glb-h-τ : {x y : X} → {p q : x == y}
             → ap sq-from-glb-h ∘ sq-from-glb-h-η
                ∼ sq-from-glb-h-ε ∘ sq-from-glb-h {p = p} {q}
  sq-from-glb-h-τ (refl (refl x)) = refl (refl reflsq)

  sq-from-glb-h-eqv : {x y : X} → (p q : x == y)
               → (p == q) ≃ Square p (refl x) (refl y) q
  sq-from-glb-h-eqv p q = sq-from-glb-h , glb-from-sq-h , sq-from-glb-h-η , sq-from-glb-h-ε , sq-from-glb-h-τ


module _ {ℓ} {X : Type ℓ} where

  sq-from-glb-v : {x y : X} → {p q : x == y} → p == q
                  → Square (refl x) p q (refl y)
  sq-from-glb-v (refl (refl x)) = reflsq

  glb-from-sq-v : {x y : X} → {p q : x == y}
                  → Square (refl x) p q (refl y) → p == q
  glb-from-sq-v reflsq = refl (refl _)

  sq-from-glb-v-η : {x y : X} → {p q : x == y}
                    → glb-from-sq-v ∘ sq-from-glb-v {p = p} {q} ∼ id
  sq-from-glb-v-η (refl (refl x)) = refl (refl (refl x))

  sq-from-glb-v-ε : {x y : X} → {p q : x == y}
                    → sq-from-glb-v ∘ glb-from-sq-v {p = p} {q} ∼ id
  sq-from-glb-v-ε reflsq = refl reflsq

  sq-from-glb-v-τ : {x y : X} → {p q : x == y}
                    → ap sq-from-glb-v ∘ sq-from-glb-v-η
                       ∼ sq-from-glb-v-ε ∘ sq-from-glb-v {p = p} {q}
  sq-from-glb-v-τ (refl (refl x)) = refl (refl reflsq)

  sq-from-glb-v-eqv : {x y : X} → (p q : x == y)
                      → (p == q) ≃ Square (refl x) p q (refl y)
  sq-from-glb-v-eqv p q = sq-from-glb-v , glb-from-sq-v ,
                          sq-from-glb-v-η , sq-from-glb-v-ε , sq-from-glb-v-τ


module _ {ℓ} {X : Type ℓ} where

  sq-l◾b-refl : {x00 x01 x10 x11 : X}
                → (l : x00 == x01) → (t : x00 == x10)
                → (b : x01 == x11) → (r : x10 == x11)
                → Square (l ◾ b) t (refl x11) r == Square l t b r 
  sq-l◾b-refl (refl _) t (refl _) r = refl _    

  sq-t◾r-refl : {x00 x01 x10 x11 : X}
                → (l : x00 == x01) → (t : x00 == x10)
                → (b : x01 == x11) → (r : x10 == x11)
                → Square l (refl x00) b (t ◾ r) == Square l t b r 
  sq-t◾r-refl l (refl _) b (refl _) = refl _    

  sq-t◾r-refl-out : {x00 x01 x10 x11 : X}
                    → {l : x00 == x01} → {t : x00 == x10}
                    → {b : x01 == x11} → {r : x10 == x11}
                    → Square l (refl x00) b (t ◾ r) → Square l t b r
  sq-t◾r-refl-out {l = l} {t} {b} {r} = p₁ (path-to-eqv (sq-t◾r-refl l t b r))

  sq-t◾r-refl-in : {x00 x01 x10 x11 : X}
                   → {l : x00 == x01} → {t : x00 == x10}
                   → {b : x01 == x11} → {r : x10 == x11}
                   → Square l t b r → Square l (refl x00) b (t ◾ r)
  sq-t◾r-refl-in {l = l} {t} {b} {r} = p₁ (p₂ (path-to-eqv (sq-t◾r-refl l t b r)))

  sq-r◾r'-out : {x00 x01 x10 x10' x11 : X}
                → {l : x00 == x01} → {t : x00 == x10}
                → {b : x01 == x11} → {r : x10 == x10'} → {r' : x10' == x11}
                → Square l t b (r ◾ r') → Square l (t ◾ r) b r'
  sq-r◾r'-out {t = refl _} {r = refl _} {r' = refl _} s = s

  sq-r◾r'-in : {x00 x01 x10 x10' x11 : X}
               → {l : x00 == x01} → {t : x00 == x10}
               → {b : x01 == x11} → {r : x10 == x10'} → {r' : x10' == x11}
               → Square l (t ◾ r) b r' → Square l t b (r ◾ r')
  sq-r◾r'-in {t = refl _} {r = refl _} {r' = refl _} s = s

module _ {ℓ} {X : Type ℓ} where

  -- "disc" ?
  disc-sq-eqv : {x00 x01 x10 x11 : X}
                → (l : x00 == x01) → (t : x00 == x10)
                → (b : x01 == x11) → (r : x10 == x11)
                → (l ◾ b == t ◾ r) ≃ Square l t b r
  disc-sq-eqv l t b r = path-to-eqv (sq-t◾r-refl _ _ _ _)
                        ● path-to-eqv (sq-l◾b-refl _ _ _ _)
                        ● sq-from-glb-h-eqv (l ◾ b) (t ◾ r)

  disc-sq-out : {x00 x01 x10 x11 : X}
                → {l : x00 == x01} → {t : x00 == x10}
                → {b : x01 == x11} → {r : x10 == x11}
                → Square l t b r → (l ◾ b) == (t ◾ r)
  disc-sq-out {l = l} {t} {b} {r} = p₁ (p₂ (disc-sq-eqv l t b r))

  disc-sq-in : {x00 x01 x10 x11 : X}
               → {l : x00 == x01} → {t : x00 == x10}
               → {b : x01 == x11} → {r : x10 == x11}
               → (l ◾ b) == (t ◾ r) → Square l t b r
  disc-sq-in {l = l} {t} {b} {r} = p₁ (disc-sq-eqv l t b r)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  sq-from-=↓-v-eqv : (f g : X → Y) → {x x' : X} → (p : x == x')
                     → (ux : f x == g x) → (ux' : f x' == g x')
                     → =↓ (paths f g) p ux ux' ≃ Square ux (ap f p) (ap g p) ux'
  sq-from-=↓-v-eqv f g (refl x) ux ux' = sq-from-glb-h-eqv ux ux' ● !e (glb-=↓-eqv ux ux') 

  sq-from-=↓-v : {f g : X → Y} → {x x' : X} → {p : x == x'}
                   → {ux : f x == g x} → {ux' : f x' == g x'}
                   → =↓ (paths f g) p ux ux' → Square ux (ap f p) (ap g p) ux'
  sq-from-=↓-v {f} {g} {p = p} {ux} {ux'} = p₁ (sq-from-=↓-v-eqv f g p ux ux')

  =↓-from-sq-v : {f g : X → Y} → {x x' : X} → {p : x == x'}
                 → {ux : f x == g x} → {ux' : f x' == g x'}
                 → Square ux (ap f p) (ap g p) ux' → =↓ (paths f g) p ux ux'
  =↓-from-sq-v {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (sq-from-=↓-v-eqv f g p ux ux'))

  sq-from-=↓-v-η : {f g : X → Y} → {x x' : X} → {p : x == x'}
                → {ux : f x == g x} → {ux' : f x' == g x'}
                → =↓-from-sq-v ∘ sq-from-=↓-v {p = p} {ux} {ux'} ∼ id
  sq-from-=↓-v-η {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (p₂ (sq-from-=↓-v-eqv f g p ux ux')))

  sq-from-=↓-v-β : {f g : X → Y} → {x x' : X} → {p : x == x'}
                → {ux : f x == g x} → {ux' : f x' == g x'}
                → sq-from-=↓-v ∘ =↓-from-sq-v {p = p} {ux} {ux'} ∼ id
  sq-from-=↓-v-β {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (p₂ (p₂ (sq-from-=↓-v-eqv f g p ux ux'))))


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  sq-from-=↓-h-eqv : (f g : X → Y) → {x x' : X} → (p : x == x')
                  → (ux : f x == g x) → (ux' : f x' == g x')
                  → =↓ (paths f g) p ux ux' ≃ Square (ap f p) ux ux' (ap g p)
  sq-from-=↓-h-eqv f g (refl x) ux ux' = sq-from-glb-v-eqv ux ux' ● !e (glb-=↓-eqv ux ux')

  sq-from-=↓-h : {f g : X → Y} → {x x' : X} → {p : x == x'}
                   → {ux : f x == g x} → {ux' : f x' == g x'}
                   → =↓ (paths f g) p ux ux' → Square (ap f p) ux ux' (ap g p)
  sq-from-=↓-h {f} {g} {p = p} {ux} {ux'} = p₁ (sq-from-=↓-h-eqv f g p ux ux')

  =↓-from-sq-h : {f g : X → Y} → {x x' : X} → {p : x == x'}
                 → {ux : f x == g x} → {ux' : f x' == g x'}
                 → Square (ap f p) ux ux' (ap g p) → =↓ (paths f g) p ux ux'
  =↓-from-sq-h {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (sq-from-=↓-h-eqv f g p ux ux'))

  sq-from-=↓-h-η : {f g : X → Y} → {x x' : X} → {p : x == x'}
                → {ux : f x == g x} → {ux' : f x' == g x'}
                → =↓-from-sq-h ∘ sq-from-=↓-h {p = p} {ux} {ux'} ∼ id
  sq-from-=↓-h-η {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (p₂ (sq-from-=↓-h-eqv f g p ux ux')))

  sq-from-=↓-h-β : {f g : X → Y} → {x x' : X} → {p : x == x'}
                → {ux : f x == g x} → {ux' : f x' == g x'}
                → sq-from-=↓-h ∘ =↓-from-sq-h {p = p} {ux} {ux'} ∼ id
  sq-from-=↓-h-β {f} {g} {p = p} {ux} {ux'} = p₁ (p₂ (p₂ (p₂ (sq-from-=↓-h-eqv f g p ux ux'))))


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-sq : (f : X → Y) → {x00 x01 x10 x11 : X}
              → {l : x00 == x01} → {t : x00 == x10}
              → {b : x01 == x11} → {r : x10 == x11}
              → Square l t b r → Square (ap f l) (ap f t) (ap f b) (ap f r)
  ap-sq f reflsq = reflsq


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  pair-line : {x x' : X} → (p : x == x')
              → {y y' : Y} → (q : y == y')
              → (x , y) == (x' , y')
  pair-line p q = pair= (p , q)

  pair-sq : {x00 x01 x10 x11 : X}
                → {lx : x00 == x01} → {tx : x00 == x10}
                → {bx : x01 == x11} → {rx : x10 == x11}
                → Square lx tx bx rx
                → {y00 y01 y10 y11 : Y}
                → {ly : y00 == y01} → {ty : y00 == y10}
                → {by : y01 == y11} → {ry : y10 == y11}
                → Square ly ty by ry
                → Square (pair-line lx ly) (pair-line tx ty) (pair-line bx by) (pair-line rx ry)
  pair-sq reflsq reflsq = reflsq


module _ {ℓ} {X : Type ℓ} where

  infixr 80 _◾-sq-v_
  _◾-sq-v_ : {x00 x01 x02 x10 x11 x12 : X}
                 → {l : x00 == x01} → {l' : x01 == x02}
                 → {t : x00 == x10}
                 → {b : x01 == x11} → {b' : x02 == x12}
                 → {r : x10 == x11} → {r' : x11 == x12}
                 → Square l t b r
                 → Square l' b b' r'
                 → Square (l ◾ l') t b' (r ◾ r')
  _◾-sq-v_ reflsq reflsq = reflsq

  infixr 80 _◾-sq-h_
  _◾-sq-h_ : {x00 x01 x10 x11 x20 x21 : X}
                 → {l : x00 == x01}
                 → {t : x00 == x10} → {t' : x10 == x20}
                 → {b : x01 == x11} → {b' : x11 == x21}
                 → {r : x10 == x11} → {r' : x20 == x21}
                 → Square l t b r
                 → Square r t' b' r'
                 → Square l (t ◾ t') (b ◾ b') r'
  _◾-sq-h_ reflsq reflsq = reflsq


module _ {ℓ} {X : Type ℓ} where

  sq-reflect : {x00 x01 x10 x11 : X}
                    → {l : x00 == x01} → {t : x00 == x10}
                    → {b : x01 == x11} → {r : x10 == x11}
                    → Square l t b r → Square t l r b
  sq-reflect reflsq = reflsq

  sq-reflect-η : {x00 x01 x10 x11 : X}
                 → {l : x00 == x01} → {t : x00 == x10}
                 → {b : x01 == x11} → {r : x10 == x11}
                 → sq-reflect ∘ sq-reflect {l = l} {t} {b} {r} ∼ id
  sq-reflect-η reflsq = refl reflsq

  sq-reflect-τ : {x00 x01 x10 x11 : X}
                 → {l : x00 == x01} → {t : x00 == x10}
                 → {b : x01 == x11} → {r : x10 == x11}
                 → ap sq-reflect ∘ sq-reflect-η {l = l} {t} {b} {r} ∼ sq-reflect-η ∘ sq-reflect
  sq-reflect-τ reflsq = refl (refl reflsq)

  sq-reflect-eqv : {x00 x01 x10 x11 : X}
                   → (l : x00 == x01) → (t : x00 == x10)
                   → (b : x01 == x11) → (r : x10 == x11)
                   → Square l t b r ≃ Square t l r b
  sq-reflect-eqv l t b r = sq-reflect , sq-reflect , sq-reflect-η , sq-reflect-η , sq-reflect-τ

  sq-reflect-h : {x00 x01 x10 x11 : X}
                 → {l : x00 == x01} → {t : x00 == x10}
                 → {b : x01 == x11} → {r : x10 == x11}
                 → Square l t b r → Square (! l) b t (! r)
  sq-reflect-h reflsq = reflsq

  sq-reflect-v : {x00 x01 x10 x11 : X}
                 → {l : x00 == x01} → {t : x00 == x10}
                 → {b : x01 == x11} → {r : x10 == x11}
                 → Square l t b r → Square r (! t) (! b) l
  sq-reflect-v reflsq = reflsq



module _ {ℓ} {X : Type ℓ} where

  -- Note that the argument order does not adhere their standard
  -- ordering of square sides
  Kan-right : {x00 x01 x10 x11 : X}
              → (t : x00 == x10)
              → (b : x01 == x11)
              → (l : x00 == x01) 
              → x10 == x11
  Kan-right t b l = ! t ◾ l ◾ b
  
  fill-sq-right : {x00 x01 x10 x11 : X}
                  → (l : x00 == x01) → (t : x00 == x10)
                  → (b : x01 == x11)
                  → Σ (x10 == x11) (λ r → Square l t b r)
  fill-sq-right l t b = Kan-right t b l ,
                        sq-r◾r'-in (whisker-sq (refl l) (! (◾invr t))
                                               (refl b) (refl (l ◾ b))
                                               (sq-t◾r-refl-in (disc-sq-in (refl (l ◾ b)))))

  Kan-left : {x00 x01 x10 x11 : X}
              → (t : x00 == x10)
              → (b : x01 == x11)
              → (r : x10 == x11) 
              → x00 == x01
  Kan-left t b r = t ◾ r ◾ ! b


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-Kan-right : (f : X → Y)
                 → {x00 x01 x10 x11 : X}
                 → (t : x00 == x10) → (b : x01 == x11) → (l : x00 == x01)
                 → ap f (Kan-right t b l) == Kan-right (ap f t) (ap f b) (ap f l)
  ap-Kan-right f (refl x) (refl .x) (refl .x) = refl (refl (f x))


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
                  → (ul : =↓ P l ux00 ux01)
                  → (ut : =↓ P t ux00 ux10)
                  → (ub : =↓ P b ux01 ux11)
                  → (ur : =↓ P r ux10 ux11)
                  → Type (ℓ₁ ⊔ ℓ₂) where
       reflsqo : SquareOver P reflsq (reflo ux00) (reflo ux00)
                                     (reflo ux00) (reflo ux00)


----------------------------------------------------------------------
--                             V. Cubes
----------------------------------------------------------------------

module _ {ℓ} {X : Type ℓ} where

  data Cube : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
       reflcube : {x000 : X} → Cube (reflsq {x00 = x000}) reflsq reflsq reflsq reflsq reflsq

  infixr 80 _◾-cube-x_
  _◾-cube-x_ : {x000 x010 x100 x110 x001 x011 x101 x111 x200 x210 x201 x211 : X}
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
               → {p2-0 : x200 == x210} → {p20- : x200 == x201}
               → {p21- : x210 == x211} → {p2-1 : x201 == x211}
               → {front' : Square p2-0 p20- p21- p2-1}
               → {p-00' : x100 == x200} → {p-01' : x101 == x201}
               → {p-10' : x110 == x210} → {p-11' : x111 == x211}
               → {left' : Square p1-0 p-00' p-10' p2-0}
               → {right' : Square p1-1 p-01' p-11' p2-1}
               → {bottom' : Square p-10' p11- p21- p-11'}
               → {top' : Square p-00' p10- p20- p-01'}
               → Cube left right back top bottom front
               → Cube left' right' front top' bottom' front'
               → Cube (left ◾-sq-h left') (right ◾-sq-h right') back
                       (top ◾-sq-v top') (bottom ◾-sq-v bottom') front'
  _◾-cube-x_ reflcube reflcube = reflcube

  infixr 80 _◾-cube-y_
  _◾-cube-y_ : {x000 x010 x100 x110 x001 x011 x101 x111 x002 x012 x102 x112 : X}
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
               → Cube left right' (back ◾-sq-h back') (top ◾-sq-h top')
                      (bottom ◾-sq-h bottom') (front ◾-sq-h front')
  _◾-cube-y_ reflcube reflcube = reflcube

  infixr 80 _◾-cube-z_
  _◾-cube-z_ : {x000 x010 x100 x110 x001 x011 x101 x111 x020 x021 x120 x121 : X}
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
               → {p-20 : x020 == x120} → {p02- : x020 == x021}
               → {p12- : x120 == x121} → {p-21 : x021 == x121}
               → {bottom' : Square p-20 p02- p12- p-21}
               → {p0-0' : x010 == x020} → {p0-1' : x011 == x021}
               → {p1-0' : x110 == x120} → {p1-1' : x111 == x121}
               → {right' : Square p0-1' p-11 p-21 p1-1'}
               → {left' : Square p0-0' p-10 p-20 p1-0'}
               → {back' : Square p0-0' p01- p02- p0-1'}
               → {front' : Square p1-0' p11- p12- p1-1'}
               → Cube left right back top bottom front
               → Cube left' right' back' bottom bottom' front'
               → Cube (left ◾-sq-v left') (right ◾-sq-v right')
                       (back ◾-sq-v back')
                       top bottom'
                       (front ◾-sq-v front')
  _◾-cube-z_ reflcube reflcube = reflcube



  whisker-cube : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
                 → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                 → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                 → {left left' : Square p0-0 p-00 p-10 p1-0}
                 → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
                 → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
                 → {right right' : Square p0-1 p-01 p-11 p1-1}
                 → {p00- : x000 == x001} → {p01- : x010 == x011}
                 → {p10- : x100 == x101} → {p11- : x110 == x111}
                 → {back back' : Square p0-0 p00- p01- p0-1}
                 → {top top' : Square p-00 p00- p10- p-01}
                 → {bottom bottom' : Square p-10 p01- p11- p-11}
                 → {front front' : Square p1-0 p10- p11- p1-1}
                 → (left == left') → (right == right')
                 → (back == back') → (top == top')
                 → (bottom == bottom') → (front == front')
                 → Cube left right back top bottom front
                 → Cube left' right' back' top' bottom' front'
  whisker-cube (refl left) (refl right) (refl back)
               (refl top) (refl bottom) (refl front) c = c

  glue-pillow-top : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
                    → {p-00' : x000 == x100} → {p00-' : x000 == x001}
                    → {p10-' : x100 == x101} → {p-01' : x001 == x101}
                    → {top' : Square p-00' p00-' p10-' p-01'}
                    → {α-l : p-00 == p-00' } → {α-t : p00- == p00-' }
                    → {α-b : p10- == p10-' } → {α-r : p-01 == p-01' }
                    → pillow {α-l = α-l} {α-t} {α-b} {α-r} top top'
                    → Cube (whisker-sq (refl _) α-l (refl _) (refl _) left)
                            (whisker-sq (refl _) α-r (refl _) (refl _) right)
                            (whisker-sq (refl _) α-t (refl _) (refl _) back)
                            top' bottom
                            (whisker-sq (refl _) α-b (refl _) (refl _) front)
  glue-pillow-top c {α-l = (refl p-00)} {α-t = (refl p00-)}
                    {α-b = (refl p10-)} {α-r = (refl p-01)} (refl top) = c

  glue-pillow-bottom : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
                    → {p-10' : x010 == x110} → {p01-' : x010 == x011}
                    → {p11-' : x110 == x111} → {p-11' : x011 == x111}
                    → {bottom' : Square p-10' p01-' p11-' p-11'}
                    → {α-l : p-10 == p-10' } → {α-t : p01- == p01-' }
                    → {α-b : p11- == p11-' } → {α-r : p-11 == p-11' }
                    → pillow {α-l = α-l} {α-t} {α-b} {α-r} bottom bottom'
                    → Cube (whisker-sq (refl _) (refl _) α-l (refl _) left)
                            (whisker-sq (refl _) (refl _) α-r (refl _) right)
                            (whisker-sq (refl _) (refl _) α-t (refl _) back)
                            top bottom'
                            (whisker-sq (refl _) (refl _) α-b (refl _) front)
  glue-pillow-bottom c {α-l = (refl p-00)} {α-t = (refl p00-)}
                    {α-b = (refl p10-)} {α-r = (refl p-01)} (refl bottom) = c


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
            → Cube (ap-sq f left) (ap-sq f right)
                    (ap-sq f back) (ap-sq f top)
                    (ap-sq f bottom) (ap-sq f front)
  ap-cube f reflcube = reflcube


module _ {ℓ} {X : Type ℓ} where

  cube-reflect-left-to-top : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
            → Cube (sq-reflect back) (sq-reflect front)
                    (sq-reflect top) left
                    right (sq-reflect bottom)
  cube-reflect-left-to-top reflcube = reflcube

  cube-reflect-xy : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
            → Cube (sq-reflect-h left) (sq-reflect-h right) (sq-reflect-h back)
                    bottom top (sq-reflect-h front)
  cube-reflect-xy reflcube = reflcube

  cube-reflect-xz : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
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
            → Cube right left (sq-reflect-v back) (sq-reflect-v top)
                    (sq-reflect-v bottom) (sq-reflect-v front)
  cube-reflect-xz reflcube = reflcube



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
  fill-cube-left reflsq reflsq reflsq reflsq reflsq = reflsq , reflcube

  fill-cube-top : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
                   → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                   → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                   → (left : Square p0-0 p-00 p-10 p1-0)
                   → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
                   → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
                   → (right : Square p0-1 p-01 p-11 p1-1)
                   → {p00- : x000 == x001} → {p01- : x010 == x011}
                   → {p10- : x100 == x101} → {p11- : x110 == x111}
                   → (back : Square p0-0 p00- p01- p0-1)
                   → (bottom : Square p-10 p01- p11- p-11)
                   → (front : Square p1-0 p10- p11- p1-1)
                   → Σ (Square p-00 p00- p10- p-01)
                        (λ top → Cube left right back top bottom front)
  fill-cube-top reflsq reflsq reflsq reflsq reflsq = reflsq , reflcube


-- module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

--   in-SquareOver= : (f g : X → Y)
--                    → {x00 x01 x10 x11 : X}
--                    → {l : x00 == x01} → {t : x00 == x10}
--                    → {b : x01 == x11} → {r : x10 == x11}
--                    → (s : Square l t b r)
--                    → {ux00 : f x00 == g x00} → {ux01 : f x01 == g x01}
--                    → {ux10 : f x10 == g x10} → {ux11 : f x11 == g x11}
--                    → (ul : =↓ (paths f g) l ux00 ux01)
--                    → (ut : =↓ (paths f g) t ux00 ux10)
--                    → (ub : =↓ (paths f g) b ux01 ux11)
--                    → (ur : =↓ (paths f g) r ux10 ux11)
--                    → Cube (sq-from-=↓-v ul) (sq-from-=↓-v ur)
--                            (sq-from-=↓-v ut) (ap-sq f s)
--                            (ap-sq g s) (sq-from-=↓-v ub)
--                    → SquareOver (paths f g) s ul ut ub ur
--   in-SquareOver= f g reflsq = {!!}


module _ {ℓ} {X : Type ℓ} where

  left-right-eqv : {x000 x010 x100 x110 x001 x011 x101 x111 : X}
                   → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                   → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                   -- → {left : Square p0-0 p-00 p-10 p1-0}
                   → {p0-1 : x001 == x011} → {p-01 : x001 == x101}
                   → {p-11 : x011 == x111} → {p1-1 : x101 == x111}
                   -- → {right : Square p0-1 p-01 p-11 p1-1}
                   → {p00- : x000 == x001} → {p01- : x010 == x011}
                   → {p10- : x100 == x101} → {p11- : x110 == x111}
                   → (back : Square p0-0 p00- p01- p0-1)
                   → (top : Square p-00 p00- p10- p-01)
                   → (bottom : Square p-10 p01- p11- p-11)
                   → (front : Square p1-0 p10- p11- p1-1)
                   → Square p0-0 p-00 p-10 p1-0 ≃ Square p0-1 p-01 p-11 p1-1
  left-right-eqv {p00- = refl _} {p01- = refl _} {p10- = refl _} {p11- = refl _}
                 back top bottom front = whisker-sq-eqv (glb-from-sq-h back) (glb-from-sq-h top)
                                                        (glb-from-sq-h bottom) (glb-from-sq-h front)


module _ {ℓ₁} {X : Type ℓ₁} where

  cube-left=right : {x000 x010 x100 x110 : X}
                    → {p0-0 : x000 == x010} → {p-00 : x000 == x100}
                    → {p-10 : x010 == x110} → {p1-0 : x100 == x110}
                    → {left right : Square p0-0 p-00 p-10 p1-0}
                    → Cube left right (sq-from-glb-h (refl p0-0)) (sq-from-glb-h (refl p-00)) (sq-from-glb-h (refl p-10)) (sq-from-glb-h (refl p1-0))
                    → left == right
  cube-left=right reflcube = refl reflsq

  cube-back=front : {x000 x010 x001 x011 : X}
                    → {p0-0 : x000 == x010} → {p00- : x000 == x001}
                    → {p01- : x010 == x011} → {p0-1 : x001 == x011}
                    → {back front : Square p0-0 p00- p01- p0-1}
                    → Cube (sq-from-glb-h (refl p0-0)) (sq-from-glb-h (refl p0-1))
                            back (sq-from-glb-v (refl p00-))
                            (sq-from-glb-v (refl p01-)) front
                    → back == front
  cube-back=front reflcube = refl reflsq


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap-sq-sq-from-glb-h-refl : (f : X → Y) → {x y : X} → (p : x == y)
                             → (ap-sq f (sq-from-glb-h (refl p))) == (sq-from-glb-h (refl (ap f p)))
  ap-sq-sq-from-glb-h-refl f (refl x) = refl reflsq

  ap-sq-sq-from-glb-v-refl : (f : X → Y) → {x y : X} → (p : x == y)
                             → (ap-sq f (sq-from-glb-v (refl p))) == (sq-from-glb-v (refl (ap f p)))
  ap-sq-sq-from-glb-v-refl f (refl x) = refl reflsq



module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} where

  pathover-from-cube : {f g : X → X} → {x y : Z → X}
                       → {ux : (z : Z) → (g ∘ f) (x z) == id (x z)}
                       → {uy : (z : Z) → (g ∘ f) (y z) == id (y z)}
                       → {q : (z : Z) → x z == y z}
                       → {v w : Z} → {p : v == w}
                       → {uv : =↓ (paths (g ∘ f) id) (q v) (ux v) (uy v)}
                       → {uw : =↓ (paths (g ∘ f) id) (q w) (ux w) (uy w)}
                       → Cube (whisker-sq (refl _) (ap∘ _ _ _) (ap∘ _ _ _) (refl _)
                                           (sq-from-=↓-v (apdo ux p))) -- ()
                               (whisker-sq (refl _) (ap∘ _ _ _) (ap∘ _ _ _) (refl _)
                                           (sq-from-=↓-v (apdo uy p)))
                               (sq-from-=↓-v uv)
                               (ap-sq (g ∘ f) (sq-from-=↓-h (apdo q p)))
                               (ap-sq id (sq-from-=↓-h (apdo q p)))
                               (sq-from-=↓-v uw)
                       → =↓ (λ z → =↓ (paths (g ∘ f) id) (q z) (ux z) (uy z))
                             p uv uw
  pathover-from-cube {f} {g} {ux = ux} {uy} {q = q} {p = refl v} {uv = uv} {uw = uw} c = glb-=↓-in (! (sq-from-=↓-v-η _) ◾ ap =↓-from-sq-v (cube-back=front (whisker-cube (refl _) (refl _) (refl _) (ap-sq-sq-from-glb-v-refl _ _) (ap-sq-sq-from-glb-v-refl _ _) (refl _) {- (ap-sq-sq-from-glb-h-refl _ _) (ap-sq-sq-from-glb-h-refl _ _) (refl _) (refl _) (refl _) (refl _) -} c)) ◾ sq-from-=↓-v-η _)


module _ {ℓ} {X : Type ℓ} where

  -- TODO : this is the inverse of cube-left=right
  cube-from-pillow : {x00 x01 x10 x11 : X}
                     → {l : x00 == x01} → {t : x00 == x10}
                     → {b : x01 == x11} → {r : x10 == x11}
                     → {s s' : Square l t b r} → s == s'
                     → Cube s s'
                            (sq-from-glb-h (refl _)) (sq-from-glb-h (refl _))
                            (sq-from-glb-h (refl _)) (sq-from-glb-h (refl _))
  cube-from-pillow (refl reflsq) = reflcube

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  cube-from-sq-eqv-η : {x00 x01 x10 x11 : X}
                       → {l : x00 == x01} → {t : x00 == x10}
                       → {b : x01 == x11} → {r : x10 == x11}
                       → {y00 y01 y10 y11 : Y}
                       → {l' : y00 == y01} → {t' : y00 == y10}
                       → {b' : y01 == y11} → {r' : y10 == y11}
                       → (e : Square l t b r ≃ Square l' t' b' r')
                       → (s : Square l t b r)
                       → Cube ((p₁ (p₂ e)) ((p₁ e) s)) s
                               (sq-from-glb-h (refl _)) (sq-from-glb-h (refl _))
                               (sq-from-glb-h (refl _)) (sq-from-glb-h (refl _))
  cube-from-sq-eqv-η e s = cube-from-pillow (η s)
    where η = p₁ (p₂ (p₂ e))


module _ {ℓ} {X : Type ℓ} where

  ap-sq-id : {x00 x01 x10 x11 : X}
             → {l : x00 == x01} → {t : x00 == x10}
             → {b : x01 == x11} → {r : x10 == x11}
             → (s : Square l t b r)
             → Cube (ap-sq id s) s (sq-from-glb-h (ap-id l))
                     (sq-from-glb-h (ap-id t)) (sq-from-glb-h (ap-id b)) (sq-from-glb-h (ap-id r))
  ap-sq-id reflsq = reflcube
