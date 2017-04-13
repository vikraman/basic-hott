{-# OPTIONS --without-K #-}
module Paths where

open import Type
open import Functions
open import DependentSum


infixr 30 _==_
data _==_ {ℓ} {X : Type ℓ} : X → X → Type ℓ where
  refl : (x : X) →  x == x 

==' : {ℓ : Level} → (X : Type ℓ) → X → X → Type ℓ
==' X x y = _==_ {X = X} x y 

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  ind= : (P : {x y : X} → (p : x == y) → Type ℓ₂)
         → ((x : X) → P (refl x))
         → {x y : X} → (p : x == y) → P p
  ind= P r (refl x) = r x 

  ind=l : {x : X} → (P : {y : X} → (p : x == y) → Type ℓ₂)
          → P (refl x)
          → {y : X} → (p : x == y) → P p
  ind=l P r (refl x) = r

  ind=r : {y : X} → (P : {x : X} → (p : x == y) → Type ℓ₂)
          → P (refl y)
          → {x : X} → (p : x == y) → P p
  ind=r P r (refl x) = r


module _ {ℓ} {X : Type ℓ} where

  infix 100 !
  ! : {x y : X} → x == y → y == x
  ! (refl x) = refl x

  infixr 80 _◾_
  _◾_ : {x y : X} → x == y → {z : X} → y == z → x == z
  _◾_ (refl y) (refl .y) = refl y

  infix 120 _◾-
  _◾- : {x y z : X} → x == y → y == z → x == z
  p ◾- = _◾_ p

  infix 100 -◾_
  -◾_ : {x y z : X} → y == z → x == y → x == z
  -◾ q = λ p → p ◾ q


module _ {ℓ} where

  coe : {X Y : Type ℓ} → X == Y → X → Y
  coe (refl X) = id

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where
 
  ap : (f : X → Y) → {x y : X} → x == y → f x == f y
  ap f (refl x) = refl (f x)


module _ {ℓ} {X : Type ℓ} where

  ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
  ◾unitr (refl x) = refl (refl x)
  
  ◾unitl : {x y : X} → (p : x == y) → refl x ◾ p == p
  ◾unitl (refl x) = refl (refl x)

  ◾invl : {x y : X} → (p : x == y) → ! p ◾ p == refl y
  ◾invl (refl x) = refl (refl x)
  
  ◾invr : {x y : X} → (p : x == y) → p ◾ ! p == refl x
  ◾invr (refl x) = refl (refl x)

  !! : {x y : X} → (p : x == y) → ! (! p) == p
  !! (refl x) = refl (refl x)

  !!! : {x y : X} → (p : x == y) → ap ! (!! p) == !! (! p)
  !!! (refl x) = refl (refl (refl x))

  !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
  !◾ (refl y) (refl .y) = refl (refl y)


module _ {ℓ} {X : Type ℓ} where

  infixr 80 _[1,0,2]_
  _[1,0,2]_ : {x y z : X} → {r s : y == z}
              → (p : x == y) → r == s → p ◾ r == p ◾ s
  (refl y) [1,0,2] γ = ◾unitl _ ◾ γ ◾ ! (◾unitl _)

  infixr 80 _[2,0,1]_
  _[2,0,1]_ : {x y z : X} → {p q : x == y}
              → p == q → (r : y == z) → p ◾ r == q ◾ r
  α [2,0,1] (refl y) = ◾unitr _ ◾ α ◾ ! (◾unitr _)

  infixr 80 _[2,0,2]_
  _[2,0,2]_ : {x y z : X} → {p q : x == y} → {r s : y == z}
              → p == q → r == s → p ◾ r == q ◾ s
  _[2,0,2]_ {q = q} {r} α β = (α [2,0,1] r) ◾ (q [1,0,2] β)

  infixr 80 _[2,0,2]'_
  _[2,0,2]'_ : {x y z : X} → {p q : x == y} → {r s : y == z}
               → p == q → r == s → p ◾ r == q ◾ s
  _[2,0,2]'_ {p = p} {s = s} α β = (p [1,0,2] β) ◾ (α [2,0,1] s)

  -----

  infixr 80 _[3,0,1]_
  _[3,0,1]_ : {x y z : X} → {p q : x == y} → {α β : p == q}
              → α == β → (r : y == z) → α [2,0,1] r == β [2,0,1] r
  _[3,0,1]_ (refl α) r = refl (α [2,0,1] r)

  infixr 80 _[1,0,3]_
  _[1,0,3]_ : {x y z : X} → {r s : y == z} → {γ δ : r == s}
              → (p : x == y) → γ == δ → p [1,0,2] γ == p [1,0,2] δ
  _[1,0,3]_ p (refl γ) = refl (p [1,0,2] γ)

  infixr 80 _[3,0,2]_
  _[3,0,2]_ : {x y z : X} → {p q : x == y} → {r s : y == z} → {α β : p == q}
              → α == β → (γ : r == s) → α [2,0,2] γ == β [2,0,2] γ
  _[3,0,2]_ (refl α) γ = refl _

  infixr 80 _[2,0,3]_
  _[2,0,3]_ : {x y z : X} → {p q : x == y} → {r s : y == z} → {γ δ : r == s}
              → (α : p == q) → γ == δ → α [2,0,2] γ == α [2,0,2] δ
  _[2,0,3]_ α (refl γ) = refl _

  infixr 80 _[3,0,3]_
  _[3,0,3]_ : {x y z : X} → {p q : x == y} → {r s : y == z}
              → {α β : p == q} → {γ δ : r == s}
              → α == β → γ == δ → α [2,0,2] γ == β [2,0,2] δ
  _[3,0,3]_ {β = β} {γ} A B = (A [3,0,2] γ) ◾ (β [2,0,3] B)

  infixr 80 _[3,1,2]_
  _[3,1,2]_ : {x y : X} → {p q r : x == y} → {α β : p == q}
              → α == β → (γ : q == r) → α ◾ γ == β ◾ γ
  _[3,1,2]_ (refl α) γ = refl (α ◾ γ)

  infixr 80 _[2,1,3]_
  _[2,1,3]_ : {x y : X} → {p q r : x == y} → {γ δ : q == r}
              → (α : p == q) → γ == δ → α ◾ γ == α ◾ δ
  _[2,1,3]_ α (refl γ) = refl (α ◾ γ)

  infixr 80 _[3,1,3]_
  _[3,1,3]_ : {x y : X} → {p q r : x == y}
              → {α β : p == q} → {γ δ : q == r}
              → α == β → γ == δ → α ◾ γ == β ◾ δ
  _[3,1,3]_ {β = β} {γ} A B = (A [3,1,2] γ) ◾ (β [2,1,3] B)


  pad-sq : {w x y z : X}
           → {l₁ l₁' : w == x} → {l₂ l₂' : x == z}
           → {r₁ r₁' : w == y} → {r₂ r₂' : y == z}
           → (α₁ : l₁ == l₁') → (α₂ : l₂ == l₂')
           → (β₁ : r₁ == r₁') → (β₂ : r₂ == r₂')
           → l₁ ◾ l₂ == r₁ ◾ r₂ → l₁' ◾ l₂' == r₁' ◾ r₂'
  pad-sq α₁ α₂ β₁ β₂ γ = (! α₁ [2,0,2] ! α₂) ◾ γ ◾ (β₁ [2,0,2] β₂)

  =-prsrv-= : {x x' y y' : X} → x == x' → y == y' → (x == y) == (x' == y')
  =-prsrv-= (refl x) (refl y) = refl (x == y)


module _ {ℓ} {X : Type ℓ} where

  ◾assoc : {w x y z : X} → (p : w == x) → (q : x == y) → (r : y == z)
           → (p ◾ q) ◾ r == p ◾ q ◾ r
  ◾assoc p q (refl y) = ◾unitr _ ◾ (p [1,0,2] ! (◾unitr _))


module _ {ℓ} where

  coe◾ : {X Y Z : Type ℓ} → (p : X == Y) → (q : Y == Z)
         → (x : X) → coe (p ◾ q) x == coe q (coe p x)
  coe◾ (refl Y) q x = ap (λ γ → coe γ x) (◾unitl q)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ap◾ : (f : X → Y) → {x y z : X} → (p : x == y) → (q : y == z)
        → ap f (p ◾ q) == ap f p ◾ ap f q
  ap◾ f (refl y) q = ap (ap f) (◾unitl _) ◾ ! (◾unitl _)

  ap∘ : {ℓ₃ : Level} → {Z : Type ℓ₃} → (g : Y → Z) → (f : X → Y) 
        → {x y : X} → (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
  ap∘ g f (refl x) = refl (refl (g (f x)))

  ap! : (f : X → Y) → {x y : X} → (p : x == y)
        → ap f (! p) == ! (ap f p)
  ap! f (refl x) = refl (refl (f x))


module _ {ℓ} {X : Type ℓ} where

  ap-id : {x y : X} → (p : x == y) → ap id p == p
  ap-id (refl x) = refl (refl x)


module _ {ℓ} {X : Type ℓ} where
  -- Some derived cancellation rules The expected input path is of
  -- type l₁ ◾ ... ◾ lₘ == r₁ ◾ ... ◾ rₙ .

  -- left cancellation
  refl=!l◾r : {x y : X} → {l r : x == y} → l == r → refl y == ! l ◾ r
  refl=!l◾r α =
    ! (◾invl _) ◾ (! _ [1,0,2] α)

  l₂=!l₁◾r : {x y z : X} → {l₁ : x == y} → {l₂ : y == z} → {r : x == z}
            → l₁ ◾ l₂ == r → l₂ == ! l₁ ◾ r
  l₂=!l₁◾r α =
    ! (◾unitl _)
    ◾ ! (◾invl _ [2,0,1] _)
    ◾ ◾assoc _ _ _
    ◾ ! _ [1,0,2] α

  -- right cancellation
  refl=r◾!l : {x y : X} → {l r : x == y} → l == r → refl x == r ◾ ! l
  refl=r◾!l α =
    ! (◾invr _)
    ◾ (α [2,0,1] ! _)

  refl=r₁◾r₂◾!l : {x y z : X} → {l : x == z} → {r₁ : x == y} → {r₂ : y == z}
                 → l == r₁ ◾ r₂ → refl x == r₁ ◾ r₂ ◾ ! l
  refl=r₁◾r₂◾!l α =
    ! (◾invr _)
    ◾ (α [2,0,1] ! _)
    ◾ ◾assoc _ _ _ 
  
  l₁=r◾!l₂ : {x y z : X} → {l₁ : x == y} → {l₂ : y == z} → {r : x == z}
            → l₁ ◾ l₂ == r → l₁ == r ◾ ! l₂
  l₁=r◾!l₂ α =
    ! (◾unitr _)
    ◾ (_ [1,0,2] ! (◾invr _))
    ◾ ! (◾assoc _ _ _)
    ◾ (α [2,0,1] ! _)

  l₁=!l₂ : {x y z : X} → {l₁ : x == y} → {l₂ : y == x}
          → l₁ ◾ l₂ == refl x → l₁ == ! l₂
  l₁=!l₂ α = l₁=r◾!l₂ α ◾ ◾unitl _

  l₁=r₁◾r₂◾!l₂ : {x y y' z : X} → {l₁ : x == y} → {l₂ : y == z}
               → {r₁ : x == y'} → {r₂ : y' == z}
               → l₁ ◾ l₂ == r₁ ◾ r₂ → l₁ == r₁ ◾ r₂ ◾ ! l₂
  l₁=r₁◾r₂◾!l₂ α = l₁=r◾!l₂ α ◾ ◾assoc _ _ _


module _ {ℓ} {X : Type ℓ} where

  ◾cnclr : {x y z : X} → {l₁ : x == y} → {l₂ : y == z}
           → {r₁ : x == y} → {r₂ : y == z}
           → l₂ == r₂ → l₁ ◾ l₂ == r₁ ◾ r₂ → l₁ == r₁
  ◾cnclr {r₁ = r₁} {r₂} α β =
    l₁=r₁◾r₂◾!l₂ β
    ◾ ap (λ γ → r₁ ◾ r₂ ◾ ! γ) α
    ◾ (r₁ [1,0,2] ◾invr _)
    ◾ ◾unitr _


module _ {ℓ} {X : Type ℓ} where

  mirror : {x y : X} → {p q : x == y} → p == q → ! p == ! q
  mirror (refl p) = refl (! p)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where
  
  tpt : (P : X → Type ℓ₂) → {x y : X} → x == y → P x → P y
  tpt P = coe ∘ ap P

  apd : (P : X → Type ℓ₂) → (f : (x : X) → P x)
        → {x y : X} → (p : x == y) → tpt P p (f x) == f y
  apd P f (refl x) = refl (f x)

  apd₂ : (P : X → Type ℓ₂) → (f : (x : X) → P x)
         → {x y : X} → {p q : x == y} → (α : p == q)
         → apd P f p == ap (λ p → tpt P p (f x)) α ◾ apd P f q
  apd₂ P f (refl p) = ! (◾unitl _)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  tpt◾ : {x y z : X} → (p : x == y) → (q : y == z)
         → (ux : P x) → tpt P (p ◾ q) ux == (tpt P q ∘ tpt P p $ ux)
  tpt◾ p q ux = ap (λ γ → coe γ ux) (ap◾ P p q) ◾ coe◾ (ap P p) (ap P q) ux

  tpt∘ : {ℓ₃ : Level} → {Y : Type ℓ₃} → (f : Y → X)
         → {x y : Y} → (p : x == y) → tpt (P ∘ f) p == tpt P (ap f p)
  tpt∘ f (refl x) = refl id

  tpt! : {x y : X} → (p : x == y)
         → (ux : P x) → (uy : P y) → tpt P (! p) uy == ux → tpt P p ux == uy
  tpt! (refl x) ux uy = ! {x = uy} {ux}


module _ {ℓ} where

  tpt-id : {X Y : Type ℓ} → (p : X == Y) → tpt id p == coe p
  tpt-id (refl X) = refl id


module _ {ℓ} {X : Type ℓ} where

  loops : X → Type ℓ
  loops x = x == x

  tpt-loops : {x y : X} → (p : x == y) → (q : loops x)
              → tpt loops p q == ! p ◾ q ◾ p
  tpt-loops (refl x) q = ! (◾unitr _) ◾ ! (◾unitl _)

  tpt=l : (x₀ : X) → {x y : X} → (p : x == y)
          → (q : x₀ == x) → tpt (λ x → x₀ == x) p q == q ◾ p
  tpt=l x₀ (refl x) q = ! (◾unitr _)

  tpt=r : (x₀ : X) → {x y : X} → (p : x == y)
          → (q : x == x₀) → tpt (λ x → x == x₀) p q == ! p ◾ q
  tpt=r x₀ (refl x) q = ! (◾unitl _)


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  paths : (X → Y) → (X → Y) → X → Type ℓ₂
  paths f g x = f x == g x
  
  paths-l : Y → (X → Y) → X → Type ℓ₂
  paths-l y g x = y == g x 

  paths-r : (X → Y) → Y → X → Type ℓ₂
  paths-r f y x = f x == y 

  fib : (X → Y) → Y → Type (ℓ₁ ⊔ ℓ₂)
  fib f y = Σ X (paths-r f y)

  tpt-paths : (f g : X → Y)
              → {x y : X} → (p : x == y) → (q : paths f g x)
              → tpt (paths f g) p q == ! (ap f p) ◾ q ◾ ap g p 
  tpt-paths f g (refl x) q = ! (◾unitr _) ◾ ! (◾unitl _)

  tpt-paths-l : (g : X → Y)
                → {x x' : X} → (p : x == x') → {y : Y} → (q : paths-l y g x)
                → tpt (paths-l y g) p q == q ◾ ap g p 
  tpt-paths-l g (refl x) q = ! (◾unitr _)

  tpt-paths-r : (f : X → Y)
                → {x x' : X} → (p : x == x') → {y : Y} → (q : paths-r f y x)
                → tpt (paths-r f y) p q == ! (ap f p) ◾ q 
  tpt-paths-r f (refl x) q = ! (◾unitl _)


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} where

  tpt→ : (P : X → Type ℓ₂) → (Q : X → Type ℓ₃)
          → {x y : X} → (p : x == y) → (f : P x → Q x)
          → tpt (λ x → P x → Q x) p f == tpt Q p ∘ f ∘ tpt P (! p)
  tpt→ P Q (refl x) f = refl f


module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {P : X → Type ℓ₂} {Q : X → Type ℓ₃} where

  tpt-fib-map : (f : (x : X) → P x → Q x)
                → {x y : X} → (p : x == y) → (ux : P x)
                → tpt Q p (f x ux) == f y (tpt P p ux)
  tpt-fib-map f (refl x) ux = refl (f x ux)   
