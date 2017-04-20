{-# OPTIONS --without-K #-}
module TwoUniverse where

open import UnivalentTypeTheory
open import PropositionalTruncation
open import OneTypes

is-type : ∀ {ℓ} (T : Type ℓ) → _
is-type T = λ X → ∥ X == T ∥

is-𝟚 = is-type 𝟚

U[𝟚] : Type₁
U[𝟚] = Σ Type₀ is-𝟚

El[𝟚] : U[𝟚] → Type₀
El[𝟚] X = 𝟚

Ũ = Σ U[𝟚] El[𝟚]

-- Labels for some of the pertinent terms
`𝟚 : U[𝟚]
`𝟚 = (𝟚 , ∣ refl 𝟚 ∣)

`id : `𝟚 == `𝟚
`id = dpair= (refl 𝟚 , identify _ _)

`not : `𝟚 == `𝟚
`not = dpair= (ua not-eqv , identify _ _)

not∘not=id : not ∘ not == id
not∘not=id = funext λ { 0₂ → refl 0₂ ; 1₂ → refl 1₂ }

note●note=ide : not-eqv ● not-eqv == ide 𝟚
note●note=ide = eqv= not∘not=id

notp◾notp=refl : ua not-eqv ◾ ua not-eqv == refl 𝟚
notp◾notp=refl = ! (ua-● not-eqv not-eqv)
               ◾ ap ua note●note=ide
               ◾ ua-ide 𝟚

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  tpt◾↓ : {x y z : X} {u : P x} {v : P y} {w : P z}
        → (p : x == y) (r : tpt P p u == v)
        → (q : y == z) (s : tpt P q v == w)
        → tpt P (p ◾ q) u == w
  tpt◾↓ (refl x) (refl p) (refl .x) (refl .p) = refl p

  dpair=◾ : {x y z : X} {u : P x} {v : P y} {w : P z}
          → (p : x == y) (r : tpt P p u == v)
          → (q : y == z) (s : tpt P q v == w)
          → dpair= (p , r) ◾ dpair= (q , s) == dpair= (p ◾ q , tpt◾↓ p r q s)
  dpair=◾ (refl x) (refl p) (refl .x) (refl .p) = refl (refl (x , p))


`ρ : `not ◾ `not == `id
`ρ = dpair=◾ (ua not-eqv) (identify _ _) (ua not-eqv) (identify _ _)
     ◾ ap dpair= (dpair= (notp◾notp=refl , prop-is-set identify _ _ _ _))

module _ {ℓ} {X : Type ℓ} where

  -- General lemma about identity under truncation (migrate up)
  ∥dpair=∥ : (P : (x : X) → Type ℓ) → ((x : X) → is-prop (P x))
         → {x x' : X} → (y : P x) → (y' : P x')
         → ∥ x == x' ∥ → ∥ (x , y) == (x' , y') ∥
  ∥dpair=∥ P φ {x} {x'} y y' = indTrunc _ f (λ p → identify)
    where f : x == x' → ∥ (x , y) == (x' , y') ∥
          f p = ∣ dpair= (p , φ x' (tpt P p y) y') ∣

module ComputationalProperties where

  coe[𝟚] : (p : `𝟚 == `𝟚) → El[𝟚] `𝟚 → El[𝟚] `𝟚
  coe[𝟚] = tpt El[𝟚]

  `id-β : (x : El[𝟚] `𝟚) → coe[𝟚] `id x == x
  `id-β x = ap (λ p → coe[𝟚] p x) dpair≡
    where dpair≡ : dpair= (refl 𝟚 , identify _ _) == refl (𝟚 , ∣ (refl 𝟚) ∣)
          dpair≡ = ap (λ p → dpair= (refl 𝟚 , p)) (prop-is-set identify _ _ _ _)

  `not-β : (x : El[𝟚] `𝟚) → coe[𝟚] `not x == not x
  `not-β 0₂ = {!!}
  `not-β 1₂ = {!!}

module ZeroDimensionalTerms where

  -- TODO: generalize to any singleton subuniverse (trivial)
  sing-path-conn : (x : U[𝟚]) → ∥ x == `𝟚 ∥
  sing-path-conn (X , p) = ∥dpair=∥ is-𝟚 (λ p → identify) p ∣ refl 𝟚 ∣ p

module EquivBool where

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with=_ : (y : A) → x == y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with= (refl x)

  φ-𝟘 : (f : 𝟚 → 𝟚) → (e : is-equiv f)
        → Σ 𝟚 (λ b → (f 0₂ == b) × (f 1₂ == b)) → 𝟘
  φ-𝟘 f (g , η , ε , τ) (b , (p , q)) = 0₂≠1₂ (! (η 0₂) ◾ ap g (p ◾ ! q) ◾ η 1₂)
  
  φ : (f : 𝟚 → 𝟚) → (e : is-equiv f) → (f == id) + (f == not)
  φ f e with inspect (f 0₂) | inspect (f 1₂)
  φ f e        | 0₂ with= p | 0₂ with= q = rec𝟘 _ (φ-𝟘 f e (0₂ , (p , q)))
  φ f e        | 0₂ with= p | 1₂ with= q = i₁ (funext (ind𝟚 _ p q)) 
  φ f e        | 1₂ with= p | 0₂ with= q = i₂ (funext (ind𝟚 _ p q))
  φ f e        | 1₂ with= p | 1₂ with= q = rec𝟘 _ (φ-𝟘 f e (1₂ , (p , q)))

  ψ : {f : 𝟚 → 𝟚} → {e : is-equiv f}
      → (f == id) + (f == not) → ((f , e) == ide 𝟚) + ((f , e) == not-eqv)
  ψ (i₁ p) = i₁ (eqv= p)
  ψ (i₂ p) = i₂ (eqv= p)

  all-eqvs : (e : 𝟚 ≃ 𝟚) → (e == ide 𝟚) + (e == not-eqv)
  all-eqvs (f , e') = ψ (φ f e')


-- The claims below follow from all-eqvs (1-dim) and Aut𝟚-is-set
-- (2-dim) and general stuff like ∥dpair=∥ and ΩBAut≃Aut from
-- UniFibExamples

module OneDimensionalTerms where

  all-1-paths : (p : `𝟚 == `𝟚) → (p == `id) + (p == `not)
  all-1-paths p = {!!}

module TwoDimensionalTerms where

  all-2-paths-id : (u : `id == `id) → u == refl `id
  all-2-paths-id = {!!}

  all-2-paths-not : (u : `not == `not) → u == refl `not
  all-2-paths-not = {!!}
