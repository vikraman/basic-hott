{-# OPTIONS --without-K #-}
module NoahsGenerators where

open import UnivalentTypeTheory
open import Surjections
open import PropositionalTruncation
open import SetTruncation


module _ {ℓ} where

  Ω : (X : Type ℓ) → X → Type ℓ
  Ω X x = x == x 

  id¹ : {X : Type ℓ} → {x : X} → Ω X x
  id¹ {x = x} = refl x

  Ω² : (X : Type ℓ) → X → Type ℓ
  Ω² X x = Ω (Ω X x) id¹

  id² : {X : Type ℓ} → {x : X} → Ω² X x
  id² {x = x} = refl id¹

  Ω³ : (X : Type ℓ) → X → Type ℓ
  Ω³ X x = Ω (Ω² X x) id²

  id³ : {X : Type ℓ} → {x : X} → Ω³ X x
  id³ {x = x} = refl id²

  Ω⁴ : (X : Type ℓ) → X → Type ℓ
  Ω⁴ X x = Ω (Ω³ X x) id³

  id⁴ : {X : Type ℓ} → {x : X} → Ω⁴ X x
  id⁴ {x = x} = refl id³


module _ {ℓ} where

  2-loop-unitr : {X : Type ℓ} → {x : X} → (α : Ω² X x)
                 → α [2,0,2] id² == α
  2-loop-unitr α = ◾unitr _ ◾ ◾unitl _ ◾ ◾unitr _

  2-loop-refl-comm-h : {X : Type ℓ} → {x : X} → (α : Ω² X x)
                       → α [2,0,2] id² == id² [2,0,2] α
  2-loop-refl-comm-h α = ◾unitr _ ◾ ! (◾unitl _)

  2-loop-refl-comm-v : {X : Type ℓ} → {x : X} → (α : Ω² X x)
                       → α ◾ id² == id² ◾ α
  2-loop-refl-comm-v α = ◾unitr α ◾ ! (◾unitl α)

  2,1-interchange : {X : Type ℓ} → {x y z : X}
                    → {p q r : x == y} → (α : p == q) → (β : q == r)
                    → {s t u : y == z} → (γ : s == t) → (δ : t == u)
                    → (α ◾ β) [2,0,2] (γ ◾ δ) == (α [2,0,2] γ) ◾ (β [2,0,2] δ)
  2,1-interchange = {!!}

  EH+ : {X : Type ℓ} → {x : X} → (α β : Ω² X x)
         → (α ◾ β) == (β ◾ α)
  EH+ α β = ! (2-loop-unitr (α ◾ β))
            ◾ 2,1-interchange α β id² id²
            ◾ ((α [2,0,2] id²) [2,1,3] 2-loop-refl-comm-h β)
            ◾ ! (2,1-interchange α id² id² β)
            ◾ (2-loop-refl-comm-v α [3,0,3] ! (2-loop-refl-comm-v β))
            ◾ 2,1-interchange id² α β id²
            ◾ (! (2-loop-refl-comm-h β) [3,1,2] (α [2,0,2] id²))
            ◾ ! (2,1-interchange β α id² id²)
            ◾ 2-loop-unitr (β ◾ α)
  
  EH- : (X : Type ℓ) → (x : X) → (α β : Ω² X x) → α ◾ β == β ◾ α
  EH- = {!!}
  
