{-# OPTIONS --without-K #-}

module EH where

open import UnivalentTypeTheory

module _ {ℓ} where

  1-Paths : {A : Type ℓ} → (a b : A) → Type _
  1-Paths a b = a == b

  2-Paths : {A : Type ℓ} → {a b : A} (p q : 1-Paths a b) → Type _
  2-Paths p q = p == q

  3-Paths : {A : Type ℓ} → {a b : A} {p q : 1-Paths a b} (u v : 2-Paths p q) → Type _
  3-Paths u v = u == v

module _ {ℓ} where

  Ω : {A : Type ℓ} (a : A) → Type _
  Ω a = 1-Paths a a

  Ω² : {A : Type ℓ} → (a : A) → Type _
  Ω² a = 2-Paths (refl a) (refl a)

  Ω³ : {A : Type ℓ} → (a : A) → Type _
  Ω³ a = 3-Paths (refl (refl a)) (refl (refl a))

∙Type : ∀ ℓ → Type _
∙Type ℓ = Σ (Type ℓ) (λ A → A)

∙Type₀ = ∙Type lzero

module _ {ℓ} where

  Ω∙ : ∙Type ℓ → ∙Type ℓ
  Ω∙ (A , a) = (a == a) , refl a

  Ω∙[_,_] : ℕ → ∙Type ℓ → ∙Type ℓ
  Ω∙[ zero , (A , a) ] = Ω∙ (A , a)
  Ω∙[ succ n , (A , a) ] = Ω∙ Ω∙[ n , (A , a) ]

  Ω[_,_] : ℕ → ∙Type ℓ → Type ℓ
  Ω[ n , (A , a) ] = p₁ Ω∙[ n , (A , a) ]

module whiskering {ℓ} {A : Type ℓ} {y z : A} {p q : 1-Paths y z} where

  _∘ᵣ_ : {w : A} → (α : 2-Paths p q) (r : 1-Paths z w) → p ◾ r == q ◾ r
  α ∘ᵣ (refl _) = ◾unitr p ◾ α ◾ ! (◾unitr q)

  _∘ₗ_ : {x : A} → (r : 1-Paths x y) (α : 2-Paths p q) → r ◾ p == r ◾ q
  (refl _) ∘ₗ α = ◾unitl p ◾ α ◾ ! (◾unitl q)

open whiskering

module horizontal {ℓ} {A : Type ℓ} {x y z : A} {p q : 1-Paths x y} {r s : 1-Paths y z} where

  _*_ : (α : p == q) (β : r == s) → p ◾ r == q ◾ s
  α * β = (α ∘ᵣ r) ◾ (q ∘ₗ β)

  _*'_ : (α : p == q) (β : r == s) → p ◾ r == q ◾ s
  α *' β = (p ∘ₗ β) ◾ (α ∘ᵣ s)

open horizontal


module lemmas {ℓ} {A : Type ℓ} {a : A} where

  α∘ᵣrefl≡α : (α : refl a == refl a) → (α ∘ᵣ refl a) == α
  α∘ᵣrefl≡α α = ◾unitl (α ◾ refl (refl a))
              ◾ ◾unitr α

  refl∘ₗβ≡β : (β : refl a == refl a) → (refl a ∘ₗ β) == β
  refl∘ₗβ≡β β = ◾unitl (β ◾ refl (refl a))
              ◾ ◾unitr β

  α*β≡α◾β : (α β : Ω² a) → (α * β) == (α ◾ β)
  α*β≡α◾β α β = ap (λ p → p ◾ (refl a ∘ₗ β)) (α∘ᵣrefl≡α α)
              ◾ ap (λ p → α ◾ p) (refl∘ₗβ≡β β)

  α*'β≡β◾α : (α β : Ω² a) → (α *' β) == (β ◾ α)
  α*'β≡β◾α α β = ap (λ p → (refl a ∘ₗ β) ◾ p) (α∘ᵣrefl≡α α)
               ◾ ap (λ p → p  ◾ α) (refl∘ₗβ≡β β)

  *≡*' : {p q : Ω a} → (α : p == refl a) (β : refl a == q) → (α * β) == (α *' β)
  *≡*' (refl ._) (refl ._) = refl (refl (refl a))

  *'≡* : {p q : Ω a} → (α : p == refl a) (β : refl a == q) → (α *' β) == (α * β)
  *'≡* (refl ._) (refl ._) = refl (refl (refl a))

open lemmas

module _ {ℓ} {A : Type ℓ} {a : A} where

  eckmann-hilton-2 : (α β : Ω² a) → α ◾ β == β ◾ α
  eckmann-hilton-2 α β = ! (α*β≡α◾β α β) ◾ *≡*' α β ◾ α*'β≡β◾α α β

  eckmann-hilton-2' : (α β : Ω² a) → α ◾ β == β ◾ α
  eckmann-hilton-2' α β = ! (α*'β≡β◾α β α) ◾ *'≡* β α ◾ α*β≡α◾β β α

  eckmann-hilton-2-lem : (α β : Ω² a) → eckmann-hilton-2 α β == eckmann-hilton-2' α β → 𝟘
  eckmann-hilton-2-lem α β p = {!!}

  eckmann-hilton-3 : (α β : Ω³ a) → α ◾ β == β ◾ α
  eckmann-hilton-3 α β = ! (α*β≡α◾β α β) ◾ *≡*' α β ◾ α*'β≡β◾α α β

  eckmann-hilton-3' : (α β : Ω³ a) → α ◾ β == β ◾ α
  eckmann-hilton-3' α β = ! (α*'β≡β◾α β α) ◾ *'≡* β α ◾ α*β≡α◾β β α

  eckmann-hilton-3-lem : (α β : Ω³ a) → eckmann-hilton-3 α β == eckmann-hilton-3' α β
  eckmann-hilton-3-lem α β = {!!}
