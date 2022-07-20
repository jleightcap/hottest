{-# OPTIONS --without-K --safe #-}

module week03 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝒰)
                           public

variable i j k : Level

record Σ {A : 𝒰 i} (B : A → 𝒰 j) : 𝒰 (i ⊔ j) where
    constructor
        _,_
    field
        pr₁ : A
        pr₂ : B pr₁
open Σ public
infixr 1 _,_

Sigma : (A : 𝒰 i) (B : A → 𝒰 j) → 𝒰 (i ⊔ j)
Sigma {i} {j} A B = Σ {i} {j} {A} B

syntax Sigma A (λ x → b) = Σ x :- A , b

data _≡_ {A : 𝒰 i} : A → A → 𝒰 i where
    refl : (x : A) → x ≡ x

_×_ : 𝒰 i → 𝒰 j → 𝒰 (i ⊔ j)
A × B = Σ x :- A , B

trans : {A : 𝒰 i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl p) (refl p) = refl p

sym : {A : 𝒰 i} {x y : A} → x ≡ y → y ≡ x
sym (refl x≡y) = refl x≡y

ap : {A : 𝒰 i} {B : 𝒰 j} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x≡y) = refl (f x≡y)

transport : {X : 𝒰 i} (A : X → 𝒰 j)
          → {x y : X} → x ≡ y → A x → A y
transport A (refl x≡y) a = a

is-prop : 𝒰 i → 𝒰 i
is-prop X = (x y : X) → x ≡ y

is-set : 𝒰 i → 𝒰 i
is-set X = (x y : X) → is-prop (x ≡ y)

_≡⟨_⟩_ : {X : 𝒰₀} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {X : 𝒰₀} (x : X) → x ≡ x
x ∎ = refl x

infixr  0 _≡⟨_⟩_
infix   1 _∎

-- 1.1

module _ {A : 𝒰₀} {B : A → 𝒰₀} where
    _~_ : ((x : A) → B x) → ((x : A) → B x) → 𝒰₀
    f ~ g = ∀ x → f x ≡ g x
    infix 0 _~_

    ~-refl : (f : (x : A) → B x) → f ~ f
    ~-refl f x = refl (f x)

    ~-inv : (f g : (x : A) → B x) → (f ~ g) → (g ~ f)
    ~-inv f g f~g x = sym (f~g x)

    ~-concat : (f g h : (x : A) → B x) → (f ~ g) → (g ~ h) → (f ~ h)
    ~-concat f g h f~g g~h x =
        f x     ≡⟨ f~g x ⟩
        g~h x

-- 2.1

_∘_ : {A B : 𝒰₀} {C : B → 𝒰₀}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
g ∘ f = λ x → g (f x)

id : {A : 𝒰₀} → A → A
id x = x

dom : {X Y : 𝒰₀} → (X → Y) → 𝒰₀
dom {X} {Y} f = X

codom : {X Y : 𝒰₀} → (X → Y) → 𝒰₀
codom {X} {Y} f = Y

record is-bijection {A B : 𝒰₀} (f : A → B) : 𝒰₀ where
    constructor
        Inverse
    field
        inverse : B → A
        η : inverse ∘ f ~ id
        ε : f ∘ inverse ~ id

is-bijection' : {A B : 𝒰₀} → (A → B) → 𝒰₀
is-bijection' f = Σ inverse :- (codom f → dom f) , ((inverse ∘ f ~ id) × (f ∘ inverse ~ id))

record _≅_ (A B : 𝒰₀) : 𝒰₀ where
    constructor
        Isomorphism
    field
        bijection : A → B
        bijectivity : is-bijection bijection

_≅'_ : (A B : 𝒰₀) → 𝒰₀
A ≅' B = Σ bijection :- (A → B) , is-bijection' bijection

-- 2.2

data 𝟚 : 𝒰₀ where
    𝟘 𝟙 : 𝟚

data 𝔹 : 𝒰₀ where
    tt ff : 𝔹

data ⊥ : 𝒰₀ where

data ⊤ : 𝒰₀ where
    ⋆ : ⊤

𝔹-𝟚-isomorphism : 𝔹 ≅ 𝟚
𝔹-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
    where
        f : 𝔹 → 𝟚
        f ff = 𝟘
        f tt = 𝟙

        g : 𝟚 → 𝔹
        g 𝟘 = ff
        g 𝟙 = tt

        g∘f : (g ∘ f) ~ id
        g∘f ff = refl ff
        g∘f tt = refl tt

        f∘g : f ∘ g ~ id
        f∘g 𝟘 = refl 𝟘
        f∘g 𝟙 = refl 𝟙

        f-is-bijection : is-bijection f
        f-is-bijection = record { inverse = g ; η = g∘f ; ε = f∘g }

-- 3.1

data _+_ (A B : 𝒰₀) : 𝒰₀ where
    inl : A → A + B
    inr : B → A + B

data ℕ : 𝒰₀ where
    zero : ℕ
    succ : ℕ → ℕ

data Fin : ℕ → 𝒰₀ where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → Fin n → Fin (succ n)

Fin-elim : (A : {n : ℕ} → Fin n → 𝒰₀)
         → ({n : ℕ} → A {succ n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (succ k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
    where
        h : {n : ℕ} (k : Fin n) → A k
        h zero = a
        h (succ k) = f k (h k)

-- 3.2

Fin' : ℕ → 𝒰₀
Fin' zero = ⊥
Fin' (succ f) = ⊤ + Fin' f

zero' : {n : ℕ} → Fin' (succ n)
zero' = inl ⋆

succ' : {n : ℕ} → Fin' n → Fin' (succ n)
succ' n = inr n

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
    where
        f : (n : ℕ) → Fin n → Fin' n
        f (succ n) zero = zero'
        f (succ n) (succ fn) = succ' (f n fn)

        g : (n : ℕ) → Fin' n → Fin n
        g (succ n) (inl ⋆) = zero
        g (succ n) (inr fn') = succ (g n fn')

        g∘f : (n : ℕ) → g n ∘ f n ~ id
        g∘f (succ n) zero = refl zero
        g∘f (succ n) (succ fn) = γ
            where
                IH : g n (f n fn) ≡ fn
                IH = g∘f n fn

                γ = g (succ n) (f (succ n) (succ fn))   ≡⟨ refl _ ⟩
                    g (succ n) (succ' (f n fn))         ≡⟨ refl _ ⟩
                    succ (g n (f n fn))                 ≡⟨ ap succ IH ⟩
                    succ fn                             ∎

        f∘g : (n : ℕ) → f n ∘ g n ~ id
        f∘g (succ n) (inl ⋆) = refl (inl ⋆)
        f∘g (succ n) (inr fn) = γ
            where
                IH : f n (g n fn) ≡ fn
                IH = f∘g n fn

                γ = f (succ n) (g (succ n) (succ' fn))  ≡⟨ refl _ ⟩
                    f (succ n) (succ (g n fn))          ≡⟨ refl _ ⟩
                    succ' (f n (g n fn))                ≡⟨ ap succ' IH ⟩
                    succ' fn                            ∎

        f-is-bijection : (n : ℕ) → is-bijection (f n)
        f-is-bijection n = record { inverse = g n ; η = g∘f n ; ε = f∘g n }

-- 4.1

_≤₁_ : ℕ → ℕ → 𝒰₀
zero ≤₁ b = ⊤
succ a ≤₁ zero = ⊥
succ a ≤₁ succ b = a ≤₁ b

-- 4.2

-- "Given a type family P over the naturals, a lower bound n is a natural number such that for all other naturals m, we
-- have that if P(m) holds, then n ≤₁ m"

is-lower-bound : (P : ℕ → 𝒰₀) (n : ℕ) → 𝒰₀
is-lower-bound P n = (m : ℕ) → P m → n ≤₁ m

minimal-element : (P : ℕ → 𝒰₀) → 𝒰₀
minimal-element P = Σ n :- ℕ , (P n × is-lower-bound P n)

-- 4.3

leq-zero : (n : ℕ) → zero ≤₁ n
leq-zero n = ⋆
