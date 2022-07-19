{-# OPTIONS --without-K --safe #-}

module Week02 where

open import Week01

record Σ {A : Type} (B : A → Type) : Type  where
    constructor
        _,_
    field
        pr₁ : A
        pr₂ : B pr₁
open Σ public
infixr 0 _,_

data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B
infixr 20 _+_

_×_ : Type → Type → Type
A × B = Σ {A} (λ _ → B)

¬_ : Type → Type
¬ A = A → 𝟘
infix 1000 ¬_

_⇔_ : Type → Type → Type
A ⇔ B = (A → B) × (B → A)
infix -2 _⇔_

-- 1.1
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry a→b = λ a,b → a→b (pr₁ a,b) (pr₂ a,b)

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry a×b a b = a×b (a , b)

-- 1.2
[i] : {A B C : Type} → (A × B) + C → (A + C) × (B + C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A + B) × C → (A × C) + (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A + B) → ¬ A × ¬ B
pr₁ ([iii] f) a = f (inl a)
pr₂ ([iii] f) b = f (inr b)

-- [iv] non-constructive

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f ¬b = λ a → ¬b (f a)

-- 1.3
tne : ∀ {A : Type} → ¬(¬(¬ A)) → ¬ A
tne ¬¬¬x = λ a → ¬¬¬x (λ ¬x → ¬x a)

-- 1.4
¬¬-functor : {A B : Type} → (A → B) → ¬(¬ A) → ¬(¬ B)
¬¬-functor a→b = [v] ([v] a→b)

¬¬-kleisli : {A B : Type} → (A → ¬(¬ B)) → ¬(¬ A) → ¬(¬ B)
¬¬-kleisli a→¬¬b ¬¬a = tne (¬¬-functor a→¬¬b ¬¬a)

-- 2.1
bool-as-type : 𝟚 → Type
bool-as-type tt = 𝟙
bool-as-type ff = 𝟘

-- 2.2
bool-≡-char₁ : ∀ (b b' : 𝟚) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b b' refl = (λ b → b) , (λ b' → b')

-- 2.3
true≢false₁ : ¬ (tt ≡ ff)
true≢false₁ p = ?

true≢false₂ : ¬ (tt ≡ ff)
true≢false₂ = λ ()

-- 2.4

