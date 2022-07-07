{-# OPTIONS --without-K --safe #-}

module Week01 where

Type = Set

data _≡_ { A : Type } : A → A → Type where
    refl : {a : A} → a ≡ a
infix 0 _≡_

data 𝟘 : Type where

data 𝟙 : Type where
    ⋆ : 𝟙

data 𝟚 : Type where
    tt ff : 𝟚

data ℕ : Type where
    zero : ℕ
    succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data List ( A : Type ) : Type where
    [] : List A
    _∷_ : A → List A → List A
infixr 10 _∷_

if_then_else_ : { A : Type } → 𝟚 → A → A → A
if tt then tb else _ = tb
if ff then _ else fb = fb

-- 1.1
_∧_ : 𝟚 → 𝟚 → 𝟚
tt ∧ b = b
ff ∧ b = ff

_∧²_ : 𝟚 → 𝟚 → 𝟚
ff ∧² ff = ff
ff ∧² tt = ff
tt ∧² ff = ff
tt ∧² tt = tt

-- 1.2
¬ : 𝟚 → 𝟚
¬ tt = ff
¬ ff = tt

_⊕_ : 𝟚 → 𝟚 → 𝟚
tt ⊕ b = ¬ b
ff ⊕ b = b

-- 1.3
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)
infixr 20  _+_

private
    +-example : 3 + 4 ≡ 7
    +-example = refl

_×_ : ℕ → ℕ → ℕ
zero × b = zero
succ a × b = b + (a × b)
infixr 30 _×_

private
    ×-example : 3 × 4 ≡ 12
    ×-example = refl

_^_ : ℕ → ℕ → ℕ
a ^ zero = succ zero
a ^ succ b = a × (a ^ b)
infixr 40 _^_

private
    ^-example : 3 ^ 4 ≡ 81
    ^-example = refl

_! : ℕ → ℕ
zero ! = succ zero
succ a ! = (succ a) × (a !)
infixr 50 _!

private
    !-example : 4 ! ≡ 24
    !-example = refl

-- 1.4
max : ℕ → ℕ → ℕ
max zero b = b
max (succ a) zero = succ a
max (succ a) (succ b) = succ (max a b)

private
    max-example : max 3 5 ≡ 5
    max-example = refl

min : ℕ → ℕ → ℕ
min zero b = zero
min (succ a) zero = zero
min (succ a) (succ b) = succ (min a b)

private
    min-example : min 3 5 ≡ 3
    min-example = refl

-- 1.5
map : { X Y : Type } → (X → Y) → List X → List Y
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

private
    map-example : map (_+ 3) (1 ∷ 2 ∷ 3 ∷ []) ≡ 4 ∷ 5 ∷ 6 ∷ []
    map-example = refl

-- 1.6
filter : { X : Type } ( p : X → 𝟚 ) → List X → List X
filter p [] = []
filter p (x ∷ xs) = if p x then (x ∷ rest) else rest
  where
    rest = filter p xs

_≠_ : ℕ → ℕ → 𝟚
zero ≠ zero = ff
zero ≠ succ b = tt
succ a ≠ zero = tt
succ a ≠ succ b = a ≠ b

private
    filter-example : filter (0 ≠_) (2 ∷ 1 ∷ 0 ∷ 1 ∷ []) ≡ 2 ∷ 1 ∷ 1 ∷ []
    filter-example = refl

-- 2.1
_≣_ : 𝟚 → 𝟚 → Type
ff ≣ ff = 𝟙
ff ≣ tt = 𝟘
tt ≣ ff = 𝟘
tt ≣ tt = 𝟙
infix 0 _≣_

-- 2.2
𝟚-refl : ( b : 𝟚 ) → b ≣ b
𝟚-refl tt = ⋆
𝟚-refl ff = ⋆

-- 2.3
≡-to-≣ : ( a b : 𝟚 ) → a ≡ a → a ≣ a
≡-to-≣ tt b p = ⋆
≡-to-≣ ff b p = ⋆

≣-to-≡ : ( a b : 𝟚 ) → a ≣ a → a ≡ a
≣-to-≡ tt b p = refl
≣-to-≡ ff b p = refl

-- 3.1
¬-invo : ( b : 𝟚 ) → ¬ (¬ b) ≡ b
¬-invo tt = refl
¬-invo ff = refl

_∨_ : 𝟚 → 𝟚 → 𝟚
ff ∨ b = b
tt ∨ _ = tt

∨-comm : ( a b : 𝟚 ) → a ∨ b ≡ b ∨ a
∨-comm ff ff = refl
∨-comm ff tt = refl
∨-comm tt ff = refl
∨-comm tt tt = refl

-- 3.2
∧-comm : ( a b : 𝟚 ) → a ∧ b ≡ b ∧ a
∧-comm ff ff = refl
∧-comm ff tt = refl
∧-comm tt ff = refl
∧-comm tt tt = refl

-- 3.3
∧-assoc : ( a b c : 𝟚 ) → a ∧ (b ∧ c) ≡ (a ∧ b) ∧ c
∧-assoc tt b c = refl
∧-assoc ff b c = refl

∧²-asoc : ( a b c : 𝟚 ) → a ∧² (b ∧² c) ≡ (a ∧² b) ∧ c
∧²-asoc ff ff ff = refl
∧²-asoc ff ff tt = refl
∧²-asoc ff tt ff = refl
∧²-asoc ff tt tt = refl
∧²-asoc tt ff ff = refl
∧²-asoc tt ff tt = refl
∧²-asoc tt tt ff = refl
∧²-asoc tt tt tt = refl

-- 3.4
ap : { A B : Type } ( f : A → B ) { x y : A } → x ≡ y → f x ≡ f y
ap f refl = refl

min-comm : ( n m : ℕ ) → min n m ≡ min m n
min-comm zero zero = refl
min-comm zero (succ m) = refl
min-comm (succ n) zero = refl
min-comm (succ n) (succ m) = ap succ induct
  where
    induct : min n m ≡ min m n
    induct = min-comm n m

-- 3.5
+-identr : ( n : ℕ ) → n ≡ n + 0
+-identr zero = refl
+-identr (succ n) = ap succ induct
  where
    induct : n ≡ n + 0
    induct = +-identr n

-- 3.6
id : { X : Type } → X → X
id x = x

map-id : { X : Type } ( xs : List X ) → map id xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = ap (x ∷_) induct
  where
    induct : map id xs ≡ xs
    induct = map-id xs

_∘_ : { X Y Z : Type } → (Y → Z) → (X → Y) → X → Z
g ∘ f = λ x → g (f x)

map-comp : { X Y Z : Type } ( g : Y → Z ) ( f : X → Y ) ( xs : List X )
         → map (g ∘ f) xs ≡ map g (map f xs)
map-comp g f [] = refl
map-comp g f (x ∷ xs) = ap ((g ∘ f) x ∷_) induct
  where
    induct : map (g ∘ f) xs ≡ map g (map f xs)
    induct = map-comp g f xs
