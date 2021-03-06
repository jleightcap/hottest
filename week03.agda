{-# OPTIONS --without-K --safe #-}

module week03 where

open import Agda.Primitive using (Level; lzero; lsuc; _โ_)
                           renaming (Set to ๐ฐ)
                           public

variable i j k : Level

record ฮฃ {A : ๐ฐ i} (B : A โ ๐ฐ j) : ๐ฐ (i โ j) where
    constructor
        _,_
    field
        prโ : A
        prโ : B prโ
open ฮฃ public
infixr 1 _,_

Sigma : (A : ๐ฐ i) (B : A โ ๐ฐ j) โ ๐ฐ (i โ j)
Sigma {i} {j} A B = ฮฃ {i} {j} {A} B

syntax Sigma A (ฮป x โ b) = ฮฃ x :- A , b

data _โก_ {A : ๐ฐ i} : A โ A โ ๐ฐ i where
    refl : (x : A) โ x โก x

_ร_ : ๐ฐ i โ ๐ฐ j โ ๐ฐ (i โ j)
A ร B = ฮฃ x :- A , B

trans : {A : ๐ฐ i} {x y z : A} โ x โก y โ y โก z โ x โก z
trans (refl p) (refl p) = refl p

sym : {A : ๐ฐ i} {x y : A} โ x โก y โ y โก x
sym (refl xโกy) = refl xโกy

ap : {A : ๐ฐ i} {B : ๐ฐ j} (f : A โ B) {x y : A} โ x โก y โ f x โก f y
ap f (refl xโกy) = refl (f xโกy)

transport : {X : ๐ฐ i} (A : X โ ๐ฐ j)
          โ {x y : X} โ x โก y โ A x โ A y
transport A (refl xโกy) a = a

is-prop : ๐ฐ i โ ๐ฐ i
is-prop X = (x y : X) โ x โก y

is-set : ๐ฐ i โ ๐ฐ i
is-set X = (x y : X) โ is-prop (x โก y)

_โกโจ_โฉ_ : {X : ๐ฐโ} (x : X) {y z : X} โ x โก y โ y โก z โ x โก z
x โกโจ p โฉ q = trans p q

_โ : {X : ๐ฐโ} (x : X) โ x โก x
x โ = refl x

infixr  0 _โกโจ_โฉ_
infix   1 _โ

-- 1.1

module _ {A : ๐ฐโ} {B : A โ ๐ฐโ} where
    _~_ : ((x : A) โ B x) โ ((x : A) โ B x) โ ๐ฐโ
    f ~ g = โ x โ f x โก g x
    infix 0 _~_

    ~-refl : (f : (x : A) โ B x) โ f ~ f
    ~-refl f x = refl (f x)

    ~-inv : (f g : (x : A) โ B x) โ (f ~ g) โ (g ~ f)
    ~-inv f g f~g x = sym (f~g x)

    ~-concat : (f g h : (x : A) โ B x) โ (f ~ g) โ (g ~ h) โ (f ~ h)
    ~-concat f g h f~g g~h x =
        f x     โกโจ f~g x โฉ
        g~h x

-- 2.1

_โ_ : {A B : ๐ฐโ} {C : B โ ๐ฐโ}
    โ ((y : B) โ C y)
    โ (f : A โ B)
    โ (x : A) โ C (f x)
g โ f = ฮป x โ g (f x)

id : {A : ๐ฐโ} โ A โ A
id x = x

dom : {X Y : ๐ฐโ} โ (X โ Y) โ ๐ฐโ
dom {X} {Y} f = X

codom : {X Y : ๐ฐโ} โ (X โ Y) โ ๐ฐโ
codom {X} {Y} f = Y

record is-bijection {A B : ๐ฐโ} (f : A โ B) : ๐ฐโ where
    constructor
        Inverse
    field
        inverse : B โ A
        ฮท : inverse โ f ~ id
        ฮต : f โ inverse ~ id

is-bijection' : {A B : ๐ฐโ} โ (A โ B) โ ๐ฐโ
is-bijection' f = ฮฃ inverse :- (codom f โ dom f) , ((inverse โ f ~ id) ร (f โ inverse ~ id))

record _โ_ (A B : ๐ฐโ) : ๐ฐโ where
    constructor
        Isomorphism
    field
        bijection : A โ B
        bijectivity : is-bijection bijection

_โ'_ : (A B : ๐ฐโ) โ ๐ฐโ
A โ' B = ฮฃ bijection :- (A โ B) , is-bijection' bijection

-- 2.2

data ๐ : ๐ฐโ where
    ๐ ๐ : ๐

data ๐น : ๐ฐโ where
    tt ff : ๐น

data โฅ : ๐ฐโ where

data โค : ๐ฐโ where
    โ : โค

๐น-๐-isomorphism : ๐น โ ๐
๐น-๐-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
    where
        f : ๐น โ ๐
        f ff = ๐
        f tt = ๐

        g : ๐ โ ๐น
        g ๐ = ff
        g ๐ = tt

        gโf : (g โ f) ~ id
        gโf ff = refl ff
        gโf tt = refl tt

        fโg : f โ g ~ id
        fโg ๐ = refl ๐
        fโg ๐ = refl ๐

        f-is-bijection : is-bijection f
        f-is-bijection = record { inverse = g ; ฮท = gโf ; ฮต = fโg }

-- 3.1

data _+_ (A B : ๐ฐโ) : ๐ฐโ where
    inl : A โ A + B
    inr : B โ A + B

data โ : ๐ฐโ where
    zero : โ
    succ : โ โ โ

data Fin : โ โ ๐ฐโ where
    zero : {n : โ} โ Fin (succ n)
    succ : {n : โ} โ Fin n โ Fin (succ n)

Fin-elim : (A : {n : โ} โ Fin n โ ๐ฐโ)
         โ ({n : โ} โ A {succ n} zero)
         โ ({n : โ} (k : Fin n) โ A k โ A (succ k))
         โ {n : โ} (k : Fin n) โ A k
Fin-elim A a f = h
    where
        h : {n : โ} (k : Fin n) โ A k
        h zero = a
        h (succ k) = f k (h k)

-- 3.2

Fin' : โ โ ๐ฐโ
Fin' zero = โฅ
Fin' (succ f) = โค + Fin' f

zero' : {n : โ} โ Fin' (succ n)
zero' = inl โ

succ' : {n : โ} โ Fin' n โ Fin' (succ n)
succ' n = inr n

Fin-isomorphism : (n : โ) โ Fin n โ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
    where
        f : (n : โ) โ Fin n โ Fin' n
        f (succ n) zero = zero'
        f (succ n) (succ fn) = succ' (f n fn)

        g : (n : โ) โ Fin' n โ Fin n
        g (succ n) (inl โ) = zero
        g (succ n) (inr fn') = succ (g n fn')

        gโf : (n : โ) โ g n โ f n ~ id
        gโf (succ n) zero = refl zero
        gโf (succ n) (succ fn) = ฮณ
            where
                IH : g n (f n fn) โก fn
                IH = gโf n fn

                ฮณ = g (succ n) (f (succ n) (succ fn))   โกโจ refl _ โฉ
                    g (succ n) (succ' (f n fn))         โกโจ refl _ โฉ
                    succ (g n (f n fn))                 โกโจ ap succ IH โฉ
                    succ fn                             โ

        fโg : (n : โ) โ f n โ g n ~ id
        fโg (succ n) (inl โ) = refl (inl โ)
        fโg (succ n) (inr fn) = ฮณ
            where
                IH : f n (g n fn) โก fn
                IH = fโg n fn

                ฮณ = f (succ n) (g (succ n) (succ' fn))  โกโจ refl _ โฉ
                    f (succ n) (succ (g n fn))          โกโจ refl _ โฉ
                    succ' (f n (g n fn))                โกโจ ap succ' IH โฉ
                    succ' fn                            โ

        f-is-bijection : (n : โ) โ is-bijection (f n)
        f-is-bijection n = record { inverse = g n ; ฮท = gโf n ; ฮต = fโg n }

-- 4.1

_โคโ_ : โ โ โ โ ๐ฐโ
zero โคโ b = โค
succ a โคโ zero = โฅ
succ a โคโ succ b = a โคโ b

-- 4.2

-- "Given a type family P over the naturals, a lower bound n is a natural number such that for all other naturals m, we
-- have that if P(m) holds, then n โคโ m"

is-lower-bound : (P : โ โ ๐ฐโ) (n : โ) โ ๐ฐโ
is-lower-bound P n = (m : โ) โ P m โ n โคโ m

minimal-element : (P : โ โ ๐ฐโ) โ ๐ฐโ
minimal-element P = ฮฃ n :- โ , (P n ร is-lower-bound P n)

-- 4.3

leq-zero : (n : โ) โ zero โคโ n
leq-zero n = โ
