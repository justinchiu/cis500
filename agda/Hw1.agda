module Hw1 where
  open import Level

  data Day : Set where
    Monday Tuesday Wednesday Thursday Friday Saturday Sunday : Day

  nextWeekday : Day → Day
  nextWeekday Monday    = Tuesday
  nextWeekday Tuesday   = Wednesday
  nextWeekday Wednesday = Thursday
  nextWeekday Thursday  = Friday
  nextWeekday Friday    = Saturday
  nextWeekday Saturday  = Monday
  nextWeekday Sunday    = Monday

  infix 4 _≡_
  data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL    refl #-}

  testNextWeekday : nextWeekday (nextWeekday Saturday) ≡ Tuesday
  testNextWeekday = refl

  data ⊥ : Set where
  record ⊤ : Set where

  trivial : ⊤
  trivial = record {}

  data Bool : Set where
    true  : Bool
    false : Bool

  ~ : Bool → Bool
  ~ true = false
  ~ false = true

  _&&_ : Bool → Bool → Bool
  true  && b  = b
  false && _ = false

  _||_ : Bool → Bool → Bool
  true  || _ = true
  false || b = b

  testOr1 : _||_ true false ≡ true
  testOr1 = refl
  
  testOr2 : _&&_ false false ≡ false
  testOr2 = refl
  
  _nand_ : Bool → Bool → Bool
  true nand true = false
  _    nand _    = true

  -- Exercise 1: 1 star (andb3)
  andB3 : Bool → Bool → Bool → Bool
  andB3 true true true = true
  andB3 _    _    _    = false

  data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ

  pred : ℕ → ℕ
  pred Z     = Z
  pred (S n) = n

  minusTwo : ℕ → ℕ
  minusTwo Z         = Z
  minusTwo (S Z)     = Z
  minusTwo (S (S n)) = n

  even : ℕ → Bool
  even Z          = true
  even (S Z)      = false
  even (S (S n))  = even n

  odd : ℕ → Bool
  odd x = ~ (even x)

  _+_ : ℕ → ℕ → ℕ
  Z     + m = m
  (S n) + m = S (n + m)

  _*_ : ℕ → ℕ → ℕ
  Z     * _ = Z
  (S n) * m = m + (n * m)

  {-# BUILTIN NATURAL ℕ #-}
  
  check3 : 3 ≡ S (S (S Z))
  check3 = refl

  _-_ : ℕ → ℕ → ℕ
  Z     - m     = Z
  n     - Z     = n
  (S n) - (S m) = n - m

  _^_ : ℕ → ℕ → ℕ
  Z ^ _     = Z
  n ^ Z     = S Z
  n ^ (S m) = n * (n ^ m)

  _! : ℕ → ℕ
  Z     ! = 1
  (S n) ! = (S n) * n !

  _==_ : ℕ → ℕ → Bool
  Z     == Z     = true
  (S n) == (S m) = n == m
  _     == _     = false

  _<_ : ℕ → ℕ → Bool
  Z     < (S _) = true
  _     < Z     = false
  (S n) < (S m) = n < m

  _>_ : ℕ → ℕ → Bool
  Z     > _     = false
  (S _) > Z     = true
  (S n) > (S m) = n > m

  _≤_ : ℕ → ℕ → Bool
  n ≤ m = (n == m) || (n < m)

  _≥_ : ℕ → ℕ → Bool
  n ≥ m = (n == m) || (n > m)

  leqCheck : (Z ≤ (S Z)) ≡ true
  leqCheck = refl

  plus0n : ∀ {n : ℕ} → (Z + n) ≡ n
  plus0n = λ {n} → refl
  
  plus1n : ∀ {n : ℕ} → (1 + n) ≡ (S n)
  plus1n = λ {n} → refl

  mult0n : ∀ {n : ℕ} → (Z * n) ≡ Z
  mult0n = λ {n} → refl

  plusId : ∀ {n m : ℕ} → n ≡ m → (n + n) ≡ (m + m)
  plusId refl = refl

  plusId3 : ∀ {n m o : ℕ} → n ≡ m → m ≡ o → (n + m) ≡ (m + o)
  plusId3 refl refl = refl

  mult0Plus : ∀ {n m : ℕ} → ((0 + n) * m) ≡ (n * m)
  mult0Plus = λ {n} {m} → refl

  mult1Plus : ∀ {n m : ℕ} → ((1 + n) * m) ≡ (m + (n * m))
  mult1Plus = λ {n} {m} → refl

  plus1Neq0 : ∀ {n : ℕ} → ((S n) == 0) ≡ false
  plus1Neq0 = λ {n} → refl

  negInvolutive : ∀ {b : Bool} → ~ (~ b) ≡ b
  negInvolutive {true}  = refl
  negInvolutive {false} = refl

  zeroℕEqPlusOne : ∀ {n : ℕ} → (0 == (n + 1)) ≡ false
  zeroℕEqPlusOne {Z}   = refl
  zeroℕEqPlusOne {S n} = refl

  if_then_else_ : {A : Set} -> Bool -> A -> A -> A
  if true then x else y = x
  if false then x else y = y

  id : ∀ {x} {T : Set x} → T → T
  id x = x

  trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  identityFnAppliedTwice : ∀ (f : Bool → Bool)
    → (∀ (x : Bool) → (f x) ≡ x)
    → (∀ (b : Bool) → (f (f b)) ≡ b)
  identityFnAppliedTwice f fx b with fx b | fx (f b)
  ... | c₁ | c₂ = trans c₂ c₁

  {-# BUILTIN BOOL Bool #-}

  negationFnAppliedTwice : ∀ (f : Bool → Bool)
    → (∀ (x : Bool) → (f x) ≡ (~ x))
    → (∀ (b : Bool) → (f (f b)) ≡ b)
  negationFnAppliedTwice f fnx b rewrite (fnx b) | fnx (~ b) with b
  ... | true = refl
  ... | false = refl

  sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  andEqOr : ∀ (a b : Bool)
    → (a && b ≡ a || b)
    → a ≡ b
  andEqOr true true eq = refl
  andEqOr true false eq = sym eq
  andEqOr false true eq = eq
  andEqOr false false eq = refl

  data Bin : Set where
    BZ : Bin
    *2 : Bin → Bin
    *2+1 : Bin → Bin

  incr : Bin → Bin
  incr BZ = *2+1 BZ
  incr (*2 b) = *2+1 b
  incr (*2+1 b) = *2 (incr b)

  binToNat : Bin → ℕ
  binToNat BZ = Z
  binToNat (*2 b) = 2 * (binToNat b)
  binToNat (*2+1 b) = 1 + (2 * (binToNat b))

  plus' :  ℕ → ℕ → ℕ
  plus' Z m = m
  plus' (S n) m = S (plus' n m)

  factorialBad : ℕ → ℕ
  factorialBad n with n == Z
  ... | true = 1
  ... | false = n * (factorialBad (n - 1))

  
