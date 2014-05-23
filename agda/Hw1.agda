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

  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  testNextWeekday : nextWeekday (nextWeekday Saturday) ≡ Tuesday
  testNextWeekday = refl

  data Bool : Set where
    True  : Bool
    False : Bool

  ¬ : Bool → Bool
  ¬ True = False
  ¬ False = True

  _∧_ : Bool → Bool → Bool
  True  ∧ b  = b
  False ∧ _ = False

  _∨_ : Bool → Bool → Bool
  True  ∨ _ = True
  False ∨ b = b

  testOr1 : _∨_ True False ≡ True
  testOr1 = refl
  
  testOr2 : _∨_ False False ≡ False
  testOr2 = refl
  
  nAndB : Bool → Bool → Bool
  nAndB True True = False
  nAndB _    _    = True

  -- Exercise 1: 1 star (andb3)
  andB3 : Bool → Bool → Bool → Bool
  andB3 True True True = True
  andB3 _    _    _    = False

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
  even Z          = True
  even (S Z)      = False
  even (S (S n))  = even n

  odd : ℕ → Bool
  odd x = ¬ (even x)

  _+_ : ℕ → ℕ → ℕ
  Z     + m = m
  (S n) + m = S (n + m)

  _*_ : ℕ → ℕ → ℕ
  Z     * _ = Z
  (S n) * m = m + (n * m)

  {-# BUILTIN NATURAL ℕ #-}
  {-# BUILTIN ZERO Z #-}
  {-# BUILTIN SUC S #-}

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
  Z     == Z     = True
  (S n) == (S m) = n == m
  _     == _     = False

  _<_ : ℕ → ℕ → Bool
  Z     < (S _) = True
  _     < Z     = False
  (S n) < (S m) = n < m

  _>_ : ℕ → ℕ → Bool
  Z     > _     = False
  (S _) > Z     = True
  (S n) > (S m) = n > m

  _≤_ : ℕ → ℕ → Bool
  n ≤ m = (n == m) ∨ (n < m)

  _≥_ : ℕ → ℕ → Bool
  n ≥ m = (n == m) ∨ (n > m)

  leqCheck : (Z ≤ (S Z)) ≡ True
  leqCheck = refl

  plus0n : ∀ {n : ℕ} → (Z + n) ≡ n
  plus0n = λ {n} → refl
  
  plus1n : ∀ {n : ℕ} → (1 + n) ≡ (S n)
  plus1n = λ {n} → refl

  mult0n : ∀ {n : ℕ} → (Z * n) ≡ Z
  mult0n = λ {n} → refl

  plusId : ∀ {n m : ℕ} → n ≡ m → (n + n) ≡ (m + m)
  plusId .a .a (refl a) = refl a

  plusId3 : ∀ {n m o : ℕ} → n ≡ m → m ≡ o → (n + m) ≡ (m + o)
  plusId3 refl refl = refl

  mult0Plus : ∀ {n m : ℕ} → ((0 + n) * m) ≡ (n * m)
  mult0Plus = λ {n} {m} → refl

  mult1Plus : ∀ {n m : ℕ} → ((1 + n) * m) ≡ (m + (n * m))
  mult1Plus = λ {n} {m} → refl

  plus1Neq0 : ∀ {n : ℕ} → ((S n) == 0) ≡ False
  plus1Neq0 = λ {n} → refl
