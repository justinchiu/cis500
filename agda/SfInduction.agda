module SfInduction where
  open import SfBasics

  andTrueElim1 : ∀ (b c : Bool) → b && c ≡ true → b ≡ true
  andTrueElim1 true c _ = refl
  andTrueElim1 false c eq rewrite eq = refl

  andTrueElim2 : ∀ (b c : Bool) → b && c ≡ true → c ≡ true
  andTrueElim2 b true x = refl
  andTrueElim2 true false eq = eq
  andTrueElim2 false false eq = eq

  cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
  cong f refl = refl
  
  plus0r1 : ∀ (n : ℕ) → n + 0 ≡ n
  plus0r1 Z = refl
  plus0r1 (S n) = cong S (plus0r1 n)

  minusSelf : ∀ (n : ℕ) → n - n ≡ 0
  minusSelf Z = refl
  minusSelf (S n) = minusSelf n

  mult0r : ∀ (n : ℕ) → n * 0 ≡ 0
  mult0r Z = refl
  mult0r (S n) = mult0r n

  plusNSm : ∀ (n m : ℕ) → S (n + m) ≡ n + (S m)
  plusNSm Z m = refl
  plusNSm (S n) m = cong S (plusNSm n m)

  +-comm : ∀ (n m : ℕ) → n + m ≡ m + n
  +-comm Z m = sym (plus0r1 m)
  +-comm (S n) m = trans (cong S (+-comm n m)) (plusNSm m n)

  +-assoc : ∀ (n m p : ℕ) → n + (m + p) ≡ (n + m) + p
  +-assoc Z m p = refl
  +-assoc (S n) m p = cong S (+-assoc n m p)

  double : ℕ → ℕ
  double Z = Z
  double (S n) = S (S (double n))

  double-+ : ∀ (n : ℕ) → double n ≡ n + n
  double-+ Z = refl
  double-+ (S n) rewrite double-+ n = cong S (plusNSm n n)

  -- no need for assert in Agda here, I guess?
  *0+ : ∀ (n m : ℕ) → (0 + n) * m ≡ n * m
  *0+ n m = refl

  +-rearrange : ∀ (n m p q : ℕ) →
    (n + m) + (p + q) ≡ (m + n) + (p + q)
  +-rearrange n m p q rewrite +-comm n m | +-comm p q = refl

  +-swap : ∀ (n m p : ℕ) → n + (m + p) ≡ m + (n + p)
  +-swap n m p = trans (+-assoc n m p) ((sym (trans (+-assoc m n p) (+-rearrange m n 0 p))))

  *mSn : ∀ (m n : ℕ) → m * (S n) ≡ m + (m * n)
  *mSn Z n = refl
  *mSn (S m) n rewrite *mSn m n = cong S (+-swap n m (m * n))

  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  *-comm Z n = sym (mult0r n)
  *-comm (S m) n rewrite *-comm m n = sym (*mSn n m)

  evenThenOdd : ∀ (n : ℕ) → even n ≡ ~ (even (S n))
  evenThenOdd Z = refl
  evenThenOdd (S n) rewrite evenThenOdd n with even (S n)
  ... | true = refl
  ... | false = refl

    
