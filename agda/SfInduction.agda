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
  +-comm (S n) m = {!!}

  
