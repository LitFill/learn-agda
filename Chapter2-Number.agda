module Chapter2-Number where

import Chapter1-Hello

module Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)

  one = suc zero
  two = suc one
  three = suc two
  four = suc three

  open Chapter1-Hello 
    using (Bool; true; false)

  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false

  n=2? : ℕ → Bool
  n=2? zero = false
  n=2? (suc zero) = false
  n=2? (suc (suc zero)) = true
  n=2? (suc (suc (suc x))) = false

  n=2?' : ℕ → Bool
  n=2?' (suc (suc zero)) = true
  n=2?' _ = false

  module IsEvenM where
    data Evenℕ : Set where
      zero : Evenℕ
      suc-suc : Evenℕ -> Evenℕ

    toℕ : Evenℕ -> ℕ
    toℕ zero = zero
    toℕ (suc-suc x) = suc (suc (toℕ x))

  data IsEven : ℕ -> Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n)) 

  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)
  
  data IsOdd : ℕ → Set where
    one-odd : IsOdd (suc zero)
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  three-is-odd : IsOdd three
  three-is-odd = suc-suc-odd one-odd

  data IsOdd' : ℕ → Set where
    one-odd' : IsOdd' one
    suc-suc-odd' : {n : ℕ} → IsOdd' n → IsOdd' (suc (suc n))

  three-is-odd' : IsOdd' three
  three-is-odd' = suc-suc-odd' one-odd'

  data IsOdd'' : ℕ → Set where
    suc-of_is-odd : {n : ℕ} → IsEven n → IsOdd'' (suc n)

  three-is-odd'' : IsOdd'' three
  three-is-odd'' = suc-of suc-suc-even zero-even is-odd

  odd-follow-even : {n : ℕ} → IsEven n → IsOdd'' (suc n)
  odd-follow-even zero-even = suc-of zero-even is-odd
  odd-follow-even (suc-suc-even x) = suc-of (suc-suc-even x) is-odd

  odd-follow-even' : {n : ℕ} → IsEven n → IsOdd'' (suc n)
  odd-follow-even' = suc-of_is-odd

module MyMaybe where
  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing :     Maybe A

  open Naturals
  open import Data.Nat
    using (ℕ; zero; suc)

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc x)) with evenEv x
  ... | just x₁ = just (suc-suc-even x₁)
  ... | nothing = nothing

module Addition where
  open Naturals
  open import Data.Nat
    using (ℕ; zero; suc)

  _+_ : ℕ → ℕ → ℕ
  zero  + y = y
  suc x + y = x + suc y

  infixl 6 _+_

  module Mult where
    infixl 7 _*_
    _*_ : ℕ → ℕ → ℕ
    zero  * b = zero
    suc a * b = b + a * b

    module Exponent where
      infixl 8 _^_
      _^_ : ℕ → ℕ → ℕ
      a ^ zero = one
      a ^ suc b = a * a ^ b

  module Monus where
    infixl 6 _∸_ 
    _∸_ : ℕ → ℕ → ℕ
    x ∸ zero = x
    zero ∸ suc y = zero
    suc x ∸ suc y = x ∸ y
  
  module Natural-Tests where
    open import Relation.Binary.PropositionalEquality
    open Monus
    open Mult

    _ : one + two ≡ three
    _ = refl

    _ : three ∸ one ≡ two
    _ = refl

    _ : one ∸ three ≡ zero
    _ = refl

    _ : two * two ≡ four
    _ = refl

module False-Integers where
  data ℤ : Set where
    zero : ℤ
    succ : ℤ → ℤ
    pred : ℤ → ℤ

  normalize : ℤ → ℤ
  normalize zero = zero
  normalize (succ zero) = succ zero
  normalize (succ (succ x)) = succ (normalize (succ x))
  normalize (succ (pred x)) = normalize x
  normalize (pred zero) = pred zero
  normalize (pred (succ x)) = normalize x
  normalize (pred (pred x)) = pred (normalize (pred x))

  module Counter-Example where
    open import Relation.Binary.PropositionalEquality

    _ : normalize (succ (succ (pred (pred zero)))) ≡ succ (pred zero)
    _ = refl

    _ : normalize (succ (pred zero)) ≡ zero
    _ = refl

    -- _ : normalize (pred (succ (succ (pred (pred zero))))) ≡ succ (pred (pred zero))
    -- _ = refl

module False-Integers-2 where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)

  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ

  normalize : ℤ → ℤ
  normalize (mkℤ zero neg) = mkℤ zero neg
  normalize (mkℤ (suc pos) zero) = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg)) = normalize (mkℤ pos neg)

  infixl 6 _*_
  infixl 5 _+_ _-_

  _+_ : ℤ → ℤ → ℤ
  mkℤ pos neg + mkℤ pos₁ neg₁ = 
    normalize (mkℤ (pos ℕ.+ pos₁) (neg ℕ.+ neg₁))

  _-_ : ℤ → ℤ → ℤ
  mkℤ pos neg - mkℤ pos₁ neg₁ = 
    normalize (mkℤ (pos ℕ.+ neg₁) (neg ℕ.+ pos₁))

  -- (p1 - n1) * (p2 - n2)
  -- = p1p2 - p1n2 - p2n1 + n1n2
  -- = (p1p2 + n1n2) - (p1n2 + p2n1)
  
  _*_ : ℤ → ℤ → ℤ
  mkℤ pos neg * mkℤ pos₁ neg₁ =
    normalize 
      (mkℤ (pos ℕ.* pos₁ ℕ.+ neg ℕ.* neg₁)
           (pos ℕ.* neg₁ ℕ.+ pos₁ ℕ.* neg))

  module Testing where
    open import Relation.Binary.PropositionalEquality

    _ : mkℤ 2 3 + mkℤ 5 1 ≡ mkℤ 3 0
    _ = refl

    _ : mkℤ 2 3 - mkℤ 5 1 ≡ mkℤ 0 5
    _ = refl

    _ : mkℤ 2 3 * mkℤ 5 1 ≡ mkℤ 0 4
    _ = refl

module False-Integers-3 where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ

  six : ℤ
  six = + 6

  neg-six : ℤ
  neg-six = - 6

module Integers where
  open import Relation.Binary.PropositionalEquality
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  pattern +[1+_] n = + ℕ.suc n
  pattern +0 = + ℕ.zero

  0ℤ : ℤ
  0ℤ = +0

  1ℤ : ℤ
  1ℤ = +[1+ ℕ.zero ]

  -1ℤ : ℤ
  -1ℤ = -[1+ ℕ.zero ]

  suc : ℤ → ℤ
  suc (+ x) = +[1+ x ]
  suc -[1+ ℕ.zero ] = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ ℕ.suc x ]

  -_ : ℤ → ℤ
  - +0 = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]
  
  module Naive-Addition where
    _⊖_ : ℕ → ℕ → ℤ
    ℕ.zero  ⊖ ℕ.zero  = +0
    ℕ.zero  ⊖ ℕ.suc b = -[1+ b ]
    ℕ.suc a ⊖ ℕ.zero  = +[1+ a ]
    ℕ.suc a ⊖ ℕ.suc b = a ⊖ b

    infixl 5 _+_
    _+_ : ℤ → ℤ → ℤ
    + x      + + y      = + (x ℕ.+ y)
    + x      + -[1+ y ] = x ⊖ ℕ.suc y
    -[1+ x ] + + y      = y ⊖ ℕ.suc x
    -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

    infixl 5 _-_
    _-_ : ℤ → ℤ → ℤ
    x - y = x + (- y)

    infixl 6 _*_
    _*_ : ℤ → ℤ → ℤ
    x * +0 = +0
    x * +[1+ ℕ.zero ] = x
    x * -[1+ ℕ.zero ] = - x
    x * +[1+ ℕ.suc y ] = +[1+ y ] * x + x
    x * -[1+ ℕ.suc y ] = -[1+ y ] * x - x

    module Testing-It where
      open import Relation.Binary.PropositionalEquality

      _ : - (+ 4) * - (+ 6) ≡ + 24
      _ = refl

      _ : + 8 - (- (+ 3)) ≡ + 11
      _ = refl

open import Data.Nat 
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Naturals
  using (one; two; three; four; IsEven)
  renaming ( zero-even    to z-even
           ; suc-suc-even to ss-even )
  public

open import Data.Maybe
  using (Maybe; just; nothing)
  public
