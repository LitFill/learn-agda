module Chapter1-Hello where

module Booleans where
  open import Relation.Binary.PropositionalEquality

  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool → Bool
  not true  = false
  not false = true

  _ : not (not false) ≡ false
  _ = refl

  _∨_ : Bool → Bool → Bool
  true  ∨ _     = true
  false ∨ other = other

  _∧_ : Bool → Bool → Bool
  true  ∧ other = other
  false ∧ _     = false

module Employees where
  open Booleans
  open import Data.String
    using (String)

  data Departement : Set where
    administrative : Departement
    engineering    : Departement
    finance        : Departement
    marketing      : Departement
    sales          : Departement

  record Employee : Set where
    field
      name        : String
      departement : Departement
      is-new-hire : Bool

  tillman : Employee
  tillman = record 
    { name        = "Tilman"
    ; departement = engineering
    ; is-new-hire = false
    }

module Tuples where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A
      proj₂ : B

  open _×_

  my-tuple : Bool × Bool
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }

  first : Bool × Bool → Bool
  first record { proj₁ = x } = x 

  my-tuple-first : Bool
  my-tuple-first = my-tuple .proj₁

  my-tuple-second : Bool
  my-tuple-second = proj₂ my-tuple

  my-copatern : Bool × Bool
  my-copatern .proj₁ = true
  my-copatern .proj₂ = not false

  nested-copatern : Bool × (Bool × Bool)
  nested-copatern .proj₁ = false ∧ true
  nested-copatern .proj₂ .proj₁ = not true
  nested-copatern .proj₂ .proj₂ = false ∨ (true ∨ true)

  _,_ : {A B : Set} → A → B → A × B 
  x , y = record { proj₁ = x; proj₂ = y }

  my-tuple' : Bool × Bool
  my-tuple' = (true ∨ true) , not false

module Tuple-2 where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      proj-1 : A
      proj-2 : B

  open _×_

  infixr 2 _×_
  infixr 4 _,_

  data _⊎_ (A : Set) (B : Set) : Set where
    inj-1 : A → A ⊎ B
    inj-2 : B → A ⊎ B

  infixr 1 _⊎_

  curry : {A B C : Set} → (A × B → C) → A → B → C
  curry f a b = f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → A × B → C 
  uncurry f (a , b) = f a b

  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Pets where
  open import Data.String
    using (String)

  data Species : Set where
    bird cat dog reptile : Species

  data Temprament : Set where
    anxious chill excitable grumpy : Temprament 

  record Pet : Set where
    constructor makePet
    field
      species    : Species
      temprament : Temprament
      name       : String

module Implicits where
  open import Data.Bool
    using (Bool; true; false; not; _∨_)

  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming ( _,′_ to _,_
             ; curry′ to curry
             ; uncurry′ to uncurry
             )

  open import Data.String
    using (String)

  mk-tuple : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple A B x x₁ = x , x₁ 

  _ : Bool × String
  _ = mk-tuple Bool String true "string" 

open import Data.Bool
  using (Bool; true; false; not; _∨_; _∧_)
  public

open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public
