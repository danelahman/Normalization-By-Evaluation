------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
--------------- Little Standard Library --------------
------------------------------------------------------


module Utils where


  -- Heterogeneous (John Major) equality
  data _≅_ {A : Set} (a : A) : {A' : Set} → A' → Set where
    refl : a ≅ a


  -- Symmetry of equality
  sym : 
    {A : Set} 
    → {a a' : A} 
    → a ≅ a' 
    → a' ≅ a

  sym refl = refl


  -- Transitivity of equality
  trans : 
    {A : Set} 
    → {a b c : A} 
    → a ≅ b 
    → b ≅ c 
    → a ≅ c

  trans refl refl = refl


  -- Equational reasoning for equality
  _≅〈_〉_ : 
    {A : Set} 
    (x : A) 
    {y z : A} 
    → (x ≅ y) 
    → (y ≅ z) 
    → (x ≅ z)

  x ≅〈 p 〉 q = trans p q

  _∎ : 
    {A : Set} 
    (x : A) 
    → x ≅ x

  z ∎ = refl

  infix  2 _∎
  infixr 2 _≅〈_〉_

  -- Congruence for equality
  cong : 
    {A B : Set} 
    → (f : A → B) 
    → {a a' : A} 
    → a ≅ a' 
    → f a ≅ f a'

  cong f refl = refl

  -- Congruence for equality
  cong2 : 
    {A : Set}
    {B : A → Set}
    {C : ∀ a → B a → Set} 
    → (f : ∀ a b → C a b) 
    → {a a' : A} 
    → a ≅ a' 
    → {b : B a} 
    → {b' : B a'} 
    → b ≅ b' 
    → f a b ≅ f a' b'

  cong2 f refl refl = refl


  -- Substitutions for equality
  subst : 
    {A : Set} 
    → (C : A → Set) 
    → {a : A} 
    → C a 
    → {b : A} 
    → a ≅ b 
    → C b

  subst C p refl = p


  -- Postulated function extensionality
  postulate 
    ext : 
      {A : Set}
      {B B' : A → Set}
      {f : ∀ a → B a}
      {g : ∀ a → B' a} 
      → (∀ a → f a ≅ g a) 
      → f ≅ g

  postulate 
    iext : 
      {A : Set}
      {B B' : A → Set}
      {f : ∀ {a} → B a}
      {g : ∀{a} → B' a} 
      → (∀ a → f {a} ≅ g {a}) 
      → _≅_ { {a : A} → B a} f { {a : A} → B' a} g


  -- Singleton set
  record Unit : Set where
    constructor ⋆
  open Unit


  data Unit' : Set where
    unit : Unit'


  -- Every element of unit type is equal to the unique constructor
  unit-lem : 
    {x : Unit} 
    → x ≅ ⋆

  unit-lem {⋆} = refl


  -- Dependent sums
  record Σ (A : Set)(B : A → Set) : Set where
    constructor _,_
    field fst : A
          snd : B fst
  open Σ public


  -- Dependent function space
  Π : (A : Set) -> (B : A -> Set) -> Set
  Π A B = (x : A) -> B x


  -- Binary products
  _×_ : Set → Set → Set
  A × B = Σ A λ _ → B

  infixl 10 _×_


  -- Lambda map of monoidal structure of products
  ×-lambda : {X : Set} → (Unit × X) → X
  ×-lambda (⋆ , x) = x


  -- Alpha map of monoidal structure of products
  ×-alpha : {X Y Z : Set} → ((X × Y) × Z) → (X × (Y × Z))
  ×-alpha ((x , y) , z) = x , (y , z)

  -- Sums
  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B


  -- Empty set
  data ∅ : Set where


  -- Set of truth values
  data True : Set where
    void : True
  open True


  -- Identity
  id : {A : Set} -> A -> A 
  id {A} x = x


  -- Composition
  infixl 5 _·_
  _·_ : {A B C : Set} → (f : A → B) → (g : C → A) → C → B
  (f · g) x = f (g x)


  -- Snoc-Lists
  data List (A : Set) : Set where
    []  : List A
    _::_ : List A → A → List A
  open List

  infixl 5 _::_ 


  -- Concatenation of lists
  concat : {A : Set} → List A → List A → List A
  concat y [] = y
  concat y (xs :: x) = (concat y xs) :: x
