------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------------ Residualizing Monad -----------------
------------------------------------------------------


open import Utils
open import Syntax
open import Renamings
open import Presheaves


module Monad where 

  -- Object map of the residualizing monad
  data T (X : Ctx → Set) : Ctx → Set where
    T-return : {Γ : Ctx} → X Γ → T X Γ
    T-to : {Γ : Ctx} {σ : Ty} → Γ ⊢ap σ → T X (Γ :: σ) → T X Γ
    -- algebraic constructors
    T-or : {Γ : Ctx} → T X Γ → T X Γ → T X Γ
    T-if : {Γ : Ctx} → Γ ⊢nv bit → T X Γ → T X Γ → T X Γ
    T-input : {Γ : Ctx} → T X (Γ :: bit) → T X Γ
    T-output : {Γ : Ctx} → Γ ⊢nv bit → T X Γ → T X Γ


  -- Algebra operations
  Alg-or : {X : Ctx → Set} {Γ : Ctx} → T X Γ → T X Γ → T X Γ
  Alg-or d d' = T-or d d'

  Alg-if : {X : Ctx → Set} {Γ : Ctx} → Γ ⊢nv bit → T X Γ → T X Γ → T X Γ
  Alg-if b d d' = T-if b d d'

  Alg-input : {X : Ctx → Set} {Γ : Ctx} → T X (Γ :: bit) → T X Γ
  Alg-input d = T-input d

  Alg-output : {X : Ctx → Set} {Γ : Ctx} → Γ ⊢nv bit → T X Γ → T X Γ
  Alg-output b d = T-output b d


  -- Action of renaming on the residualizing monad
  T-rename : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → T (set X) Γ → T (set X) Γ'
  T-rename {X} {Γ} {Γ'} f (T-return x) = T-return ((act X) f x)
  T-rename {X} {Γ} {Γ'} f (T-to {.Γ} {σ} x y) = T-to (⊢ap-rename f x) (T-rename {X} {Γ :: σ} {Γ' :: σ} (wk₂ f) y)
  T-rename {X} {Γ} {Γ'} f (T-or x y) = T-or (T-rename {X} {Γ} {Γ'} f x) (T-rename {X} {Γ} {Γ'} f y)
  T-rename {X} {Γ} {Γ'} f (T-if b x y) = T-if (⊢nv-rename f b) (T-rename {X} {Γ} {Γ'} f x) (T-rename {X} {Γ} {Γ'} f y)
  T-rename {X} {Γ} {Γ'} f (T-input x) = T-input (T-rename {X} {Γ :: bit} {Γ' :: bit} (wk₂ f) x)
  T-rename {X} {Γ} {Γ'} f (T-output b x) = T-output (⊢nv-rename f b) (T-rename {X} {Γ} {Γ'} f x)


  -- The residualizing monad on presheaves
  T-Set^Ren : Set^Ren → Set^Ren
  T-Set^Ren X = 
    record {
      set = T (set X);
      act = T-rename {X}
    }


  -- Unit of the residualizing monad
  η : {X : Set^Ren} → Set^Ren-Map X (T-Set^Ren X)
  η X = T-return X


  -- η is natural in Γ
  η-naturality : 
    {X : Set^Ren} 
    {Γ Γ' : Ctx} 
    {f : Ren Γ Γ'} 
    → (x : set X Γ) 
    → T-rename {X} f (η {X} x) ≅ η {X} {Γ'} ((act X) f x)

  η-naturality {X} {Γ} {Γ'} {f} x = 
      T-return (act X f x)
    ∎


  -- Kleisli extension of the residualizing monad
  * : {X Y : Set^Ren} → (Set^Ren-Map X (T-Set^Ren Y)) → Set^Ren-Map (T-Set^Ren X) (T-Set^Ren Y)
  * {X} {Y} f {Γ} (T-return x) = f {Γ} x
  * {X} {Y} f {Γ} (T-to {.Γ} {σ} t x) = T-to t (* {X} {Y} f {Γ :: σ} x) 
  * {X} {Y} f {Γ} (T-or x y) = T-or (* {X} {Y} f {Γ} x) (* {X} {Y} f {Γ} y)
  * {X} {Y} f {Γ} (T-if b x y) = T-if b (* {X} {Y} f {Γ} x) (* {X} {Y} f {Γ} y)
  * {X} {Y} f {Γ} (T-input x) = T-input (* {X} {Y} f {Γ :: bit} x)
  * {X} {Y} f {Γ} (T-output b x) = T-output b (* {X} {Y} f {Γ} x)


  -- Naturality of the Kleisliextension
  *-naturality : 
    {X Y : Set^Ren} 
    {Γ Γ' : Ctx} 
    {f : Ren Γ Γ'} 
    → (g : Set^Ren-Map X (T-Set^Ren Y))
    → (p : {Γ Γ' : Ctx} {f : Ren Γ Γ'} 
            → (x : (set X) Γ) 
            → T-rename {Y} f (g x) ≅ g ((act X) f x))
    → (x : T (set X) Γ) 
    → T-rename {Y} f (* {X} {Y} g x) ≅ * {X} {Y} g (T-rename {X} f x)

  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-return x) = 
      T-rename f (g x)
    ≅〈 p x 〉
      g (act X f x)
    ∎
  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-to x y) = 
      T-to (⊢ap-rename f x) (T-rename (wk₂ f) (* g y))
    ≅〈 cong (T-to (⊢ap-rename f x)) (*-naturality g p y) 〉
      T-to (⊢ap-rename f x) (* g (T-rename (wk₂ f) y))
    ∎
  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-or x y) = 
      T-or (T-rename f (* g x)) (T-rename f (* g y))
    ≅〈 cong2 T-or (*-naturality g p x) (*-naturality g p y) 〉
      T-or (* g (T-rename f x)) (* g (T-rename f y))
    ∎
  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-if b x y) = 
      T-if (⊢nv-rename f b) (T-rename f (* g x)) (T-rename f (* g y))
    ≅〈 cong2 (T-if (⊢nv-rename f b)) (*-naturality g p x) (*-naturality g p y) 〉
      T-if (⊢nv-rename f b) (* g (T-rename f x)) (* g (T-rename f y))
    ∎
  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-input x) = 
      T-input (T-rename (wk₂ f) (* g x))
    ≅〈 cong T-input (*-naturality g p x) 〉
      T-input (* g (T-rename (wk₂ f) x))
    ∎
  *-naturality {X} {Y} {Γ} {Γ'} {f} g p (T-output b x) = 
      T-output (⊢nv-rename f b) (T-rename f (* g x))
    ≅〈 cong (T-output (⊢nv-rename f b)) (*-naturality g p x) 〉
      T-output (⊢nv-rename f b) (* g (T-rename f x))
    ∎


  -- Action of T on presheaf maps
  Tf : {X Y : Set^Ren} → (Set^Ren-Map X Y) → Set^Ren-Map (T-Set^Ren X) (T-Set^Ren Y)
  Tf {X} {Y} f {Γ} x = * {X} {Y} (λ {Γ'} x → η {Y} (f {Γ'} x)) {Γ} x  


  -- Multiplication of the residualizing monad
  μ : {X : Set^Ren} → Set^Ren-Map (T-Set^Ren (T-Set^Ren X)) (T-Set^Ren X)
  μ {X} {Y} x = * {T-Set^Ren X} {X} id x


  -- Strength of the residualizing monad
  t-r : {X Y : Set^Ren} → Set^Ren-Map (X ⊗ (T-Set^Ren Y)) (T-Set^Ren (X ⊗ Y))
  t-r {Γ} (x , T-return y)  = T-return (x , y)
  t-r {X} {Y} {Γ}  (x , T-to {.Γ} {σ} t y) = T-to t (t-r {X} {Y} {Γ :: σ} ((act X wk₁ x) , y))
  t-r {X} {Y} {Γ}  (x , T-or y z) = T-or (t-r {X} {Y} {Γ} (x , y)) (t-r {X} {Y} {Γ} (x , z))
  t-r {X} {Y} {Γ}  (x , T-if b y z) = T-if b (t-r {X} {Y} {Γ} (x , y)) (t-r {X} {Y} {Γ} (x , z))
  t-r {X} {Y} {Γ}  (x , T-input y) = T-input (t-r {X} {Y} {Γ :: bit} ((act X wk₁ x) , y))
  t-r {X} {Y} {Γ}  (x , T-output b y) = T-output b (t-r {X} {Y} {Γ} (x , y))

  -- Components of Kleisli exponentials
  _⇒_ : (X Y : Ctx → Set) → Ctx → Set 
  (X ⇒ Y) Γ = {Γ' : Ctx} → Ren Γ Γ' → X Γ' → T Y Γ'


  -- Action of renaming on Kleisli exponentials
  ⇒-rename : {X Y : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → ((set X) ⇒ (set Y)) Γ → ((set X) ⇒ (set Y)) Γ'
  ⇒-rename f x g = x (comp-ren g f)


  -- Presheaf given by Kleisli exponentials
  ⇒-Set^Ctx : Set^Ren → Set^Ren → Set^Ren
  ⇒-Set^Ctx X Y = 
    record {
      set = ((set X) ⇒ (set Y));
      act = ⇒-rename {X} {Y}
    }    


  -- Evaluation of Kleisli exponentials
  ε : {X Y : Set^Ren} → Set^Ren-Map (⇒-Set^Ctx X Y ⊗ X) (T-Set^Ren Y)
  ε (f , x) = f id-ren x


  -- Monad laws / Kleisli triple laws

  -- Law1
  T-law1 : 
    {X : Set^Ren} 
    {Γ : Ctx} 
    → (x : set (T-Set^Ren X) Γ) 
    → * {X} {X} (η {X}) {Γ} x ≅ x

  T-law1 {X} (T-return x) = 
      T-return x ∎
  T-law1 {X} (T-to t x) = 
      T-to t (* (η {X}) {_} x)
    ≅〈 cong (T-to t) (T-law1 x) 〉
      T-to t x ∎
  T-law1 {X} {Γ} (T-or x y) = 
      T-or (* T-return {Γ} x) (* (η {X}) {Γ} y)
    ≅〈 (cong (T-or (* T-return {Γ} x)) (T-law1 y)) 〉
      T-or (* T-return {Γ} x) y
    ≅〈 (cong (λ x' → T-or x' y) (T-law1 x)) 〉
      T-or x y ∎
  T-law1 {X} {Γ} (T-if b x y) = 
      T-if b (* (η {X}) {Γ} x) (* (η {X}) {Γ} y)
    ≅〈 cong2 (T-if b) (T-law1 x) (T-law1 y) 〉
      T-if b x y
    ∎
  T-law1 {X} {Γ} (T-input x) = 
      T-input (* (η {X}) {Γ :: bit} x)
    ≅〈 cong T-input (T-law1 x) 〉
      T-input x
    ∎
  T-law1 {X} {Γ} (T-output b x) = 
      T-output b (* (η {X}) {Γ} x)
    ≅〈 cong (T-output b) (T-law1 x) 〉
      T-output b x
    ∎


  -- Law2
  T-law2 : 
    {X Y : Set^Ren} 
    {Γ : Ctx} 
    → (x : (set X) Γ) 
    → (f : {Γ : Ctx} → (set X) Γ → T (set Y) Γ) 
    → * {X} {Y} f {Γ} (η {X} x) ≅ f {Γ} x

  T-law2 {X} {Y} {Γ} x f = 
      f {Γ} x ∎


  -- Law3
  T-law3 : 
    {X Y Z : Set^Ren} 
    {Γ : Ctx} 
    → (x : T (set X) Γ) 
    → (f : {Γ : Ctx} → (set X) Γ → T (set Y) Γ) 
    → (g : {Γ : Ctx} → (set Y) Γ → T (set Z) Γ)
    → * {Y} {Z} g {Γ} (* {X} {Y} f {Γ} x) ≅ * {X} {Z} (λ {Γ'} y → * {Y} {Z} g {Γ'} (f {Γ'} y)) {Γ} x 

  T-law3 {X} {Y} {Z} {Γ} (T-return x) f g = 
      * g {Γ} (f {Γ} x) ∎
  T-law3 {X} {Y} {Z} {Γ} (T-to {.Γ} {σ} t x) f g = 
      T-to t (* g {Γ :: σ} (* f {Γ :: σ} x))
    ≅〈 cong (T-to t) (T-law3 {Γ = Γ :: σ} x f g) 〉
      T-to t (* (λ {Γ} z → * g {Γ} (f {Γ} z)) {Γ :: σ} x) ∎
  T-law3 {X} {Y} {Z} {Γ} (T-or x y) f g = 
      T-or (* {Y} {Z} g {Γ} (* {X} {Y} f {Γ} x)) (* {Y} {Z} g {Γ} (* {X} {Y} f {Γ} y))
    ≅〈 (cong (T-or (* {Y} {Z} g {Γ} (* {X} {Y} f {Γ} x))) (T-law3 {Γ = Γ} y f g)) 〉
      T-or (* {Y} {Z} g {Γ} (* {X} {Y} f {Γ} x)) (* {X} {Z} (λ {Γ} z → * {Y} {Z} g {Γ} (f {Γ} z)) {Γ} y) 
    ≅〈 (cong (λ z → T-or z (* {X} {Z} (λ {Γ'} y' → * {Y} {Z} g {Γ'} (f {Γ'} y')) {Γ} y)) (T-law3 {Γ = Γ} x f g)) 〉
      T-or (* {X} {Z} (λ {Γ} z → * {Y} {Z} g {Γ} (f {Γ} z)) {Γ} x) (* {X} {Z} (λ {Γ} z → * {Y} {Z} g {Γ} (f {Γ} z)) {Γ} y) ∎
  T-law3 {X} {Y} {Z} {Γ} (T-if b x y) f g = 
      T-if b (* g {Γ} (* f {Γ} x)) (* g {Γ} (* f {Γ} y))
    ≅〈 cong2 (T-if b) (T-law3 {Γ = Γ} x f g) (T-law3 {Γ = Γ} y f g) 〉
      T-if b (* (λ {Γ} z → * g {Γ} (f {Γ} z)) {Γ} x) (* (λ {Γ} z → * g {Γ} (f {Γ} z)) {Γ} y)
    ∎
  T-law3 {X} {Y} {Z} {Γ} (T-input x) f g = 
      T-input (* g (* f x))
    ≅〈 cong T-input (T-law3 x f g) 〉
      T-input (* (λ z → * g (f z)) x)
    ∎
  T-law3 {X} {Y} {Z} {Γ} (T-output b x) f g = 
      T-output b (* g {Γ} (* f {Γ} x)) 
    ≅〈 cong (T-output b) (T-law3 {Γ = Γ} x f g)  〉
      T-output b (* (λ {Γ} z → * g {Γ} (f {Γ} z)) {Γ} x) 
    ∎


  -- Monad strength laws

  -- Strength law 1
  t-r-law1 : 
    {X : Set^Ren} 
    {Γ : Ctx} 
    → (i : set Set^Ren-Terminal Γ)
    → (x : set (T-Set^Ren X) Γ) 
    → (Tf {Set^Ren-Terminal ⊗ X} 
          {X} 
          ×-lambda 
          (t-r {Set^Ren-Terminal} {X} {Γ} (i , x))) ≅ ×-lambda (i , x)

  t-r-law1 i (T-return x) = 
      T-return x
    ∎
  t-r-law1 {X} {Γ} i (T-to {.Γ} {σ} x y) = 
      T-to x (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ :: σ} (i , y)))
    ≅〈 cong (T-to x) (t-r-law1 i y) 〉
      T-to x y
    ∎
  t-r-law1 {X} {Γ} i (T-or x y) = 
      T-or (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ} (i , x))) (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ} (i , y)))
    ≅〈 cong2 T-or (t-r-law1 i x) (t-r-law1 i y) 〉
      T-or x y
    ∎
  t-r-law1 {X} {Γ} i (T-if b x y) = 
      T-if b (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ} (i , x))) (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ} (i , y)))
    ≅〈 cong2 (T-if b) (t-r-law1 i x) (t-r-law1 i y) 〉
      T-if b x y
    ∎
  t-r-law1 {X} {Γ} i (T-input x) = 
      T-input (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ :: bit} (i , x)))
    ≅〈 cong T-input (t-r-law1 i x) 〉
      ×-lambda (i , T-input x)
    ∎
  t-r-law1 {X} {Γ} i (T-output b x) = 
      T-output b (Tf (snd) (t-r {Set^Ren-Terminal} {X} {Γ} (i , x)))
    ≅〈 cong (T-output b) (t-r-law1 i x) 〉
      T-output b x
    ∎


  -- Sterngth law 2
  t-r-law2 : 
    {X Y : Set^Ren}
    {Γ : Ctx}
    → (x : set X Γ)
    → (y : set Y Γ)
    → t-r {X} {Y} {Γ} (x , η {Y} y) ≅ η {X ⊗ Y} (x , y)
    
  t-r-law2 x y = 
      T-return (x , y)
    ∎


  -- Strength law 3
  t-r-law3 :
    {X Y Z : Set^Ren}
    {Γ : Ctx}
    → (x : set X Γ)
    → (y : set Y Γ)
    → (z : T (set Z) Γ)
    → Tf {(X ⊗ Y) ⊗ Z} 
         {X ⊗ (Y ⊗ Z)} 
         ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z)) ≅ t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z)))

  t-r-law3 x y (T-return z) = 
      T-return (x , (y , z))
    ∎
  t-r-law3 {X} {Y} {Z} x y (T-to {Γ} {σ} z z') = 
      T-to z (Tf ×-alpha (t-r {X ⊗ Y} {Z} (((act X) wk₁ x , (act Y) wk₁ y) , z')))
    ≅〈 cong (T-to z) (t-r-law3 {X} {Y} {Z} ((act X) wk₁ x) ((act Y) wk₁ y) z') 〉
      T-to z (t-r {X} {Y ⊗ Z} ((act X) wk₁ x , (t-r {Y} {Z} ((act Y) wk₁ y , z'))))
    ∎
  t-r-law3 {X} {Y} {Z} x y (T-or z z') = 
      T-or (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z))) (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z')))
    ≅〈 cong2 T-or (t-r-law3 {X} {Y} {Z} x y z) (t-r-law3 {X} {Y} {Z} x y z') 〉
      T-or (t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z)))) (t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z'))))
    ∎
  t-r-law3 {X} {Y} {Z} x y (T-if b z z') = 
      T-if b (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z))) (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z')))
    ≅〈 cong2 (T-if b) (t-r-law3 {X} {Y} {Z} x y z) (t-r-law3 {X} {Y} {Z} x y z') 〉
      T-if b (t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z)))) (t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z'))))
    ∎
  t-r-law3 {X} {Y} {Z} x y (T-input z) =
      T-input (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((act X wk₁ x , act Y wk₁ y) , z)))
    ≅〈 cong T-input (t-r-law3 {X} {Y} {Z} (act X wk₁ x) (act Y wk₁ y) z) 〉
      T-input (t-r {X} {Y ⊗ Z} (act X wk₁ x , (t-r {Y} {Z} (act Y wk₁ y , z))))
    ∎
  t-r-law3 {X} {Y} {Z} x y (T-output b z) = 
      T-output b (Tf ×-alpha (t-r {X ⊗ Y} {Z} ((x , y) , z)))
    ≅〈 cong (T-output b) (t-r-law3 {X} {Y} {Z} x y z) 〉
      T-output b (t-r {X} {Y ⊗ Z} (x , (t-r {Y} {Z} (y , z))))
    ∎


  -- Strength law 4
  t-r-law4 :
    {X Y : Set^Ren}
    {Γ : Ctx}
    → (x : set X Γ)
    → (y :  set (T-Set^Ren (T-Set^Ren Y)) Γ)
    → μ {X ⊗ Y} 
        (Tf {X ⊗ (T-Set^Ren Y)} 
            {T-Set^Ren (X ⊗ Y)}
            (t-r {X} {Y}) 
            (t-r {X} {T-Set^Ren Y} (x , y))) ≅ t-r {X} {Y} (x , (μ {Y} y))

  t-r-law4 {X} {Y} x (T-return y) = 
      t-r (x , y)
    ∎
  t-r-law4 {X} {Y} x (T-to y y') = 
      T-to y
        (* (λ {Γ} z → z)
          (* (λ {Γ} z → T-return (t-r z))
            (t-r (act X (λ {σ} → Tl) x , y'))))
    ≅〈 cong (T-to y) (t-r-law4 ((act X) wk₁ x) y') 〉
      T-to y 
        (t-r (act X (λ {σ} → Tl) x , * (λ {Γ} z → z) y'))
    ∎
  t-r-law4 {X} {Y} x (T-or y y') = 
      T-or
        (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (x , y))))
        (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (x , y'))))
    ≅〈 cong2 T-or (t-r-law4 x y) (t-r-law4 x y') 〉
      T-or 
        (t-r (x , * (λ {Γ} z → z) y)) 
        (t-r (x , * (λ {Γ} z → z) y'))
    ∎
  t-r-law4 {X} {Y} x (T-if b y y') = 
      T-if b
        (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (x , y))))
        (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (x , y'))))
    ≅〈 cong2 (T-if b) (t-r-law4 x y) (t-r-law4 x y') 〉
      T-if b 
        (t-r (x , * (λ {Γ} z → z) y)) 
        (t-r (x , * (λ {Γ} z → z) y'))
    ∎
  t-r-law4 {X} {Y} x (T-input y) = 
      T-input
        (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (act X wk₁ x , y))))
    ≅〈 cong T-input (t-r-law4 (act X wk₁ x) y) 〉
      t-r (x , T-input (* (λ {Γ} z → z) y))
    ∎
  t-r-law4 {X} {Y} x (T-output b y) = 
      T-output b (* (λ {Γ} z → z) (* (λ {Γ} z → T-return (t-r z)) (t-r (x , y))))
    ≅〈 cong (T-output b) (t-r-law4 x y) 〉
      T-output b (t-r (x , * (λ {Γ} z → z) y))
    ∎
