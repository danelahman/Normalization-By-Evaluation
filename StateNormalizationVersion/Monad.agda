{-# OPTIONS --no-termination-check #-}
----------------------------------------------------------
----------------- Normalization by evaluation ------------
-------------------- and algebraic effects ---------------
----------------------------------------------------------
---------------------- Residuating monad -----------------
-- Sum of effect free residuating monad and state monad --
----------------------------------------------------------
----------------------------------------------------------
---- PS! Agda does not see the definition of strength ----
---- terminating. ----------------------------------------
----------------------------------------------------------


open import Utils
open import Syntax
open import Renamings
open import Presheaves


module Monad where 

  -- "Syntax" for (strictly positive) functors for constructing the residuating monad
  data SPFunctor : Set1 where
    Id : SPFunctor
    Const : (Ctx → Set) → SPFunctor
    _⊕'_ : SPFunctor → SPFunctor → SPFunctor 
    _⊗'_ : SPFunctor → SPFunctor → SPFunctor
    ⇒ : (Ctx → Set) → SPFunctor → SPFunctor
    APTerm :  SPFunctor → SPFunctor

  infixl 6 _⊕'_
  infixr 7 _⊗'_


  -- "Semantics" of the (strictly positive) functors in Set^Ren for constructing the residuating monad
  [_]_ : SPFunctor → (Ctx → Set) → (Ctx → Set) 
  [ Id ] X = λ Γ → X Γ
  [ Const C ] X = C
  [ F ⊕' G ] X = λ Γ → ([ F ] X) Γ + ([ G ] X) Γ
  [ F ⊗' G ] X = λ Γ → ([ F ] X) Γ × ([ G ] X) Γ
  [ ⇒ C F ] X = λ Γ → C Γ → ([ F ] X) Γ
  [ APTerm F ] X = λ Γ → Σ Ty (λ σ → (Γ ⊢ap σ) × ([ F ] X) (Γ :: σ) )


  -- Least fixed point of the (strictly positive) residuating functor
  data μ_ (F : SPFunctor) : Ctx → Set where 
    lfp : {Γ : Ctx} → ([ F ] (μ F)) Γ → (μ F) Γ


  -- Object map of the residuating monad
  T : (Ctx → Set) → (Ctx → Set)
  T X = μ (⇒ (λ _ → (Unit + Unit)) ((Const (λ _ → (Unit + Unit))) ⊗' (Const X ⊕' APTerm Id)))


  -- Action of renaming on for residuating monad
  T-rename : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → T (set X) Γ → T (set X) Γ'
  T-rename-helper : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ')  
    → set X Γ +
        Σ Ty
        (λ σ →
           Σ (Γ ⊢ap σ)
           (λ _ →
              (μ
               ⇒ (λ _ → Unit + Unit)
               (Const (λ _ → Unit + Unit) ⊗' (Const (set X) ⊕' APTerm Id)))
              (Γ :: σ)))
    → set X Γ' +
      Σ Ty
      (λ σ →
         Σ (Γ' ⊢ap σ)
         (λ _ →
            (μ
             ⇒ (λ _ → Unit + Unit)
             (Const (λ _ → Unit + Unit) ⊗' (Const (set X) ⊕' APTerm Id)))
            (Γ' :: σ)))

  T-rename-helper {X} f (inl d) = inl (act X f d)
  T-rename-helper {X} f (inr (σ , (t , d))) = inr (σ , ((act (APTerms σ) f t) , T-rename {X} (wk₂ f) d))

  T-rename {X} {Γ} {Γ'} f (lfp d) = lfp (λ b → 
    (fst (d b)) , T-rename-helper {X} f (snd (d b)))


  -- Residuating monad on presheaves
  T-Set^Ren : Set^Ren → Set^Ren
  T-Set^Ren X = 
    record {
      set = T (set X);
      act = T-rename {X}
    }


  -- Unit of the residuating monad
  η : {X : Set^Ren} → Set^Ren-Map X (T-Set^Ren X)
  η d = lfp (λ {(inl b) → (inl b) , (inl d) ; (inr b) → (inr b) , (inl d)})


  -- Kleisli extension
  * : {X Y : Set^Ren} → (Set^Ren-Map X (T-Set^Ren Y)) → Set^Ren-Map (T-Set^Ren X) (T-Set^Ren Y)
  *-helper : {X Y : Set^Ren} {Γ : Ctx} → 
    (f  : {Γ : List Ty} →
     set X Γ →
     (μ
      ⇒ (λ _ → Unit + Unit)
      (Const (λ _ → Unit + Unit) ⊗' (Const (set Y) ⊕' APTerm Id)))
     Γ)
    → 
    Σ (Unit + Unit)
     (λ _ →
        set X Γ +
        Σ Ty
        (λ σ →
           Σ (Γ ⊢ap σ)
           (λ _ →
              (μ
               ⇒ (λ _ → Unit + Unit)
               (Const (λ _ → Unit + Unit) ⊗' (Const (set X) ⊕' APTerm Id)))
              (Γ :: σ))))
    →
    Σ (Unit + Unit)
      (λ _ →
         set Y Γ +
         Σ Ty
         (λ σ →
            Σ (Γ ⊢ap σ)
            (λ _ →
               (μ
                ⇒ (λ _ → Unit + Unit)
                (Const (λ _ → Unit + Unit) ⊗' (Const (set Y) ⊕' APTerm Id)))
               (Γ :: σ))))

  *-helper f (b , inl d) with (f d)
  *-helper f (b , inl d) | lfp d' = d' b
  *-helper {X} {Y} f (b , inr (σ , (t , d))) = b , (inr (σ , (t , * {X} {Y} f d)))

  * {X} {Y} f (lfp d) = lfp (λ b → *-helper {X} {Y} f (d b))


  -- Strength of the residuating monad
  strength : {X Y : Set^Ren} → Set^Ren-Map (X ⊗ (T-Set^Ren Y)) (T-Set^Ren (X ⊗ Y))
  strength-helper : {X Y : Set^Ren} {Γ : Ctx} → (a : set X Γ) →
    Σ (Unit + Unit)
    (λ _ →
       set Y Γ +
       Σ Ty
       (λ σ →
          Σ (Γ ⊢ap σ)
          (λ _ →
             (μ
              ⇒ (λ _ → Unit + Unit)
              (Const (λ _ → Unit + Unit) ⊗' (Const (set Y) ⊕' APTerm Id)))
             (Γ :: σ)))) → 
    Σ (Unit + Unit)
      (λ _ →
         Σ (set X Γ) (λ _ → set Y Γ) +
         Σ Ty
         (λ σ →
            Σ (Γ ⊢ap σ)
            (λ _ →
               (μ
                ⇒ (λ _ → Unit + Unit)
                (Const (λ _ → Unit + Unit) ⊗'
                 (Const (λ Γ₁ → Σ (set X Γ₁) (λ _ → set Y Γ₁)) ⊕' APTerm Id)))
               (Γ :: σ))))

  strength-helper a (b , inl d) = b , (inl (a , d))
  strength-helper {X} {Y} {Γ} a (b , inr (σ , (t , d))) = b , inr (σ , (t , strength {X} {Y} {Γ :: σ} (act X wk₁ a , d)))

  strength {X} {Y} {Γ} (a , lfp d) = lfp (λ b → strength-helper {X} {Y} a (d b))



  -- Components of Kleisli exponentials
  _⇒T_ : (X Y : Ctx → Set) → Ctx → Set 
  (X ⇒T Y) Γ = {Γ' : Ctx} → Ren Γ Γ' → X Γ' → T Y Γ'


  -- Algebraic operations for the residual monad (global state operations)
  Alg-lookup :  {X : Set^Ren} → (Set^Ren-Map ((T-Set^Ren X) ⊗ (T-Set^Ren X)) (T-Set^Ren X))
  Alg-lookup (lfp d , lfp d') = lfp (λ {(inl b) → d (inl b) ; (inr b) → d' (inr b)})

  Alg-update0 :  {X : Set^Ren} → (Set^Ren-Map (T-Set^Ren X) (T-Set^Ren X))
  Alg-update0 (lfp d) = lfp (λ b → d (inl ⋆))

  Alg-update1 :  {X : Set^Ren} → (Set^Ren-Map (T-Set^Ren X) (T-Set^Ren X))
  Alg-update1 (lfp d) = lfp (λ b → d (inr ⋆))

