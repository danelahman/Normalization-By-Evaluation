------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------------ Residuating monad -----------------
------------------------------------------------------


open import Utils
open import Syntax
open import Renamings
open import Presheaves


module Monad where 

  -- The residual monad
  data T'' (X : Ctx → Set) : Ctx → Set
  data T' (X : Ctx → Set) : Ctx → Set
  data T (X : Ctx → Set) : Ctx → Set
    
  data T'' X where
    T-return : {Γ : Ctx} → X Γ → T'' X Γ
    T-to : {Γ : Ctx} {σ : Ty} → Γ ⊢ap σ → T X (Γ :: σ) → T'' X Γ

  data T' X where
    T-update0 : {Γ : Ctx} → T'' X Γ → T' X Γ
    T-update1 : {Γ : Ctx} → T'' X Γ → T' X Γ

  data T X where
    T-lookup : {Γ : Ctx} → T' X Γ → T' X Γ → T X Γ

  -- Action of renaming of the residual monad
  T-rename : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → T (set X) Γ → T (set X) Γ'
  T'-rename : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → T' (set X) Γ → T' (set X) Γ'
  T''-rename : {X : Set^Ren} {Γ Γ' : Ctx} → (f : Ren Γ Γ') → T'' (set X) Γ → T'' (set X) Γ'

  T-rename {X} {Γ} {Γ'} f (T-lookup d d') = T-lookup (T'-rename {X} {Γ} {Γ'} f d) (T'-rename {X} {Γ} {Γ'} f d')

  T'-rename {X} {Γ} {Γ'} f (T-update0 d) = T-update0 (T''-rename {X} {Γ} {Γ'} f d)
  T'-rename {X} {Γ} {Γ'} f (T-update1 d) = T-update1 (T''-rename {X} {Γ} {Γ'} f d)

  T''-rename {X} {Γ} {Γ'} f (T-return x) = T-return ((act X) f x)
  T''-rename {X} {Γ} {Γ'} f (T-to {.Γ} {σ} t d) = T-to (⊢ap-rename f t) (T-rename {X} {Γ :: σ} {Γ' :: σ} (wk₂ f) d)

  -- The residual monad on presheaves
  T-Set^Ren : Set^Ren → Set^Ren
  T-Set^Ren X = 
    record {
      set = T (set X);
      act = T-rename {X}
    }

  -- Unit of the residual monad
  η : {X : Set^Ren} → Set^Ren-Map X (T-Set^Ren X)
  η d = T-lookup (T-update0 (T-return d)) (T-update1 (T-return d))


  -- Kleisli extension of the residual monad
  * : {X Y : Set^Ren} → (Set^Ren-Map X (T-Set^Ren Y)) → Set^Ren-Map (T-Set^Ren X) (T-Set^Ren Y)

  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) with f d | f d'
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a) (T-update0 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a) (T-update1 b)
  * f (T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a) (T-update1 b)
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update0 (T-to t' d'))) with f d
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update0 a) (T-update0 a') = T-lookup (T-update0 a) (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update0 a) (T-update1 a') = T-lookup (T-update0 a) (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update1 a) (T-update0 a') = T-lookup (T-update1 a) (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update1 a) (T-update1 a') = T-lookup (T-update1 a) (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-return d'))) with f d' 
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update0 b)
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update0 b)
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update1 b)
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update1 b)
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update0 (T-to t' d'))) = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update0 (T-to t' (* {X} {Y} f d')))

  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) with f d | f d'
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a) (T-update0 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a) (T-update1 b')
  * f (T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a) (T-update0 b')
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update1 (T-to t' d'))) with f d
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update0 a) (T-update0 a') = T-lookup (T-update0 a) (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update0 a) (T-update1 a') = T-lookup (T-update0 a) (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update1 a) (T-update0 a') = T-lookup (T-update1 a) (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update1 a) (T-update1 a') = T-lookup (T-update1 a) (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-return d'))) with f d' 
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update0 b')
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update1 b')
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update0 b')
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update1 b')
  * {X} {Y} f (T-lookup (T-update0 (T-to t d)) (T-update1 (T-to t' d'))) = T-lookup (T-update0 (T-to t (* {X} {Y} f d))) (T-update1 (T-to t' (* {X} {Y} f d')))

  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) with f d | f d'
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a') (T-update0 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a') (T-update1 b)
  * f (T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b)
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update0 (T-to t' d'))) with f d
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update0 a) (T-update0 a') = T-lookup (T-update0 a') (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update0 a) (T-update1 a') = T-lookup (T-update1 a') (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update1 a) (T-update0 a') = T-lookup (T-update0 a') (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update0 (T-to t' d'))) | T-lookup (T-update1 a) (T-update1 a') = T-lookup (T-update1 a') (T-update0 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-return d'))) with f d' 
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update0 b)
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update0 b)
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update1 b)
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-return d'))) | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update1 b)
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update0 (T-to t' d'))) = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update0 (T-to t' (* {X} {Y} f d')))

  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) with f d | f d'
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update0 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update0 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update0 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update0 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 a') (T-update0 b')
  * f (T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) | T-lookup (T-update1 a) (T-update1 a') | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 a') (T-update1 b')
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update1 (T-to t' d'))) with f d
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update0 a) (T-update0 a') = T-lookup (T-update0 a') (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update0 a) (T-update1 a') = T-lookup (T-update1 a') (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update1 a) (T-update0 a') = T-lookup (T-update0 a') (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-return d)) (T-update1 (T-to t' d'))) | T-lookup (T-update1 a) (T-update1 a') = T-lookup (T-update1 a') (T-update1 (T-to t' (* {X} {Y} f d')))
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-return d'))) with f d' 
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update0 b) (T-update0 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update0 b')
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update0 b) (T-update1 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update1 b')
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update1 b) (T-update0 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update0 b')
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-return d'))) | T-lookup (T-update1 b) (T-update1 b') = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update1 b')
  * {X} {Y} f (T-lookup (T-update1 (T-to t d)) (T-update1 (T-to t' d'))) = T-lookup (T-update1 (T-to t (* {X} {Y} f d))) (T-update1 (T-to t' (* {X} {Y} f d')))


  -- Strength of the residual monad
  t-r : {X Y : Set^Ren} → Set^Ren-Map (X ⊗ (T-Set^Ren Y)) (T-Set^Ren (X ⊗ Y))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-return d)) (T-update0 (T-return d'))) = T-lookup (T-update0 (T-return (a , d))) (T-update0 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-return d)) (T-update0 (T-to {.Γ} {σ} t' d'))) = T-lookup (T-update0 (T-return (a , d))) (T-update0 (T-to t' (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d'))))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-to {.Γ} {σ} t d)) (T-update0 (T-return d'))) = T-lookup (T-update0 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update0 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-to {.Γ} {σ} t d)) (T-update0 (T-to {.Γ} {σ'} t' d'))) = T-lookup (T-update0 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update0 (T-to t' (t-r {X} {Y} {Γ :: σ'} (act X wk₁ a , d'))))

  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-return d)) (T-update1 (T-return d'))) = T-lookup (T-update0 (T-return (a , d))) (T-update1 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-return d)) (T-update1 (T-to {.Γ} {σ} t' d'))) = T-lookup (T-update0 (T-return (a , d))) (T-update1 (T-to t' (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d'))))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-to {.Γ} {σ} t d)) (T-update1 (T-return d'))) = T-lookup (T-update0 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update1 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update0 (T-to {.Γ} {σ} t d)) (T-update1 (T-to {.Γ} {σ'} t' d'))) = T-lookup (T-update0 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update1 (T-to t' (t-r {X} {Y} {Γ :: σ'} (act X wk₁ a , d'))))

  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-return d)) (T-update0 (T-return d'))) = T-lookup (T-update1 (T-return (a , d))) (T-update0 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-return d)) (T-update0 (T-to {.Γ} {σ} t' d'))) = T-lookup (T-update1 (T-return (a , d))) (T-update0 (T-to t' (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d'))))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-to {.Γ} {σ} t d)) (T-update0 (T-return d'))) = T-lookup (T-update1 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update0 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-to {.Γ} {σ} t d)) (T-update0 (T-to {.Γ} {σ'} t' d'))) = T-lookup (T-update1 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update0 (T-to t' (t-r {X} {Y} {Γ :: σ'} (act X wk₁ a , d'))))

  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-return d)) (T-update1 (T-return d'))) = T-lookup (T-update1 (T-return (a , d))) (T-update1 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-return d)) (T-update1 (T-to {.Γ} {σ} t' d'))) = T-lookup (T-update1 (T-return (a , d))) (T-update1 (T-to t' (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d'))))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-to {.Γ} {σ} t d)) (T-update1 (T-return d'))) = T-lookup (T-update1 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update1 (T-return (a , d')))
  t-r {X} {Y} {Γ}  (a , T-lookup (T-update1 (T-to {.Γ} {σ} t d)) (T-update1 (T-to {.Γ} {σ'} t' d'))) = T-lookup (T-update1 (T-to t (t-r {X} {Y} {Γ :: σ} (act X wk₁ a , d)))) (T-update1 (T-to t' (t-r {X} {Y} {Γ :: σ'} (act X wk₁ a , d'))))


  -- Components of Kleisli exponentials
  _⇒_ : (X Y : Ctx → Set) → Ctx → Set 
  (X ⇒ Y) Γ = {Γ' : Ctx} → Ren Γ Γ' → X Γ' → T Y Γ'


  -- Algebraic operations for the residual monad (global state operations)
  Alg-lookup :  {X : Set^Ren} → (Set^Ren-Map ((T-Set^Ren X) ⊗ (T-Set^Ren X)) (T-Set^Ren X))
  Alg-lookup (T-lookup (T-update0 a) (T-update0 a') , T-lookup (T-update0 b) (T-update0 b')) = T-lookup (T-update0 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update0 a') , T-lookup (T-update0 b) (T-update1 b')) = T-lookup (T-update0 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update0 a') , T-lookup (T-update1 b) (T-update0 b')) = T-lookup (T-update0 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update0 a') , T-lookup (T-update1 b) (T-update1 b')) = T-lookup (T-update0 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update1 a') , T-lookup (T-update0 b) (T-update0 b')) = T-lookup (T-update0 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update1 a') , T-lookup (T-update0 b) (T-update1 b')) = T-lookup (T-update0 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update1 a') , T-lookup (T-update1 b) (T-update0 b')) = T-lookup (T-update0 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update0 a) (T-update1 a') , T-lookup (T-update1 b) (T-update1 b')) = T-lookup (T-update0 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update0 a') , T-lookup (T-update0 b) (T-update0 b')) = T-lookup (T-update1 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update0 a') , T-lookup (T-update0 b) (T-update1 b')) = T-lookup (T-update1 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update0 a') , T-lookup (T-update1 b) (T-update0 b')) = T-lookup (T-update1 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update0 a') , T-lookup (T-update1 b) (T-update1 b')) = T-lookup (T-update1 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update1 a') , T-lookup (T-update0 b) (T-update0 b')) = T-lookup (T-update1 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update1 a') , T-lookup (T-update0 b) (T-update1 b')) = T-lookup (T-update1 a) (T-update1 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update1 a') , T-lookup (T-update1 b) (T-update0 b')) = T-lookup (T-update1 a) (T-update0 b')
  Alg-lookup (T-lookup (T-update1 a) (T-update1 a') , T-lookup (T-update1 b) (T-update1 b')) = T-lookup (T-update1 a) (T-update1 b')

  Alg-update0 :  {X : Set^Ren} → (Set^Ren-Map (T-Set^Ren X) (T-Set^Ren X))
  Alg-update0 (T-lookup (T-update0 d) (T-update0 d')) = T-lookup (T-update0 d) (T-update0 d)
  Alg-update0 (T-lookup (T-update0 d) (T-update1 d')) = T-lookup (T-update0 d) (T-update0 d)
  Alg-update0 (T-lookup (T-update1 d) (T-update0 d')) = T-lookup (T-update0 d) (T-update0 d)
  Alg-update0 (T-lookup (T-update1 d) (T-update1 d')) = T-lookup (T-update0 d) (T-update0 d)

  Alg-update1 :  {X : Set^Ren} → (Set^Ren-Map (T-Set^Ren X) (T-Set^Ren X))
  Alg-update1 (T-lookup (T-update0 d) (T-update0 d')) = T-lookup (T-update1 d') (T-update1 d')
  Alg-update1 (T-lookup (T-update0 d) (T-update1 d')) = T-lookup (T-update1 d') (T-update1 d')
  Alg-update1 (T-lookup (T-update1 d) (T-update0 d')) = T-lookup (T-update1 d') (T-update1 d')
  Alg-update1 (T-lookup (T-update1 d) (T-update1 d')) = T-lookup (T-update1 d') (T-update1 d')

