------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
--------------------- Soundness ----------------------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------


open import Utils
open import Syntax
open import Theory
open import NbE
open import Presheaves
open import Renamings
open import Substitutions
open import LogicalRelations
open import Lemmas
open import Monad

module Soundness where

  open Σ

  -- Renaming variables in environments before interpreting terms
  env-rename-ext-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {e : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    {d : ⟦ σ ⟧ Γ'} 
    → (x : σ' ∈ (Γ :: σ)) 
    → env-extend (env-rename f e) (⟦⟧-rename {σ} f d) x ≅ ⟦⟧-rename {σ'} f (env-extend e d x)

  env-rename-ext-lem {Γ} {Γ'} {Γ''} {σ} {.σ} {e} {f} {d} Hd = 
      ⟦⟧-rename {σ} f d
    ∎
  env-rename-ext-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {e} {f} {d} (Tl x) = 
      ⟦⟧-rename {σ'} f (e x)
    ∎


  -- Extending environments and exchanging the outermost variables
  env-extend-exchange-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' σ'' : Ty} 
    {e : Env Γ Γ'} 
    {d : ⟦ σ' ⟧ Γ'} 
    {d' : ⟦ σ'' ⟧ Γ'} 
    → (x : σ ∈ (Γ :: σ'')) 
    → env-extend e d' x ≅ env-extend (env-extend {Γ} {Γ'} {σ'} e d) d' (exchange (Tl x))

  env-extend-exchange-lem {Γ} {Γ'} {σ} {σ'} {.σ} {e} {d} {d'} Hd = 
      d'
    ∎
  env-extend-exchange-lem {Γ} {Γ'} {σ} {σ'} {σ''} {e} {d} {d'} (Tl x) = 
      e x
    ∎


  -- Naturality of interpretation of value terms
  ⟦⟧v-naturality : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {e : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⟦⟧-rename {σ} f (⟦ t ⟧v e) ≅ ⟦ t ⟧v (env-rename f e)

  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ} {e} {f} (var t) = 
      ⟦⟧-rename {σ} f (e t)
    ∎
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ} {e} {f} (proj₁ t) = 
      ⟦⟧-rename {σ} f (⟦ proj₁ t ⟧v e)
    ≅〈 cong fst (⟦⟧v-naturality t) 〉
      ⟦ proj₁ t ⟧v (env-rename f e)
    ∎
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ} {e} {f} (proj₂ t) = 
      ⟦⟧-rename {σ} f (⟦ proj₂ t ⟧v e)
    ≅〈 cong snd (⟦⟧v-naturality t) 〉
      ⟦ proj₂ t ⟧v (env-rename f e)
    ∎
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {e} {f} (pair t u) = 
      ⟦⟧-rename {σ₁ ∧ σ₂} f (⟦ pair t u ⟧v e)
    ≅〈 cong2 _,_ (⟦⟧v-naturality t) (⟦⟧v-naturality u) 〉
      ⟦ pair t u ⟧v (env-rename f e)
    ∎
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {One} {e} {f} ⋆ = 
      ⋆
    ∎
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ ⇀ τ} {e} {f} (lam t) = 
      (λ {σ'} → ⟦⟧-rename {σ ⇀ τ} f (⟦ lam t ⟧v e) {σ'})
    ≅〈 iext (λ Γ''' → ext (λ f → ext (λ d → cong ⟦ t ⟧p (iext (λ σ' → cong (λ (x : Env _ _) → env-extend x d) (iext (λ σ'' → ext (λ x → sym (⟦⟧-rename-comp-lem {σ = σ''} (e x)))))))))) 〉
      (λ {σ'} → ⟦ lam t ⟧v (env-rename f e) {σ'})
    ∎
  ⟦⟧v-naturality true = 
      trueNV
    ∎
  ⟦⟧v-naturality false = 
      falseNV
    ∎


  -- Extension and strength lemma
  *-strength-unit-lem : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e : Env Γ Γ'} 
    → (d : T ⟦ σ ⟧ Γ') 
    → d ≅ * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot σ} (λ v → η {Denot σ} (snd v)) (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d))

  *-strength-unit-lem (T-return d) = 
      T-return d
    ∎
  *-strength-unit-lem {Γ} {Γ'} {σ} {e} (T-to {.Γ'} {τ} d d') = 
      T-to d d'
    ≅〈 cong (T-to d) (*-strength-unit-lem {Γ} {Γ' :: τ} {σ} {λ {σ'} z → ⟦⟧-rename {σ'} wk₁ (e z)} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot σ} (λ v → η {Denot σ} (snd v)) (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , (T-to d d')))
    ∎
  *-strength-unit-lem {Γ} {Γ'} {σ} {e} (T-or d d') = 
      T-or d d'
    ≅〈 cong2 T-or (*-strength-unit-lem {Γ} {Γ'} {σ} {e} d) (*-strength-unit-lem {Γ} {Γ'} {σ} {e} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot σ} (λ v → η {Denot σ} (snd v)) (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , (T-or d d')))
    ∎
  *-strength-unit-lem {Γ} {Γ'} {σ} {e} (T-if b d d') = 
      T-if b d d'
    ≅〈 cong2 (T-if b) (*-strength-unit-lem {Γ} {Γ'} {σ} {e} d) (*-strength-unit-lem {Γ} {Γ'} {σ} {e} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot σ} (λ v → η {Denot σ} (snd v)) (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , (T-if b d d')))
    ∎


  -- Lemma about extending the environment and weakening a renaming
  env-extend-rename-wk₂-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    {d : ⟦ σ ⟧ Γ''} 
    → (x : σ' ∈ (Γ :: σ)) 
    → env-extend (λ x' → (e (f x'))) d x ≅ env-extend e d (wk₂ f x)

  env-extend-rename-wk₂-lem {Γ} {Γ'} {Γ''} {σ} {.σ} {f} {e} {d} Hd = 
      d
    ∎
  env-extend-rename-wk₂-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} {d} (Tl x) = 
      e (f x)
    ∎

  
  -- Renaming a term being interpreted is the same as renaming an environment
  rename-env-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⟦ t ⟧v (λ x → ⟦ var (f x) ⟧v e) ≅ ⟦ ⊢v-rename f t ⟧v e

  rename-env-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → ⟦ t ⟧p (λ x → ⟦ var (f x) ⟧v e) ≅ ⟦ ⊢p-rename f t ⟧p e

  *-rename-env-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (u : Γ :: σ' ⊢p σ) → (d : T ⟦ σ' ⟧ Γ'') 
    → * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , d)) 
      ≅ 
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , d))

  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-return d) = 
      ⟦ u ⟧p (env-extend (λ {σ0} z → e (f z)) d)
    ≅〈 cong ⟦ u ⟧p (iext (λ σ' → ext (λ x → env-extend-rename-wk₂-lem x))) 〉
      ⟦ u ⟧p (λ {σ0} z → env-extend e d (wk₂ f z))
    ≅〈 rename-env-lem-p u 〉
      ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend e d)
    ∎
  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-to d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-to d d')))
    ≅〈 cong (T-to d) (*-rename-env-lem u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-to d d')))
    ∎
  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-or d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-or d d')))
    ≅〈 cong2 T-or (*-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u d) (*-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-or d d')))
    ∎
  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-if b d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-if b d d')))
    ≅〈 cong2 (T-if b) (*-rename-env-lem u d) (*-rename-env-lem u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-if b d d')))
    ∎

  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ} {f} {e} (var x) = 
      e (f x)
    ∎
  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ} {f} {e} (proj₁ t) = 
      ⟦ proj₁ t ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong fst (rename-env-lem-v t) 〉
      ⟦ ⊢v-rename f (proj₁ t) ⟧v e
    ∎
  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ} {f} {e} (proj₂ t) = 
      ⟦ proj₂ t ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong snd (rename-env-lem-v t) 〉
      ⟦ ⊢v-rename f (proj₂ t) ⟧v e
    ∎
  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {f} {e} (pair t u) = 
      ⟦ pair t u ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong2 _,_ (rename-env-lem-v t) (rename-env-lem-v u) 〉
      ⟦ ⊢v-rename f (pair t u) ⟧v e
    ∎
  rename-env-lem-v {Γ} {Γ'} {Γ''} {One} {f} {e} ⋆ = 
      ⋆
    ∎
  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {e} (lam t) = 
      (λ {σ'} → ⟦ lam t ⟧v (λ x → ⟦ var (f x) ⟧v e) {σ'})
    ≅〈 iext (λ Γ''' → ext (λ f' → ext (λ d → trans (cong ⟦ t ⟧p (iext (λ σ' → ext (λ x → env-extend-rename-wk₂-lem x)))) (rename-env-lem-p t)))) 〉
      (λ {σ'} → ⟦ ⊢v-rename f (lam t) ⟧v e {σ'})
    ∎
  rename-env-lem-v true = 
      trueNV
    ∎
  rename-env-lem-v false = 
      falseNV
    ∎
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} (return t) = 
      T-return (⟦ t ⟧v (λ {σ'} z → e (f z)))
    ≅〈 cong T-return (rename-env-lem-v t) 〉
      T-return (⟦ ⊢v-rename f t ⟧v e)
    ∎
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} (_to_ {σ'} t u) = 
      ⟦ t to u ⟧p (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (⟦ t ⟧p (λ x → e (f x))) 〉 
      * (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) (t-r (((λ {σ} → e {σ}) , ⟦ t ⟧p (λ x → e (f x)))))
    ≅〈 cong (λ x → * {Env-Denot Γ' ⊗ Denot σ'} {Denot σ} (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , x))) (rename-env-lem-p t) 〉
      ⟦ ⊢p-rename f (t to u) ⟧p e
    ∎
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} (app t u) = 
      ⟦ t ⟧v (λ {σ'} z → e (f z)) (λ {σ'} → id) (⟦ u ⟧v (λ {σ'} z → e (f z)))
    ≅〈 cong2 (λ x y → x id y) (rename-env-lem-v t) (rename-env-lem-v u) 〉
      ⟦ ⊢v-rename f t ⟧v e (λ {σ'} → id) (⟦ ⊢v-rename f u ⟧v e)
    ∎
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} (or t u) = 
      T-or (⟦ t ⟧p (λ z → e (f z))) (⟦ u ⟧p (λ z → e (f z)))
    ≅〈 cong2 T-or (rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} t) (rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} u) 〉
      T-or (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ∎
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} (if b then t else u) = 
      T-if (⟦ b ⟧v (λ {σ'} z → e (f z))) (⟦ t ⟧p (λ {σ'} z → e (f z))) (⟦ u ⟧p (λ {σ'} z → e (f z)))
    ≅〈 cong2 (T-if (⟦ b ⟧v (λ x → e (f x)))) (rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} t) (rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} u) 〉 
      T-if (⟦ b ⟧v (λ {σ'} z → e (f z))) (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ≅〈 cong (λ x → T-if x(⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)) (rename-env-lem-v {Γ} {Γ'} {Γ''} {Bool} {f} {e} b) 〉
      T-if (⟦ ⊢v-rename f b ⟧v e) (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ∎


  -- Extending environments derived from substitutions
  sub-to-env-lift-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' σ'' : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (d : ⟦ σ ⟧ Γ'') 
    → (x : σ'' ∈ (Γ :: σ)) 
    → env-extend (sub-to-env s e) d x ≅ (sub-to-env (lift s) (env-extend e d) x)

  sub-to-env-lift-lem d Hd = 
      d
    ∎
  sub-to-env-lift-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {σ''} {s} {e} d (Tl x) = 
      ⟦ s x ⟧v e
    ≅〈 rename-env-lem-v (s x) 〉
      ⟦ ⊢v-rename wk₁ (s x) ⟧v (env-extend e d)
    ∎


  -- Interpretation maps are natural for substitutions 
  env-extend-subst-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⟦ t ⟧v (sub-to-env s e) ≅ ⟦ subst-v s t ⟧v e

  env-extend-subst-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → ⟦ t ⟧p (sub-to-env s e) ≅ ⟦ subst-p s t ⟧p e

  *-env-extend-subst-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (u : Γ :: σ' ⊢p σ) 
    → (d : T ⟦ σ' ⟧ Γ'') 
    → * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((sub-to-env s e) , d)) 
      ≅ 
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , d))

  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u (T-return d) = 
      ⟦ u ⟧p (env-extend (sub-to-env s e) d)
    ≅〈 cong ⟦ u ⟧p (iext (λ σ' → ext (λ x → sub-to-env-lift-lem {σ' = σ'} d x))) 〉 
      ⟦ u ⟧p (sub-to-env (lift s) (env-extend e d))
    ≅〈 env-extend-subst-lem-p u 〉
      ⟦ subst-p (lift s) u ⟧p (env-extend e d)
    ∎
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u (T-to {.Γ''} {σ''} d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((sub-to-env s e) , (T-to d d')))
    ≅〈 cong (T-to d) (trans (cong (λ (y : Env _ _) → * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'' :: σ''} (y , d'))) (iext (λ σ'' → (ext (λ x → (⟦⟧v-naturality (s x))))))) (*-env-extend-subst-lem u d')) 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-to d d')))
    ∎
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u (T-or d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((sub-to-env s e) , (T-or d d')))
    ≅〈 cong2 T-or (*-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u d) (*-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-or d d')))
    ∎
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u (T-if b d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((sub-to-env s e) , (T-if b d d')))
    ≅〈 cong2 (T-if b) (*-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u d) (*-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-if b d d')))
    ∎

  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {e} (var x) = 
      ⟦ s x ⟧v e
    ∎
  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {e} (proj₁ t) = 
      ⟦ proj₁ t ⟧v (sub-to-env s e)
    ≅〈 cong (fst) (env-extend-subst-lem-v t) 〉
      ⟦ subst-v s (proj₁ t) ⟧v e
    ∎
  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {e} (proj₂ t) = 
      ⟦ proj₂ t ⟧v (sub-to-env s e)
    ≅〈 cong (snd) (env-extend-subst-lem-v t) 〉
      ⟦ subst-v s (proj₂ t) ⟧v e
    ∎
  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {s} {e} (pair t u) = 
      ⟦ pair t u ⟧v (sub-to-env s e)
    ≅〈 cong2 _,_ (env-extend-subst-lem-v t) (env-extend-subst-lem-v u) 〉
      ⟦ subst-v s (pair t u) ⟧v e
    ∎
  env-extend-subst-lem-v ⋆ = 
      ⋆
    ∎
  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {s} {e} (lam t) = 
      (λ {σ} → ⟦ lam t ⟧v (sub-to-env s e) {σ})
    ≅〈 iext (λ Γ''' → ext (λ f → ext (λ d → trans (cong ⟦ t ⟧p (iext (λ σ'' → ext (λ x → trans (cong (λ (y : Env _ _) → env-extend y d x) (iext (λ σ'' → ext (λ y → ⟦⟧v-naturality (s y))))) (sub-to-env-lift-lem {σ = σ} {σ' = σ''} {σ'' = σ''} d x))))) (env-extend-subst-lem-p t)))) 〉
      (λ {σ} → ⟦ subst-v s (lam t) ⟧v e {σ})
    ∎
  env-extend-subst-lem-v true = 
      trueNV
    ∎
  env-extend-subst-lem-v false = 
      falseNV
    ∎
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} (return t) = 
      T-return (⟦ t ⟧v (sub-to-env s e))
    ≅〈 cong T-return (env-extend-subst-lem-v t) 〉
      T-return (⟦ subst-v s t ⟧v e)
    ∎
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} (_to_ {σ'} t u) = 
      ⟦ t to u ⟧p (sub-to-env s e)
    ≅〈 *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} u (⟦ t ⟧p (λ {σ'} x → ⟦ s x ⟧v e)) 〉
      * (λ v → ⟦ subst-p (lift s) u ⟧p (λ {σ} → env-extend (fst v {_}) (snd v) {σ})) (t-r ((λ {σ} → e {σ}) , ⟦ t ⟧p (λ x → ⟦ s x ⟧v e)))
    ≅〈 cong (λ x → * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , x))) (env-extend-subst-lem-p t) 〉
      ⟦ subst-p s (t to u) ⟧p e
    ∎
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} (app t u) = 
      ⟦ app t u ⟧p (sub-to-env s e)
    ≅〈 cong2 (λ x y → x id y) (env-extend-subst-lem-v t) (env-extend-subst-lem-v u) 〉
      ⟦ subst-v s t ⟧v e (λ {σ'} → id) (⟦ subst-v s u ⟧v e)
    ∎
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} (or t u) = 
      T-or (⟦ t ⟧p (sub-to-env s e)) (⟦ u ⟧p (sub-to-env s e))
    ≅〈 cong2 T-or (env-extend-subst-lem-p t) (env-extend-subst-lem-p u) 〉
      T-or (⟦ subst-p s t ⟧p e) (⟦ subst-p s u ⟧p e)
    ∎
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} (if b then t else u) = 
      T-if (⟦ b ⟧v (sub-to-env s e)) (⟦ t ⟧p (sub-to-env s e)) (⟦ u ⟧p (sub-to-env s e))
    ≅〈 cong2 (T-if (⟦ b ⟧v (sub-to-env s e))) (env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} t) (env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} u) 〉 
      T-if (⟦ b ⟧v (sub-to-env s e)) (⟦ subst-p s t ⟧p e) (⟦ subst-p s u ⟧p e)
    ≅〈 cong (λ x → T-if x (⟦ subst-p s t ⟧p e) (⟦ subst-p s u ⟧p e)) (env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {e} b) 〉
      T-if (⟦ subst-v s b ⟧v e) (⟦ subst-p s t ⟧p e) (⟦ subst-p s u ⟧p e)
    ∎


  **-strength-lem' : 
    {Γ Γ' : Ctx} 
    {σ σ' τ : Ty} 
    {e : Env Γ Γ'} 
    {v : Γ :: τ ⊢p σ} 
    {d : ⟦ σ' ⟧ Γ'} 
    → (d' : T ⟦ τ ⟧ Γ') 
    → * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) 
         (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , d')) 
       ≅ 
       * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) 
         (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ'} ((λ {σ} → env-extend e d {σ}) , d'))

  **-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} (T-return d') = 
      ⟦ v ⟧p (env-extend e d')
    ≅〈 cong ⟦ v ⟧p (iext (λ σ''' → ext (λ x → env-extend-exchange-lem {Γ} {Γ'} {σ'''} {σ'} {τ} {e} {d} {d'} x))) 〉
      ⟦ v ⟧p (λ z → env-extend (env-extend e d) d' (exchange (Tl z)))
    ≅〈 rename-env-lem-p v 〉 
      ⟦ ⊢p-rename (comp-ren exchange wk₁) v ⟧p (env-extend (env-extend e d) d')
    ≅〈 (cong (λ x → ⟦ x ⟧p (env-extend (env-extend e d) d')) (sym (⊢p-rename-comp-lem v))) 〉
      ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (env-extend e d) d')
    ∎
  **-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} (T-to {.Γ'} {σ''} d' d'') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , (T-to d' d'')))
    ≅〈 cong (T-to d') (trans (**-strength-lem' {Γ} {Γ' :: σ''} {σ} {σ'} {τ} {λ {σ0} z → ⟦⟧-rename {σ0} wk₁ (e z)} {v} {⟦⟧-rename {σ'} wk₁ d} d'') (cong (λ (x : Env _ _) → * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename (λ {σ0} → Tl) v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ' :: σ''} ((λ {σ} → x {σ}) , d''))) (iext (λ σ''' → ext env-rename-ext-lem)))) 〉
      * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ'} ((λ {σ} → env-extend e d {σ}) , (T-to d' d'')))
    ∎
  **-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} (T-or d' d'') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , (T-or d' d'')))
    ≅〈 cong2 T-or (**-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} d') (**-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} d'') 〉
      * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ'} ((λ {σ} → env-extend e d {σ}) , (T-or d' d'')))
    ∎
  **-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} (T-if b d' d'') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , (T-if b d' d'')))
    ≅〈 cong2 (T-if b) (**-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} d') (**-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} {d} d'') 〉
      * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ'} ((λ {σ} → env-extend e d {σ}) , (T-if b d' d'')))
    ∎


  **-strength-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' τ : Ty} 
    {e : Env Γ Γ'} 
    {u : Γ :: σ' ⊢p τ} 
    {v : Γ :: τ ⊢p σ} 
    → (d : T ⟦ σ' ⟧ Γ') 
    → * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) 
        (t-r {Env-Denot Γ} {Denot τ} {Γ'}
          ((λ {σ} → e {σ}) , 
            * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot τ} (λ v' → ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))) 
              (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , d)))) 
      ≅ 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ {Γ''} v' → 
        * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) 
          (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend (fst v' {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))))) 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , d))

  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} (T-return d) = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot τ} (λ v' → ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-return d)))))
    ≅〈 **-strength-lem' {Γ} {Γ'} {σ} {σ'} {τ} {e} {v} (⟦ u ⟧p (env-extend e d)) 〉
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ {Γ''} v' → * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend (fst v' {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-return d)))
    ∎
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} (T-to {.Γ'} {σ''} d d') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot τ} (λ v' → ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-to d d')))))
    ≅〈 cong (T-to d) (**-strength-lem {Γ} {Γ' :: σ''} {σ} {σ'} {τ} {env-rename wk₁ e} {u} {v} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ {Γ''} v' → * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend (fst v' {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-to d d')))
    ∎
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} (T-or d d') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot τ} (λ v' → ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-or d d')))))
    ≅〈 cong2 T-or (**-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} d) (**-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ {Γ''} v' → * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend (fst v' {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-or d d')))
    ∎
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} (T-if b d d') = 
      * {(Env-Denot Γ) ⊗ (Denot τ)} {Denot σ} (λ v' → ⟦ v ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot τ} {Γ'} ((λ {σ} → e {σ}) , * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot τ} (λ v' → ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-if b d d')))))
    ≅〈 cong2 (T-if b) (**-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} d) (**-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} d') 〉
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ {Γ''} v' → * {(Env-Denot (Γ :: σ')) ⊗ (Denot τ)} {Denot σ} (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend (fst v0 {_}) (snd v0))) (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend (fst v' {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend (fst v' {_}) (snd v'))))) (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , (T-if b d d')))
    ∎



  -- Soundness of the residualising interpretations
  soundness-v : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e : Env Γ Γ'} 
    → (t u : Γ ⊢v σ) 
    → Γ ⊢v t ≡ u 
    → ⟦ t ⟧v e ≅ ⟦ u ⟧v e

  soundness-p : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e : Env Γ Γ'} 
    → (t u : Γ ⊢p σ) 
    → Γ ⊢p t ≡ u 
    → ⟦ t ⟧p e ≅ ⟦ u ⟧p e

  soundness-v {Γ} {Γ'} {σ} {e} .u u ≡-refl = 
      ⟦ u ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} t u (≡-sym p) = 
      ⟦ t ⟧v e
    ≅〈 sym (soundness-v u t p) 〉
      ⟦ u ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} t v (≡-trans {.Γ} {.σ} {.t} {u} {.v} p q) = 
      ⟦ t ⟧v e
    ≅〈 soundness-v t u p 〉 
      ⟦ u ⟧v e
    ≅〈 soundness-v u v q 〉
      ⟦ v ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ₁ ∧ σ₂} {e} .(pair t u) .(pair t' u') (congpair {.Γ} {.σ₁} {.σ₂} {t} {t'} {u} {u'} p q) = 
      ⟦ t ⟧v e , ⟦ u ⟧v e
    ≅〈 cong2 _,_ (soundness-v t t' p) (soundness-v u u' q) 〉
      ⟦ t' ⟧v e , ⟦ u' ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} .(proj₁ t) .(proj₁ t') (congproj₁ {.Γ} {.σ} {σ₂} {t} {t'} p) = 
      ⟦ proj₁ t ⟧v e
    ≅〈 cong fst (soundness-v t t' p) 〉
      ⟦ proj₁ t' ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} .(proj₂ t) .(proj₂ t') (congproj₂ {.Γ} {σ₁} {.σ} {t} {t'} p) = 
      ⟦ proj₂ t ⟧v e
    ≅〈 cong snd (soundness-v t t' p) 〉
      ⟦ proj₂ t' ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ ⇀ τ} {e} .(lam t) .(lam t') (conglam {.Γ} {.σ} {.τ} {t} {t'} p) = 
      (λ {σ} → ⟦ lam t ⟧v e {σ})
    ≅〈 iext (λ Γ'' → ext (λ f → ext (λ u → soundness-p t t' p))) 〉
      (λ {σ} → ⟦ lam t' ⟧v e {σ})
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} .(proj₁ (pair u u')) u (β×₁ {.Γ} {.σ} {σ₂} {.u} {u'}) = 
      ⟦ u ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ} {e} .(proj₂ (pair t u)) u (β×₂ {.Γ} {σ₁} {.σ} {t}) = 
      ⟦ u ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {One} {e} t .⋆ η⋆ with ⟦ t ⟧v e
  soundness-v {Γ} {Γ'} {One} t .⋆ η⋆ | ⋆ = 
      ⋆
    ∎
  soundness-v {Γ} {Γ'} {σ₁ ∧ σ₂} {e} t .(pair (proj₁ t) (proj₂ t)) η× = 
      ⟦ t ⟧v e
    ∎
  soundness-v {Γ} {Γ'} {σ ⇀ τ} {e} .(lam (app (⊢v-rename (λ {σ} → Tl) u) (var Hd))) u η⇀ = 
      (λ {σ'} → ⟦ lam (app (⊢v-rename (λ {σ} → Tl) u) (var Hd)) ⟧v e {σ'})
    ≅〈 iext (λ Γ'' → ext (λ f → ext (λ d → trans (cong (λ x → x id d) (sym (rename-env-lem-v u))) (cong (λ x → x id d) (sym (⟦⟧v-naturality u)))))) 〉
      (λ {σ'} → ⟦ u ⟧v e {σ'})
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .u u ≡-refl = 
      ⟦ u ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} t u (≡-sym p) = 
      ⟦ t ⟧p e
    ≅〈 sym (soundness-p u t p) 〉
      ⟦ u ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} t v (≡-trans {.Γ} {.σ} {.t} {u} {.v} p q) = 
      ⟦ t ⟧p e
    ≅〈 soundness-p t u p 〉 
      ⟦ u ⟧p e
    ≅〈 soundness-p u v q 〉
      ⟦ v ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(app t u) .(app t' u') (congapp {.Γ} {σ'} {.σ} {t} {t'} {u} {u'} p q) = 
      (⟦ t ⟧v e) id-ren (⟦ u ⟧v e)
    ≅〈 cong2 (λ x y → x id y) (soundness-v t t' p) (soundness-v u u' q) 〉
      (⟦ t' ⟧v e) id-ren (⟦ u' ⟧v e)
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(t to u) .(t' to u') (congto {.Γ} {σ'} {.σ} {t} {t'} {u} {u'} p q) = 
      ⟦ t to u ⟧p e
    ≅〈 cong2 (λ (x : (Set^Ctx-Map ((Env-Denot Γ) ⊗ (Denot σ')) (T-Set^Ctx (Denot σ)))) y → * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} x (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , y))) (iext (λ Γ'' → ext (λ v → soundness-p {e = (env-extend ((fst v) {_}) (snd v))} u u' q))) (soundness-p t t' p) 〉
      ⟦ t' to u' ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(return t) .(return t') (congreturn {.Γ} {.σ} {t} {t'} p) = 
      T-return (⟦ t ⟧v e)
    ≅〈 cong T-return (soundness-v t t' p) 〉
      T-return (⟦ t' ⟧v e)
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(or t u) .(or t' u') (congor {.Γ} {.σ} {t} {t'} {u} {u'} p q) = 
      T-or (⟦ t ⟧p e) (⟦ u ⟧p e)
    ≅〈 cong2 T-or (soundness-p t t' p) (soundness-p u u' q) 〉
      T-or (⟦ t' ⟧p e) (⟦ u' ⟧p e)
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(if b then t else u) .(if b' then t' else u') (congif {.Γ} {.σ} {b} {b'} {t} {u} {t'} {u'} p q r) =       T-if (⟦ b ⟧v e) (⟦ t ⟧p e) (⟦ u ⟧p e)
    ≅〈 cong2 (T-if (⟦ b ⟧v e)) (soundness-p t t' q) (soundness-p u u' r) 〉 
      T-if (⟦ b ⟧v e) (⟦ t' ⟧p e) (⟦ u' ⟧p e)
    ≅〈 cong (λ x → T-if x (⟦ t' ⟧p e) (⟦ u' ⟧p e)) (soundness-v b b' p) 〉
      T-if (⟦ b' ⟧v e) (⟦ t' ⟧p e) (⟦ u' ⟧p e)
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(subst-p (ext-subst id-subst u) t) .(app (lam t) u) (β⇀ {.Γ} {σ'} {.σ} {t} {u}) = 
      ⟦ subst-p (ext-subst id-subst u) t ⟧p e
    ≅〈 sym (trans (cong ⟦ t ⟧p (iext (λ σ''' → ext (λ x → sym (sub-to-env-ext-lem u x))))) (env-extend-subst-lem-p t)) 〉
      ⟦ t ⟧p (env-extend e (⟦ u ⟧v e))
    ≅〈 cong (λ (x : Env _ _) → ⟦ t ⟧p (env-extend x (⟦ u ⟧v e)) ) (iext (λ σ'' → ext (λ x → sym (⟦⟧-rename-id-lem {σ''} (e x))))) 〉
      ⟦ t ⟧p (env-extend (env-rename id-ren e) (⟦ u ⟧v e))
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(return u to t) .(subst-p (ext-subst id-subst u) t) (βto {.Γ} {σ'} {.σ} {t} {u}) = 
      ⟦ t ⟧p (env-extend (sub-to-env id-subst e) (⟦ u ⟧v e))
    ≅〈 cong ⟦ t ⟧p (iext (λ σ''' → ext (λ x → sym (sub-to-env-ext-lem u x)))) 〉 
      ⟦ t ⟧p (sub-to-env (ext-subst id-subst u) e)
    ≅〈 env-extend-subst-lem-p t 〉
      ⟦ subst-p (ext-subst id-subst u) t ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} t .(t to return (var Hd)) ηto = 
      ⟦ t ⟧p e
    ≅〈 *-strength-unit-lem {Γ} {Γ'} {σ} {e} (⟦ t ⟧p e) 〉
      * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot σ} (λ v → η {Denot σ} (snd v)) (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , (⟦ t ⟧p e)))
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .((t to u) to v) .(t to (u to ⊢p-rename exchange (⊢p-rename (λ {σ} → Tl) v))) (assocto {.Γ} {σ'} {τ} {.σ} {t} {u} {v}) = 
      ⟦ (t to u) to v ⟧p e
    ≅〈 **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {u} {v} (⟦ t ⟧p e) 〉
      ⟦ t to (u to ⊢p-rename exchange (⊢p-rename wk₁ v)) ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .(or t u to v) .(or (t to v) (u to v)) (orto {.Γ} {σ'} {.σ} {t} {u} {v}) = 
      ⟦ or t u to v ⟧p e
    ∎
  soundness-p {Γ} {Γ'} {σ} {e} .((if b then t else u) to v) .(if b then (t to v) else (u to v)) (ifto {.Γ} {σ'} {.σ} {b} {t} {u} {v}) = 
      ⟦ (if b then t else u) to v ⟧p e
    ∎


  -- Renaming reflection with wk₁ moves wk₁ under reflection
  env-ext-reflect-lem : 
    {Γ : Ctx} 
    {σ σ' : Ty} 
    → (x : σ' ∈ (Γ :: σ)) 
    → (env-extend (env-rename wk₁ id-env) (reflect-v (varAV (Hd {_} {σ}))) x) ≅ id-env x

  env-ext-reflect-lem {Γ} {σ} {.σ} Hd = 
      reflect-v {σ} (varAV Hd)
    ∎
  env-ext-reflect-lem {Γ} {σ} {σ'} (Tl x) = 
      ⟦⟧-rename {σ'} wk₁ (reflect-v (varAV x))
    ≅〈 reflect-naturality-v (varAV x) 〉
      reflect-v {σ'} (varAV (Tl x))
    ∎


  -- Stability of the reflection and reification functions ("reification is the inverse of evaluation")
  reify-stability-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢nv σ) 
    → reify-v {σ} (⟦ ⊢nv-embed t ⟧v id-env) ≅ t

  reify-stability-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢np σ) 
    → reify-p {σ} (⟦ ⊢np-embed t ⟧p id-env) ≅ t

  reflect-stability-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢av σ) 
    → ⟦ ⊢av-embed t ⟧v id-env ≅ reflect-v t

  reflect-stability-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢ap σ) 
    → ⟦ ⊢ap-embed t ⟧p id-env ≅ reflect-p t  

  reify-stability-v (av2NV (varAV x)) = 
      av2NV (varAV x)
    ∎
  reify-stability-v (av2NV (proj₁AV t)) = 
      fst (⟦ ⊢av-embed t ⟧v id-env) 
    ≅〈 cong fst (reflect-stability-v t) 〉
      av2NV (proj₁AV t)
    ∎
  reify-stability-v (av2NV (proj₂AV t)) = 
      snd (⟦ ⊢av-embed t ⟧v id-env)
    ≅〈 cong snd (reflect-stability-v t) 〉
      av2NV (proj₂AV t)
    ∎
  reify-stability-v (bav2NV (varAV x)) = 
      bav2NV (varAV x)
    ∎
  reify-stability-v (bav2NV (proj₁AV t)) = 
      fst (⟦ ⊢av-embed t ⟧v id-env)
    ≅〈 cong fst (reflect-stability-v t) 〉
      bav2NV (proj₁AV t)
    ∎
  reify-stability-v (bav2NV (proj₂AV t)) = 
      snd (⟦ ⊢av-embed t ⟧v id-env)
    ≅〈 cong snd (reflect-stability-v t) 〉
      bav2NV (proj₂AV t)
    ∎
  reify-stability-v unitNV = 
      unitNV
    ∎
  reify-stability-v trueNV = 
      trueNV
    ∎
  reify-stability-v falseNV = 
      falseNV
    ∎
  reify-stability-v (pairNV t u) = 
      pairNV (reify-v (⟦ ⊢nv-embed t ⟧v id-env)) (reify-v (⟦ ⊢nv-embed u ⟧v id-env))
    ≅〈 cong2 pairNV (reify-stability-v t) (reify-stability-v u) 〉
      pairNV t u
    ∎
  reify-stability-v {Γ} {σ ⇀ τ} (lamNV t) = 
      lamNV (reify-p (⟦ ⊢np-embed t ⟧p (env-extend (env-rename wk₁ id-env) (reflect-v {σ} (varAV Hd)))))
    ≅〈 cong lamNV (trans (cong reify-p (cong ⟦ ⊢np-embed t ⟧p (iext (λ σ' → ext env-ext-reflect-lem)))) (reify-stability-p t)) 〉
      lamNV t
    ∎
  reify-stability-p (returnNP u) = 
      returnNP (reify-v (⟦ ⊢nv-embed u ⟧v id-env))
    ≅〈 cong returnNP (reify-stability-v u) 〉
      returnNP u
    ∎
  reify-stability-p {Γ} {σ} (toNP {σ'} {.σ} t u) = 
      reify-p {σ} (⟦ ⊢np-embed (toNP t u) ⟧p id-env)
    ≅〈 cong (λ y → reify-p (* {(Env-Denot Γ) ⊗ (Denot σ')}{Denot σ}(λ v → ⟦ ⊢np-embed u ⟧p (env-extend ((fst v) {_}) (snd v))) {Γ} (t-r {Env-Denot Γ} {Denot σ'} {Γ} ((λ {σ'} x → reflect-v (varAV x)) , y)))) (reflect-stability-p t) 〉
      toNP t (reify-p (⟦ ⊢np-embed u ⟧p (env-extend (env-rename wk₁ id-env) (reflect-v {σ'} (varAV Hd)))))
    ≅〈 cong (toNP t) (trans (cong reify-p (cong ⟦ ⊢np-embed u ⟧p (iext (λ σ'' → ext (env-ext-reflect-lem))))) (reify-stability-p u)) 〉
      toNP t u
    ∎
  reify-stability-p (orNP t u) = 
      orNP (reify-p (⟦ ⊢np-embed t ⟧p id-env)) (reify-p (⟦ ⊢np-embed u ⟧p id-env))
    ≅〈 cong2 orNP (reify-stability-p t) (reify-stability-p u) 〉
      orNP t u
    ∎
  reify-stability-p (ifNP_then_else b t u) = 
      ifNP (⟦ ⊢nv-embed b ⟧v id-env) then reify-p (⟦ ⊢np-embed t ⟧p id-env) else (reify-p (⟦ ⊢np-embed u ⟧p id-env))
    ≅〈 cong (λ x → reify-p (T-if x (⟦ ⊢np-embed t ⟧p id-env) (⟦ ⊢np-embed u ⟧p id-env))) (reify-stability-v b) 〉
      ifNP b then reify-p (⟦ ⊢np-embed t ⟧p id-env) else (reify-p (⟦ ⊢np-embed u ⟧p id-env))
    ≅〈 cong2 (λ x y → ifNP b then x else y) (reify-stability-p t) (reify-stability-p u) 〉
      ifNP b then t else u
    ∎

  reflect-stability-v (varAV x) = 
      reflect-v (varAV x)
    ∎
  reflect-stability-v (proj₁AV t) = 
      fst (⟦ ⊢av-embed t ⟧v id-env)
    ≅〈 cong fst (reflect-stability-v t) 〉
      reflect-v (proj₁AV t)
    ∎
  reflect-stability-v (proj₂AV t) = 
      snd (⟦ ⊢av-embed t ⟧v id-env)
    ≅〈 cong snd (reflect-stability-v t) 〉
      reflect-v (proj₂AV t)
    ∎
  reflect-stability-p {Γ} {σ} (appAP t u) = 
      (⟦ ⊢av-embed t ⟧v id-env) (λ {σ'} z → z) (⟦ ⊢nv-embed u ⟧v (λ {σ'} z → reflect-v (varAV z)))
    ≅〈 cong (λ y → y id-ren (⟦ ⊢nv-embed u ⟧v (λ {σ} x → reflect-v (varAV x)))) (reflect-stability-v t) 〉
      T-to (appAP (⊢av-rename id-ren t) (reify-v (⟦ ⊢nv-embed u ⟧v id-env))) (T-return (reflect-v {σ} (varAV Hd)))
    ≅〈 cong (λ y → T-to y (T-return (reflect-v {σ} (varAV Hd)))) ((cong2 appAP (⊢av-rename-id-lem t) (reify-stability-v u))) 〉
      T-to (appAP t u) (T-return (reflect-v {σ} (varAV Hd)))
    ∎


