------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------------- Substitutions --------------------
------------------------------------------------------

open import Utils
open import Syntax
open import Renamings
open import Presheaves

module Substitutions where


  -- Substitutions (hom-set in the opposite of category of contexts)
  Sub : Ctx → Ctx → Set
  Sub Γ Γ' = {σ : Ty} → σ ∈ Γ → Γ' ⊢v σ


  -- Lifting (or weakening) of substitutions
  lift : {Γ Γ' : Ctx} {σ : Ty} → Sub Γ Γ' → Sub (Γ :: σ) (Γ' :: σ)
  lift s Hd = var Hd
  lift s (Tl x) = ⊢v-rename Tl (s x)


  -- Action of substitution on value and producer terms
  subst-v :  {Γ Γ' : Ctx}  → Sub Γ Γ'  → {σ : Ty}  → Γ ⊢v σ  → Γ' ⊢v σ
  subst-p :  {Γ Γ' : Ctx}  → Sub Γ Γ'  → {σ : Ty}  → Γ ⊢p σ  → Γ' ⊢p σ

  subst-v s (var x) = s x
  subst-v s (proj₁ t) = proj₁ (subst-v s t)
  subst-v s (proj₂ t) = proj₂ (subst-v s t)
  subst-v s (pair t u) = pair (subst-v s t) (subst-v s u)
  subst-v s ⋆ = ⋆
  subst-v s (fn t) = fn (subst-p (lift s) t)

  subst-p s (return t) = return (subst-v s t)
  subst-p s (t to u) = subst-p s t to subst-p (lift s) u
  subst-p s (app t u) = app (subst-v s t) (subst-v s u)
  subst-p s (lookup t u) = lookup (subst-p s t) (subst-p s u)
  subst-p s (update0 t) = update0 (subst-p s t)
  subst-p s (update1 t) = update1 (subst-p s t)


  -- Identity substitution
  id-subst : {Γ : Ctx} → Sub Γ Γ
  id-subst x = var x


  -- Composition of substitutions
  comp-subst : {Γ Γ' Γ'' : Ctx} → Sub Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
  comp-subst s s' = subst-v s · s' 


  -- Extend a substitution
  ext-subst : {Γ Γ' : Ctx} {σ : Ty} → Sub Γ Γ' → Γ' ⊢v σ → Sub (Γ :: σ) Γ'
  ext-subst s t Hd = t
  ext-subst s t (Tl x) = s x


  -- Composing substitutions with renamings in the opposite of category of contexts
  subst-comp-ren : {Γ Γ' Γ'' : Ctx} →  Ren Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
  subst-comp-ren f s = (⊢v-rename f) · s

