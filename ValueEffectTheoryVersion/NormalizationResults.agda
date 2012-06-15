------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
--------------- Normalization Results ----------------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------


open import Utils
open import Syntax
open import Theory
open import NbE
open import Soundness
open import LogicalRelations
open import Substitutions
open import Renamings
open import Presheaves
open import PartialEquivalence
open import PartialEquivalenceLemmas

module NormalizationResults where


  -- First normalization result - normalization preserves normal forms
  normalization-result1-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢nv σ) 
    → nf-v (⊢nv-embed t) ≅ t

  normalization-result1-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢np σ) 
    → nf-p (⊢np-embed t) ≅ t

  normalization-result1-v t = 
      reify-v (⟦ ⊢nv-embed t ⟧v id-env)
    ≅〈 reify-stability-v t 〉
      t 
    ∎
  normalization-result1-p t = 
      reify-p (⟦ ⊢np-embed t ⟧p id-env)
    ≅〈 reify-stability-p t 〉
      t 
    ∎

  
  -- Second normalization result - every term is provably equal to its normal form
  normalization-result2-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢v σ) 
    → Γ ⊢v t ≡ ⊢nv-embed (nf-v t)

  normalization-result2-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢p σ) 
    → Γ ⊢p t ≡ ⊢np-embed (nf-p t)

  normalization-result2-v t = 
      t
    ≡v〈 reify-v-lem t (⟦ t ⟧v id-env) (~v-invariance {t' = t} {d = ⟦ t ⟧v (λ {σ} x → reflect-v (varAV x))} (~v-fundamental-lemma (id-subst) (id-env) t ~c-id-subst-id-env) (≅2≡-v (id-subst-lem-v t))) 〉
      ⊢nv-embed (nf-v t) 
    v∎
  normalization-result2-p t = 
      t
    ≡p〈 reify-p-lem t (⟦ t ⟧p id-env) (~p-invariance {t' = t} {d = ⟦ t ⟧p (λ {σ} x → reflect-v (varAV x))} (~p-fundamental-lemma id-subst id-env t ~c-id-subst-id-env) (≅2≡-p (id-subst-lem-p t))) 〉
      ⊢np-embed (nf-p t) 
    p∎


  -- Third normalization result - provably equal terms have the same normal form
  normalization-result3-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t u : Γ ⊢v σ) 
    → Γ ⊢v t ≡ u 
    → Γ ⊢nv nf-v t ≡ nf-v u

  normalization-result3-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t u : Γ ⊢p σ) 
    → Γ ⊢p t ≡ u 
    → Γ ⊢np nf-p t ≡ nf-p u

  normalization-result3-v t u p = 
      nf-v t
    ≡nv〈 reify-cong-v (soundness-v t u p ≈-id-env) 〉
      nf-v u
    nv∎
  normalization-result3-p t u p = reify-cong-p (soundness-p t u p ≈-id-env)


