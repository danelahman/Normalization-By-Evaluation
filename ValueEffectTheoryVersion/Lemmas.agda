------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
---------------------- Lemmas ------------------------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------

open import Utils
open import Syntax
open import Substitutions
open import Presheaves
open import Renamings
open import Theory
open import NbE
open import Monad

module Lemmas where


  -- From substitutions to environments
  sub-to-env : {Γ Γ' : Ctx} → (s : Sub Γ Γ') → Set^Ctx-Map (Env-Denot Γ') (Env-Denot Γ) 
  sub-to-env s e x = ⟦ s x ⟧v e


  -- How sub-to-env acts on substitution extensions
  sub-to-env-ext-lem' : {Γ Γ' Γ'' : Ctx} {σ σ' : Ty} {s : Sub Γ Γ'} {e : Env Γ' Γ''} → (u : Γ' ⊢v σ) → (x : σ' ∈ (Γ :: σ)) → sub-to-env (ext-subst s u) e x ≅ (env-extend (sub-to-env s e) (⟦ u ⟧v e)) x

  sub-to-env-ext-lem' {_} {_} {_} {σ} {.σ} {s} {e} u Hd = 
      ⟦ u ⟧v e
    ∎
  sub-to-env-ext-lem' {_} {_} {_} {_} {_} {s} {e} u (Tl x) = 
      ⟦ s x ⟧v e
    ∎


  -- Naturality of embeddings
  ⊢nv-embed-naturality : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢nv σ) 
    → Γ' ⊢v ⊢v-rename f (⊢nv-embed t) ≡ ⊢nv-embed (⊢nv-rename f t)

  ⊢av-embed-naturality : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢av σ) 
    → Γ' ⊢v ⊢v-rename f (⊢av-embed t) ≡ ⊢av-embed (⊢av-rename f t)

  ⊢np-embed-naturality : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢np σ) 
    → Γ' ⊢p ⊢p-rename f (⊢np-embed t) ≡ ⊢np-embed (⊢np-rename f t)

  ⊢ap-embed-naturality : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢ap σ) 
    → Γ' ⊢p ⊢p-rename f (⊢ap-embed t) ≡ ⊢ap-embed (⊢ap-rename f t)

  ⊢nv-embed-naturality (av2NV t) = 
      ⊢v-rename _ (⊢av-embed t)
    ≡v〈 ⊢av-embed-naturality t 〉
      ⊢av-embed (⊢av-rename _ t) 
    v∎
  ⊢nv-embed-naturality (bav2NV b) = 
      ⊢v-rename _ (⊢av-embed b)
    ≡v〈 ⊢av-embed-naturality b 〉
      ⊢av-embed (⊢av-rename _ b) 
    v∎
  ⊢nv-embed-naturality unitNV = 
      ⋆ 
    v∎
  ⊢nv-embed-naturality trueNV = 
      true
    v∎
  ⊢nv-embed-naturality falseNV = 
      false
    v∎
  ⊢nv-embed-naturality (pairNV t u) = 
      pair (⊢v-rename _ (⊢nv-embed t)) (⊢v-rename _ (⊢nv-embed u))
    ≡v〈 congpair (⊢nv-embed-naturality t) (⊢nv-embed-naturality u) 〉
      pair (⊢nv-embed (⊢nv-rename _ t)) (⊢nv-embed (⊢nv-rename _ u)) 
    v∎
  ⊢nv-embed-naturality (lamNV t) = 
      lam (⊢p-rename (wk₂ _) (⊢np-embed t)) 
    ≡v〈 conglam (⊢np-embed-naturality t) 〉
      lam (⊢np-embed (⊢np-rename (wk₂ _) t)) 
    v∎
  ⊢av-embed-naturality {Γ} {Γ'} {σ} {f} (varAV x) = 
      var {Γ'} {σ} (f x) 
    v∎
  ⊢av-embed-naturality (proj₁AV t) = 
      proj₁ (⊢v-rename _ (⊢av-embed t)) 
    ≡v〈 congproj₁ (⊢av-embed-naturality t) 〉
      proj₁ (⊢av-embed (⊢av-rename _ t)) 
    v∎
  ⊢av-embed-naturality (proj₂AV t) = 
      proj₂ (⊢v-rename _ (⊢av-embed t))
    ≡v〈 congproj₂ (⊢av-embed-naturality t) 〉
      proj₂ (⊢av-embed (⊢av-rename _ t)) 
    v∎
  ⊢np-embed-naturality (returnNP t) = 
      return (⊢v-rename _ (⊢nv-embed t))
    ≡p〈 congreturn (⊢nv-embed-naturality t) 〉
      return (⊢nv-embed (⊢nv-rename _ t)) 
    p∎
  ⊢np-embed-naturality (toNP t u) = 
      ⊢p-rename _ (⊢ap-embed t) to ⊢p-rename (wk₂ _) (⊢np-embed u)
    ≡p〈 congto (⊢ap-embed-naturality t) (⊢np-embed-naturality u) 〉
      ⊢ap-embed (⊢ap-rename _ t) to ⊢np-embed (⊢np-rename (wk₂ _) u) 
    p∎
  ⊢np-embed-naturality (orNP t u) = 
      or (⊢p-rename _ (⊢np-embed t)) (⊢p-rename _ (⊢np-embed u))
    ≡p〈 congor (⊢np-embed-naturality t) (⊢np-embed-naturality u) 〉
      or (⊢np-embed (⊢np-rename _ t)) (⊢np-embed (⊢np-rename _ u)) 
    p∎
  ⊢np-embed-naturality (ifNP b then t else u) = 
      if (⊢v-rename _ (⊢nv-embed b)) then (⊢p-rename _ (⊢np-embed t)) else (⊢p-rename _ (⊢np-embed u))
    ≡p〈 congif (⊢nv-embed-naturality b) (⊢np-embed-naturality t) (⊢np-embed-naturality u) 〉
      if (⊢nv-embed (⊢nv-rename _ b)) then (⊢np-embed (⊢np-rename _ t)) else (⊢np-embed (⊢np-rename _ u)) 
    p∎
  ⊢ap-embed-naturality (appAP t u) = 
      app (⊢v-rename _ (⊢av-embed t)) (⊢v-rename _ (⊢nv-embed u))
    ≡p〈 congapp (⊢av-embed-naturality t) (⊢nv-embed-naturality u) 〉
      app (⊢av-embed (⊢av-rename _ t)) (⊢nv-embed (⊢nv-rename _ u)) 
    p∎


  -- Lifting weakenings
  rename-wk₂-lift-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ' Γ''} 
    {f : Ren Γ Γ'} 
    → (x : σ ∈ (Γ :: τ)) 
    → lift s (wk₂ f x) ≅ lift (λ {σ} x' → s (f x')) x

  rename-wk₂-lift-lem Hd = 
      var Hd
    ∎
  rename-wk₂-lift-lem {Γ} {Γ'} {Γ''} {σ} {τ} {s} {f} (Tl x) = 
      ⊢v-rename wk₁ (s (f x))
    ∎


  -- How lifting can be weakened
  rename-wk₂-lift-lem2 : 
    {Γ Γ' Γ'' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (x : σ ∈ (Γ :: τ)) 
    → ⊢v-rename (wk₂ f) (lift s x) ≅ lift (subst-rename f s) x 

  rename-wk₂-lift-lem2 Hd = 
      var Hd
    ∎
  rename-wk₂-lift-lem2 {Γ} {Γ'} {Γ''} {σ} {τ} {s} {f} (Tl x) = 
      ⊢v-rename (wk₂ f) (⊢v-rename wk₁ (s x))
    ≅〈 ⊢v-rename-comp-lem (s x) 〉 
      ⊢v-rename (comp-ren wk₁ f) (s x)
    ≅〈 sym (⊢v-rename-comp-lem (s x)) 〉
      ⊢v-rename wk₁ (⊢v-rename f (s x))
    ∎


  -- Renaming a substitution
  rename-subst-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⊢v-rename f (subst-v s t) ≅ subst-v (subst-rename f s) t

  rename-subst-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → ⊢p-rename f (subst-p s t) ≅ subst-p (subst-rename f s) t

  rename-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (var x) = 
      ⊢v-rename f (s x)
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (proj₁ t) = 
      proj₁ (⊢v-rename f (subst-v s t))
    ≅〈 cong proj₁ (rename-subst-lem-v t) 〉
      proj₁ (subst-v (subst-rename f s) t)
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (proj₂ t) = 
      proj₂ (⊢v-rename f (subst-v s t))
    ≅〈 cong proj₂ (rename-subst-lem-v t) 〉
      proj₂ (subst-v (subst-rename f s) t)
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {s} {f} (pair t u) = 
      pair (⊢v-rename f (subst-v s t)) (⊢v-rename f (subst-v s u))
    ≅〈 cong2 pair (rename-subst-lem-v t) (rename-subst-lem-v u) 〉
      pair (subst-v (subst-rename f s) t) (subst-v (subst-rename f s) u)
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {One} {s} {f} ⋆ = 
      ⋆
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {f} true = 
      true
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {f} false = 
      false
    ∎
  rename-subst-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {s} {f} (lam t) = 
      lam (⊢p-rename (wk₂ f) (subst-p (lift s) t))
    ≅〈 cong lam (trans (rename-subst-lem-p t) (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ → ext rename-wk₂-lift-lem2)))) 〉
      lam (subst-p (lift (subst-rename f s)) t)
    ∎
  rename-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (return t) = 
      return (⊢v-rename f (subst-v s t))
    ≅〈 cong return (rename-subst-lem-v t) 〉
      return (subst-v (subst-rename f s) t)
    ∎
  rename-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (t to u) = 
      ⊢p-rename f (subst-p s t) to ⊢p-rename (wk₂ f) (subst-p (lift s) u)
    ≅〈 cong2 _to_ (rename-subst-lem-p t) (trans (rename-subst-lem-p u) (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ σ → ext rename-wk₂-lift-lem2)))) 〉
      subst-p (subst-rename f s) t to subst-p (lift (subst-rename f s)) u
    ∎
  rename-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (app t u) = 
      app (⊢v-rename f (subst-v s t)) (⊢v-rename f (subst-v s u))
    ≅〈 cong2 app (rename-subst-lem-v t) (rename-subst-lem-v u) 〉
      app (subst-v (subst-rename f s) t) (subst-v (subst-rename f s) u)
    ∎
  rename-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (or t u) = 
      or (⊢p-rename f (subst-p s t)) (⊢p-rename f (subst-p s u))
    ≅〈 cong2 or (rename-subst-lem-p t) (rename-subst-lem-p u) 〉
      or (subst-p (subst-rename f s) t) (subst-p (subst-rename f s) u)
    ∎
  rename-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (if b then t else u) = 
      if (⊢v-rename f (subst-v s b)) then (⊢p-rename f (subst-p s t)) else (⊢p-rename f (subst-p s u))
    ≅〈 cong2 (λ x y → if (⊢v-rename f (subst-v s b)) then x else y) (rename-subst-lem-p t) (rename-subst-lem-p u) 〉
      if (⊢v-rename f (subst-v s b)) then (subst-p (subst-rename f s) t) else (subst-p (subst-rename f s) u)
    ≅〈 cong (λ x → if x then (subst-p (subst-rename f s) t) else (subst-p (subst-rename f s) u)) (rename-subst-lem-v b) 〉
      if (subst-v (subst-rename f s) b) then (subst-p (subst-rename f s) t) else (subst-p (subst-rename f s) u)
    ∎


  -- Substituting in a renamed term
  subst-rename-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {s : Sub Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → subst-v s (⊢v-rename f t) ≅ subst-v (s · f) t

  subst-rename-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {s : Sub Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → subst-p s (⊢p-rename f t) ≅ subst-p (s · f) t

  subst-rename-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (var x) = 
      f (s x)
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (proj₁ t) = 
      proj₁ (subst-v f (⊢v-rename s t))
    ≅〈 cong proj₁ (subst-rename-lem-v t) 〉
      proj₁ (subst-v (λ {σ'} → f · s) t)
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {f} (proj₂ t) = 
      proj₂ (subst-v f (⊢v-rename s t))
    ≅〈 cong proj₂ (subst-rename-lem-v t) 〉
      proj₂ (subst-v (λ {σ'} → f · s) t)
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {s} {f} (pair t u) = 
      pair (subst-v f (⊢v-rename s t)) (subst-v f (⊢v-rename s u))
    ≅〈 cong2 pair (subst-rename-lem-v t) (subst-rename-lem-v u) 〉
      pair (subst-v (λ {σ} → f · s) t) (subst-v (λ {σ} → f · s) u)
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {One} {s} {f} ⋆ = 
      ⋆
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {f} true = 
      true
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {f} false = 
      false
    ∎
  subst-rename-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {s} {f} (lam t) = 
      lam (subst-p (lift f) (⊢p-rename (wk₂ s) t))
    ≅〈 cong lam (trans (subst-rename-lem-p t) (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ → ext rename-wk₂-lift-lem)))) 〉
      lam (subst-p (lift (λ {σ'} z → f (s z))) t)
    ∎
  subst-rename-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (return t) = 
      return (subst-v f (⊢v-rename s t))
    ≅〈 cong return (subst-rename-lem-v t) 〉
      return (subst-v (λ {σ'} → f · s) t)
    ∎
  subst-rename-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (t to u) = 
      subst-p f (⊢p-rename s t) to subst-p (lift f) (⊢p-rename (wk₂ s) u)
    ≅〈 cong2 _to_ (subst-rename-lem-p t) (trans (subst-rename-lem-p u) (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ σ → ext rename-wk₂-lift-lem)))) 〉
      subst-p (λ {σ'} → f · s) t to subst-p (lift (λ {σ'} z → f (s z))) u
    ∎
  subst-rename-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (app t u) = 
      app (subst-v f (⊢v-rename s t)) (subst-v f (⊢v-rename s u))
    ≅〈 cong2 app (subst-rename-lem-v t) (subst-rename-lem-v u) 〉
      app (subst-v (λ {σ'} → f · s) t) (subst-v (λ {σ'} → f · s) u)
    ∎
  subst-rename-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (or t u) = 
      or (subst-p f (⊢p-rename s t)) (subst-p f (⊢p-rename s u))
    ≅〈 cong2 or (subst-rename-lem-p t) (subst-rename-lem-p u) 〉
      or (subst-p (λ {σ'} → f · s) t) (subst-p (λ {σ'} → f · s) u)
    ∎
  subst-rename-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {f} (if b then t else u) = 
      if (subst-v f (⊢v-rename s b)) then (subst-p f (⊢p-rename s t)) else (subst-p f (⊢p-rename s u))
    ≅〈 cong2 (λ x y → if (subst-v f (⊢v-rename s b)) then x else y) (subst-rename-lem-p t) (subst-rename-lem-p u) 〉
      if (subst-v f (⊢v-rename s b)) then (subst-p (λ {σ'} → f · s) t) else (subst-p (λ {σ'} → f · s) u)
    ≅〈 cong (λ x → if x then (subst-p (λ {σ'} → f · s) t) else (subst-p (λ {σ'} → f · s) u)) (subst-rename-lem-v b) 〉
      if (subst-v (λ {σ'} → f · s) b) then (subst-p (λ {σ'} → f · s) t) else (subst-p (λ {σ'} → f · s) u)
    ∎


  -- Lifting a already lifted term
  subst-lift-lift-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ Γ'} 
    {s' : Sub Γ' Γ''} 
    → (x : σ ∈ (Γ :: τ)) 
    → subst-v (lift s') (lift s x) ≅ lift (comp-subst s' s) x

  subst-lift-lift-lem Hd = 
      var Hd
    ∎
  subst-lift-lift-lem {Γ} {Γ'} {Γ''} {σ} {τ} {f} {g} (Tl x) = 
      subst-v (lift g) (⊢v-rename wk₁ (f x))
    ≅〈 subst-rename-lem-v (f x) 〉
      subst-v (subst-rename wk₁ g) (f x) 
    ≅〈 sym (rename-subst-lem-v (f x)) 〉
      ⊢v-rename wk₁ (subst-v g (f x))
    ∎


  -- Composition lemma for value and producer substitutions
  subst-comp-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {s' : Sub Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → subst-v s' (subst-v s t) ≅ subst-v (comp-subst s' s) t

  subst-comp-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {s' : Sub Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → subst-p s' (subst-p s t) ≅ subst-p (comp-subst s' s) t

  subst-comp-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {s'} (var x) = 
      subst-v s' (s x)
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {s'} (proj₁ t) = 
      proj₁ (subst-v s' (subst-v s t))
    ≅〈 cong proj₁ (subst-comp-lem-v t) 〉
      proj₁ (subst-v (comp-subst s' s) t)
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {σ} {s} {s'} (proj₂ t) = 
      proj₂ (subst-v s' (subst-v s t))
    ≅〈 cong proj₂ (subst-comp-lem-v t) 〉
      proj₂ (subst-v (comp-subst s' s) t)
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {s} {s'} (pair t u) = 
      pair (subst-v s' (subst-v s t)) (subst-v s' (subst-v s u))
    ≅〈 cong2 pair (subst-comp-lem-v t) (subst-comp-lem-v u) 〉
      pair (subst-v (comp-subst s' s) t) (subst-v (comp-subst s' s) u)
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {One} {s} {s'} ⋆ = 
      ⋆
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {s'} true = 
      true
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {Bool} {s} {s'} false = 
      false
    ∎
  subst-comp-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {s} {s'} (lam t) = 
      lam (subst-p (lift s') (subst-p (lift s) t))
    ≅〈 cong lam (trans (subst-comp-lem-p t) (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ → ext subst-lift-lift-lem)))) 〉
      lam (subst-p (lift (comp-subst s' s)) t)
    ∎
  subst-comp-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {s'} (return t) = 
      return (subst-v s' (subst-v s t))
    ≅〈 cong return (subst-comp-lem-v t) 〉
      return (subst-v (comp-subst s' s) t)
    ∎
  subst-comp-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {s'} (t to u) = 
      subst-p s' (subst-p s t) to subst-p (lift s') (subst-p (lift s) u)
    ≅〈 cong2 _to_ (subst-comp-lem-p t) (trans (subst-comp-lem-p u) (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ σ → ext subst-lift-lift-lem)))) 〉
      subst-p (comp-subst s' s) t to subst-p (lift (comp-subst s' s)) u
    ∎
  subst-comp-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {s'} (app t u) = 
      app (subst-v s' (subst-v s t)) (subst-v s' (subst-v s u))
    ≅〈 cong2 app (subst-comp-lem-v t) (subst-comp-lem-v u) 〉
      app (subst-v (comp-subst s' s) t) (subst-v (comp-subst s' s) u)
    ∎
  subst-comp-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {s'} (or t u) = 
      or (subst-p s' (subst-p s t)) (subst-p s' (subst-p s u))
    ≅〈 cong2 or (subst-comp-lem-p t) (subst-comp-lem-p u) 〉
      or (subst-p (comp-subst s' s) t) (subst-p (comp-subst s' s) u)
    ∎
  subst-comp-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {s'} (if b then t else u) = 
      if (subst-v s' (subst-v s b)) then (subst-p s' (subst-p s t)) else (subst-p s' (subst-p s u))
    ≅〈 cong2 (λ x y → if (subst-v s' (subst-v s b)) then x else y) (subst-comp-lem-p t) (subst-comp-lem-p u) 〉
      if (subst-v s' (subst-v s b)) then (subst-p (comp-subst s' s) t) else (subst-p (comp-subst s' s) u)
    ≅〈 cong (λ x → if x then (subst-p (comp-subst s' s) t) else (subst-p (comp-subst s' s) u)) (subst-comp-lem-v b) 〉
      if (subst-v (comp-subst s' s) b) then (subst-p (comp-subst s' s) t) else (subst-p (comp-subst s' s) u)
    ∎


  -- Substituting the last free variable in a lifted term (mostly used to reason about lambda abstractions)
  subst-ext-lift-lem : 
    {Γ Γ' : Ctx} 
    {τ σ : Ty} 
    {s : Sub Γ Γ'} 
    → (u : Γ' ⊢v τ) 
    → (x : σ ∈ (Γ :: τ)) 
    → subst-v (ext-subst id-subst u) (lift s x) ≅ ext-subst s u x

  subst-ext-lift-lem u Hd = 
      u
    ∎
  subst-ext-lift-lem {Γ} {Γ'} {τ} {σ} {s} u (Tl x) = 
      subst-v (ext-subst id-subst u) (⊢v-rename wk₁ (s x))
    ≅〈 subst-rename-lem-v (s x) 〉
      subst-v id-subst (s x)
    ≅〈 id-subst-lem-v (s x) 〉
      s x
    ∎


  -- Substituting the last free variable in an already substituted term
  ext-subst-lem-v : 
    {Γ Γ' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ Γ'} 
    → (t : Γ :: τ ⊢v σ) 
    → (u : Γ' ⊢v τ) 
    → subst-v (ext-subst id-subst u) (subst-v (lift s) t) ≅ subst-v (ext-subst s u) t  

  ext-subst-lem-p : 
    {Γ Γ' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ Γ'} 
    → (t : Γ :: τ ⊢p σ) 
    → (u : Γ' ⊢v τ) 
    → subst-p (ext-subst id-subst u) (subst-p (lift s) t) ≅ subst-p (ext-subst s u) t

  ext-subst-lem-v {Γ} {Γ'} {σ} {τ} {s} t u = 
      subst-v (ext-subst id-subst u) (subst-v (lift s) t)
    ≅〈 subst-comp-lem-v t 〉
      subst-v (comp-subst (ext-subst id-subst u) (lift s)) t 
    ≅〈 cong (λ (x : Sub _ _) → subst-v x t) (iext (λ σ' → ext (subst-ext-lift-lem u))) 〉
      subst-v (ext-subst s u) t
    ∎
  ext-subst-lem-p {Γ} {Γ'} {σ} {τ} {s} t u = 
      subst-p (ext-subst id-subst u) (subst-p (lift s) t)
    ≅〈 subst-comp-lem-p t 〉 
      subst-p (comp-subst (ext-subst id-subst u) (lift s)) t
    ≅〈 cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ → ext (subst-ext-lift-lem u))) 〉
      subst-p (ext-subst s u) t
    ∎


  -- Lifting substitution renamings
  lift-exchange-rename-lem : 
    {Γ Γ' : Ctx} 
    {σ' τ τ' : Ty} 
    {s : Sub Γ Γ'} 
    → (x : τ' ∈ (Γ :: τ)) 
    → (lift (subst-rename (wk₁ {Γ'} {σ'}) s) x) ≅ (⊢v-rename {τ'} (λ x → exchange {Γ'} {σ'} {τ} (Tl x)) (lift s x))

  lift-exchange-rename-lem Hd = 
      var Hd
    ∎
  lift-exchange-rename-lem {Γ} {Γ'} {σ'} {τ} {τ'} {f} (Tl x) = 
      ⊢v-rename wk₁ (⊢v-rename wk₁ (f x))
    ≅〈 ⊢v-rename-comp-lem (f x) 〉 
      ⊢v-rename (comp-ren wk₁ wk₁) (f x)
    ≅〈 sym (⊢v-rename-comp-lem (f x)) 〉
      ⊢v-rename (λ {σ} z → exchange (Tl z)) (⊢v-rename wk₁ (f x))
    ∎


  -- Substituting and extending lemma
  subst-ext-subst-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' : Ty} 
    {s : Sub Γ Γ'} 
    → (u : Γ ⊢v σ) 
    → (x : σ' ∈ (Γ :: σ)) 
    → subst-v s (ext-subst id-subst u x) ≅ subst-v (ext-subst id-subst (subst-v s u)) (lift s x)

  subst-ext-subst-lem {Γ} {Γ'} {σ} {.σ} {s} u Hd = 
      subst-v s u
    ∎
  subst-ext-subst-lem {Γ} {Γ'} {σ} {σ'} {s} u (Tl x) = 
      s x
    ≅〈 sym (id-subst-lem-v (s x)) 〉 
      subst-v (ext-subst id-subst (subst-v s u) · wk₁) (s x)
    ≅〈 sym (subst-rename-lem-v (s x)) 〉
      subst-v (ext-subst id-subst (subst-v s u)) (⊢v-rename wk₁ (s x))
    ∎


  -- Double lifting and exchange
  lift-lift-exchange-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' σ'' : Ty} 
    {s : Sub Γ Γ'} 
    → (x : σ ∈ (Γ :: σ')) 
    → _≅_ {Γ' :: σ'' :: σ' ⊢v σ} (lift (subst-rename wk₁ s) x) {Γ' :: σ'' :: σ' ⊢v σ} (lift (lift s) (exchange (Tl x)))

  lift-lift-exchange-lem Hd = 
      var Hd
    ∎
  lift-lift-exchange-lem {Γ} {Γ'} {σ} {σ'} {σ''} {s} (Tl x) = 
      ⊢v-rename wk₁ (⊢v-rename wk₁ (s x))
    ∎


  -- Congruence of the action of substitution
  ≡-substcong-v : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {t t' : Γ ⊢v σ} 
    → Γ ⊢v t ≡ t' 
    → Γ' ⊢v subst-v s t ≡ subst-v s t'

  ≡-substcong-p : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {t t' : Γ ⊢p σ} 
    → Γ ⊢p t ≡ t' 
    → Γ' ⊢p subst-p s t ≡ subst-p s t'

  ≡-substcong-v {Γ} {Γ'} {σ} {s} {t} {.t} ≡-refl = 
      subst-v s t
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {t} {u} (≡-sym p) = 
      subst-v s t
    ≡v〈 ≡-sym (≡-substcong-v p) 〉
      subst-v s u
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      subst-v s t
    ≡v〈 ≡-substcong-v p 〉
      subst-v s u
    ≡v〈 ≡-substcong-v q 〉
      subst-v s v
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ₁ ∧ σ₂} {s} {pair t u} {pair t' u'} (congpair p q) = 
      pair (subst-v s t) (subst-v s u)
    ≡v〈 congpair (≡-substcong-v p) (≡-substcong-v q) 〉
      pair (subst-v s t') (subst-v s u')
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {proj₁ t} {proj₁ u} (congproj₁ p) = 
      proj₁ (subst-v s t)
    ≡v〈 congproj₁ (≡-substcong-v p) 〉
      proj₁ (subst-v s u)
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {proj₂ t} {proj₂ u} (congproj₂ p) = 
      proj₂ (subst-v s t)
    ≡v〈 congproj₂ (≡-substcong-v p) 〉
      proj₂ (subst-v s u)
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ ⇀ τ} {s} {lam t} {lam u} (conglam p) = 
      lam (subst-p (lift s) t)
    ≡v〈 conglam (≡-substcong-p p) 〉
      lam (subst-p (lift s) u)
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {proj₁ (pair t u)} {.t} β×₁ = 
      proj₁ (pair (subst-v s t) (subst-v s u))
    ≡v〈 β×₁ 〉
      subst-v s t
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ} {s} {proj₂ (pair t u)} {.u} β×₂ = 
      proj₂ (pair (subst-v s t) (subst-v s u))
    ≡v〈 β×₂ 〉
      subst-v s u
    v∎
  ≡-substcong-v {Γ} {Γ'} {One} {s} {t} {⋆} η⋆ = 
      subst-v s t
    ≡v〈 η⋆ 〉
      ⋆
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ₁ ∧ σ₂} {s} {t} {pair .(proj₁ t) .(proj₂ t)} η× = 
      subst-v s t
    ≡v〈 η× 〉
      pair (proj₁ (subst-v s t)) (proj₂ (subst-v s t))
    v∎
  ≡-substcong-v {Γ} {Γ'} {σ ⇀ τ} {s} (η⇀ {.Γ} {.σ} {.τ} {t}) = 
      lam (app (subst-v (lift s) (⊢v-rename (λ {σ'} → Tl) t)) (var Hd))
    ≡v〈 (conglam (congapp (≅2≡-v (trans (subst-rename-lem-v t) (sym (rename-subst-lem-v t)))) ≡-refl)) 〉
      lam (app (⊢v-rename wk₁ (subst-v s t)) (var Hd))
    ≡v〈 η⇀ 〉
      subst-v s t
    v∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {t} {.t} ≡-refl = 
      subst-p s t
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {t} {u} (≡-sym p) = 
      subst-p s t
    ≡p〈 ≡-sym (≡-substcong-p p) 〉
      subst-p s u
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      subst-p s t
    ≡p〈 ≡-substcong-p p 〉
      subst-p s u
    ≡p〈 ≡-substcong-p q 〉
      subst-p s v
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {app t u} {app t' u'} (congapp p q) = 
      app (subst-v s t) (subst-v s u)
    ≡p〈 congapp (≡-substcong-v p) (≡-substcong-v q) 〉
      app (subst-v s t') (subst-v s u')
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {t to u} {t' to u'} (congto p q) = 
      subst-p s t to subst-p (lift s) u
    ≡p〈 congto (≡-substcong-p p) (≡-substcong-p q) 〉
      subst-p s t' to subst-p (lift s) u'
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {return t} {return u} (congreturn p) = 
      return (subst-v s t)
    ≡p〈 congreturn (≡-substcong-v p) 〉
      return (subst-v s u)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {or t u} {or t' u'} (congor p q) = 
      or (subst-p s t) (subst-p s u)
    ≡p〈 congor (≡-substcong-p p) (≡-substcong-p q) 〉
      or (subst-p s t') (subst-p s u')
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} {if b then t else u} {if b' then t' else u'} (congif p q r) = 
      if (subst-v s b) then (subst-p s t) else (subst-p s u)
    ≡p〈 congif (≡-substcong-v p) (≡-substcong-p q) (≡-substcong-p r) 〉
      if (subst-v s b') then (subst-p s t') else (subst-p s u')
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (β⇀ {.Γ} {σ'} {.σ} {t} {u}) = 
      subst-p s (subst-p (ext-subst var u) t) 
    ≡p〈 ≅2≡-p (trans (subst-comp-lem-p t) (trans (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ' → ext (subst-ext-subst-lem u)))) (sym (subst-comp-lem-p t)))) 〉
      subst-p (ext-subst id-subst (subst-v s u)) (subst-p (lift s) t) 
    ≡p〈 β⇀ 〉
      app (lam (subst-p (lift s) t)) (subst-v s u)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (βto {.Γ} {σ'} {.σ} {t} {u}) = 
      return (subst-v s u) to subst-p (lift s) t
    ≡p〈 βto 〉 
      subst-p (ext-subst id-subst (subst-v s u)) (subst-p (lift s) t)
    ≡p〈 ≅2≡-p (trans (subst-comp-lem-p t) (trans (cong (λ (x : Sub _ _) → subst-p x t) (sym (iext (λ σ → ext (subst-ext-subst-lem u))))) (sym (subst-comp-lem-p t)))) 〉
      subst-p s (subst-p (ext-subst var u) t)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (ηto {.Γ} {.σ} {t}) = 
      subst-p s t
    ≡p〈 ηto 〉
      subst-p s t to return (var Hd)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {f} {(t to u) to v} (assocto) = 
      (subst-p f t to subst-p (lift f) u) to subst-p (lift f) v
    ≡p〈 assocto 〉
      subst-p f t to (subst-p (lift f) u to ⊢p-rename exchange (⊢p-rename wk₁ (subst-p (lift f) v)))
    ≡p〈 congto ≡-refl (congto ≡-refl (≅2≡-p (trans (⊢p-rename-comp-lem (subst-p (lift f) v)) (trans (rename-subst-lem-p v) (trans (trans (cong (λ (x : Sub _ _) → subst-p x v) (iext (λ σ → ext (λ x → trans (sym (lift-exchange-rename-lem x)) (lift-lift-exchange-lem x))))) (sym (subst-rename-lem-p v))) (sym (cong (subst-p (lift (lift f))) (⊢p-rename-comp-lem v)))))))) 〉
      subst-p f t to (subst-p (lift f) u to subst-p (lift (lift f)) (⊢p-rename exchange (⊢p-rename wk₁ v)))
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (orto {.Γ} {σ'} {.σ} {t} {u} {v}) = 
      or (subst-p s t) (subst-p s u) to subst-p (lift s) v
    ≡p〈 orto 〉
      or (subst-p s t to subst-p (lift s) v) (subst-p s u to subst-p (lift s) v)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (ifto {.Γ} {σ'} {.σ} {b} {t} {u} {v}) = 
      if (subst-v s b) then (subst-p s t) else (subst-p s u) to (subst-p (lift s) v)
    ≡p〈 ifto 〉
      if (subst-v s b) then ((subst-p s t) to (subst-p (lift s) v)) else ((subst-p s u) to (subst-p (lift s) v))
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (or-idempotency {.Γ} {.σ} {t}) = 
      or (subst-p s t) (subst-p s t)
    ≡p〈 or-idempotency 〉
      subst-p s t
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (or-commutativity {.Γ} {.σ} {t} {u}) = 
      or (subst-p s t) (subst-p s u)
    ≡p〈 or-commutativity 〉
      or (subst-p s u) (subst-p s t)
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (or-associativity {.Γ} {.σ} {t} {u} {v}) = 
      or (or (subst-p s t) (subst-p s u)) (subst-p s v)
    ≡p〈 or-associativity 〉
      or (subst-p s t) (or (subst-p s u) (subst-p s v))
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (if-true {.Γ} {.σ} {t} {u}) = 
      if true then (subst-p s t) else (subst-p s u)
    ≡p〈 if-true 〉
      subst-p s t
    p∎
  ≡-substcong-p {Γ} {Γ'} {σ} {s} (if-false {.Γ} {.σ} {t} {u}) = 
      if false then (subst-p s t) else (subst-p s u)
    ≡p〈 if-false 〉
      subst-p s u
    p∎


  -- Renaming extended idendity substitution
  rename-ext-idsubst-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    → (u : Γ ⊢v σ) 
    → (x : σ' ∈ (Γ :: σ)) 
    → ⊢v-rename f (ext-subst id-subst u x) ≅ ext-subst id-subst (⊢v-rename f u) (wk₂ f x)

  rename-ext-idsubst-lem {Γ} {Γ'} {σ} {.σ} {f} u Hd = 
      ⊢v-rename f u
    ∎
  rename-ext-idsubst-lem {Γ} {Γ'} {σ} {σ'} {f} u (Tl x) = 
      var (f x)
    ∎


  -- Double weakening and exchanging
  wk₂-wk₂-exchange-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' σ'' : Ty} 
    {f : Ren Γ Γ'} 
    → (x : σ ∈ (Γ :: σ')) 
    → _≅_ {σ ∈ (Γ' :: σ'' :: σ')} (exchange (Tl (wk₂ f x))) {σ ∈ (Γ' :: σ'' :: σ')} (wk₂ (wk₂ f) (exchange (Tl x)))

  wk₂-wk₂-exchange-lem Hd = 
      Hd
    ∎
  wk₂-wk₂-exchange-lem {Γ} {Γ'} {σ} {σ'} {σ''} {f} (Tl x) = 
      Tl (Tl (f x))
    ∎


  -- Congruence of the action of renaming on value and producer terms
  ≡-renamecong-v : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t u : Γ ⊢v σ} 
    → Γ ⊢v t ≡ u
    → Γ' ⊢v ⊢v-rename f t ≡ ⊢v-rename f u

  ≡-renamecong-p : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t u : Γ ⊢p σ} 
    → Γ ⊢p t ≡ u
    → Γ' ⊢p ⊢p-rename f t ≡ ⊢p-rename f u

  ≡-renamecong-v {Γ} {Γ'} {σ} {f} {t} {.t} ≡-refl = 
      ⊢v-rename f t
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} {t} {u} (≡-sym p) = 
      ⊢v-rename f t
    ≡v〈 ≡-sym (≡-renamecong-v p) 〉
      ⊢v-rename f u
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢v-rename f t
    ≡v〈 ≡-renamecong-v p 〉 
      ⊢v-rename f u
    ≡v〈 ≡-renamecong-v q 〉
      ⊢v-rename f v
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ₁ ∧ σ₂} {f} {pair t u} {pair t' u'} (congpair p q) = 
      pair (⊢v-rename f t) (⊢v-rename f u)
    ≡v〈 congpair (≡-renamecong-v p) (≡-renamecong-v q) 〉
      pair (⊢v-rename f t') (⊢v-rename f u')
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} {proj₁ t} {proj₁ u} (congproj₁ p) = 
      proj₁ (⊢v-rename f t)
    ≡v〈 congproj₁ (≡-renamecong-v p) 〉
      proj₁ (⊢v-rename f u)
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} {proj₂ t} {proj₂ u} (congproj₂ p) = 
      proj₂ (⊢v-rename f t)
    ≡v〈 congproj₂ (≡-renamecong-v p) 〉
      proj₂ (⊢v-rename f u)
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ ⇀ τ} {f} {lam t} {lam u} (conglam p) = 
      lam (⊢p-rename (wk₂ f) t)
    ≡v〈 conglam (≡-renamecong-p p) 〉
      lam (⊢p-rename (wk₂ f) u)
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} (β×₁ {.Γ} {.σ} {σ'} {t} {u}) = 
      proj₁ (pair (⊢v-rename f t) (⊢v-rename f u))
    ≡v〈 β×₁ 〉
      ⊢v-rename f t
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ} {f} (β×₂ {.Γ} {σ'} {.σ} {t} {u}) = 
      proj₂ (pair (⊢v-rename f t) (⊢v-rename f u))
    ≡v〈 β×₂ 〉
      ⊢v-rename f u
    v∎
  ≡-renamecong-v {Γ} {Γ'} {One} {f} (η⋆ {.Γ} {t}) = 
      ⊢v-rename f t
    ≡v〈 η⋆ 〉
      ⋆
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ₁ ∧ σ₂} {f} (η× {.Γ} {.σ₁} {.σ₂} {t}) = 
      ⊢v-rename f t
    ≡v〈 η× 〉
      pair (proj₁ (⊢v-rename f t)) (proj₂ (⊢v-rename f t))
    v∎
  ≡-renamecong-v {Γ} {Γ'} {σ ⇀ τ} {f} (η⇀ {.Γ} {.σ} {.τ} {t}) = 
      lam (app (⊢v-rename (wk₂ f) (⊢v-rename wk₁ t)) (var Hd))
    ≡v〈 conglam (congapp (≅2≡-v (trans (⊢v-rename-comp-lem t) (sym (⊢v-rename-comp-lem t)))) ≡-refl) 〉 
      lam (app (⊢v-rename wk₁ (⊢v-rename f t)) (var Hd))
    ≡v〈 η⇀ 〉
      ⊢v-rename f t
    v∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {t} {.t} ≡-refl =
      ⊢p-rename f t
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {t} {u} (≡-sym p) = 
      ⊢p-rename f t
    ≡p〈 ≡-sym (≡-renamecong-p p) 〉
      ⊢p-rename f u
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢p-rename f t
    ≡p〈 ≡-renamecong-p p 〉
      ⊢p-rename f u
    ≡p〈 ≡-renamecong-p q 〉
      ⊢p-rename f v
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {app t u} {app t' u'} (congapp p q) = 
      app (⊢v-rename f t) (⊢v-rename f u)
    ≡p〈 congapp (≡-renamecong-v p) (≡-renamecong-v q) 〉
      app (⊢v-rename f t') (⊢v-rename f u')
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {t to u} {t' to u'} (congto p q) = 
      ⊢p-rename f t to ⊢p-rename (wk₂ f) u
    ≡p〈 congto (≡-renamecong-p p) (≡-renamecong-p q) 〉
      ⊢p-rename f t' to ⊢p-rename (wk₂ f) u'
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {return t} {return u} (congreturn p) = 
      return (⊢v-rename f t)
    ≡p〈 congreturn (≡-renamecong-v p) 〉
      return (⊢v-rename f u)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {or t u} {or t' u'} (congor p q) = 
      or (⊢p-rename f t) (⊢p-rename f u)
    ≡p〈 congor (≡-renamecong-p p) (≡-renamecong-p q) 〉
      or (⊢p-rename f t') (⊢p-rename f u')
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {if b then t else u} {if b' then t' else u'} (congif p q r) = 
      if (⊢v-rename f b) then (⊢p-rename f t) else (⊢p-rename f u)
    ≡p〈 congif (≡-renamecong-v p) (≡-renamecong-p q) (≡-renamecong-p r) 〉
      if (⊢v-rename f b') then (⊢p-rename f t') else (⊢p-rename f u')
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (β⇀ {.Γ} {σ'} {.σ} {t} {u}) = 
      ⊢p-rename f (subst-p (ext-subst id-subst u) t)
    ≡p〈 ≅2≡-p (trans (rename-subst-lem-p t) (trans (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ' → ext (rename-ext-idsubst-lem u)))) (sym (subst-rename-lem-p t)))) 〉
      subst-p (ext-subst id-subst (⊢v-rename f u)) (⊢p-rename (wk₂ f) t)
    ≡p〈 β⇀ 〉
      app (lam (⊢p-rename (wk₂ f) t)) (⊢v-rename f u)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (βto {.Γ} {σ'} {.σ} {t} {u}) = 
      return (⊢v-rename f u) to ⊢p-rename (wk₂ f) t
    ≡p〈 βto 〉 
      subst-p (ext-subst id-subst (⊢v-rename f u)) (⊢p-rename (wk₂ f) t)
    ≡p〈 ≅2≡-p (trans (subst-rename-lem-p t) (trans (cong (λ (x : Sub _ _) → subst-p x t) (sym (iext (λ σ → ext (rename-ext-idsubst-lem u))))) (sym (rename-subst-lem-p t)))) 〉
      ⊢p-rename f (subst-p (ext-subst id-subst u) t)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (ηto {.Γ} {.σ} {t}) = 
      ⊢p-rename f t
    ≡p〈 ηto 〉
      ⊢p-rename f t to return (var Hd)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} {(t to u) to v} assocto = 
      (⊢p-rename f t to ⊢p-rename (wk₂ f) u) to ⊢p-rename (wk₂ f) v
    ≡p〈 assocto 〉
      ⊢p-rename f t to (⊢p-rename (wk₂ f) u to ⊢p-rename exchange (⊢p-rename wk₁ (⊢p-rename (wk₂ f) v)))
    ≡p〈 congto ≡-refl (congto ≡-refl (≅2≡-p (trans (⊢p-rename-comp-lem (⊢p-rename (wk₂ f) v)) (trans (⊢p-rename-comp-lem v) (trans (cong (λ (x : Ren _ _) → ⊢p-rename x v) (iext (λ σ → ext wk₂-wk₂-exchange-lem))) (sym (trans (⊢p-rename-comp-lem (⊢p-rename wk₁ v)) (⊢p-rename-comp-lem v)))))))) 〉
      ⊢p-rename f t to (⊢p-rename (wk₂ f) u to ⊢p-rename (wk₂ (wk₂ f)) (⊢p-rename exchange (⊢p-rename wk₁ v)))
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (orto {.Γ} {τ} {.σ} {t} {u} {v}) = 
      or (⊢p-rename f t) (⊢p-rename f u) to ⊢p-rename (wk₂ f) v
    ≡p〈 orto 〉
      or (⊢p-rename f t to ⊢p-rename (wk₂ f) v) (⊢p-rename f u to ⊢p-rename (wk₂ f) v)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (ifto {.Γ} {τ} {.σ} {b} {t} {u} {v}) = 
      if (⊢v-rename f b) then (⊢p-rename f t) else (⊢p-rename f u) to (⊢p-rename (wk₂ f) v)
    ≡p〈 ifto 〉
      if (⊢v-rename f b) then ((⊢p-rename f t) to (⊢p-rename (wk₂ f) v)) else ((⊢p-rename f u) to (⊢p-rename (wk₂ f) v))
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (or-idempotency {.Γ} {.σ} {t}) = 
      or (⊢p-rename f t) (⊢p-rename f t)
    ≡p〈 or-idempotency 〉
      ⊢p-rename f t
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (or-commutativity {.Γ} {.σ} {t} {u}) = 
      or (⊢p-rename f t) (⊢p-rename f u)
    ≡p〈 or-commutativity 〉
      or (⊢p-rename f u) (⊢p-rename f t)
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (or-associativity {.Γ} {.σ} {t} {u} {v}) = 
      or (or (⊢p-rename f t) (⊢p-rename f u)) (⊢p-rename f v)
    ≡p〈 or-associativity 〉
      or (⊢p-rename f t) (or (⊢p-rename f u) (⊢p-rename f v))
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (if-true {.Γ} {.σ} {t} {u}) = 
      if true then (⊢p-rename f t) else (⊢p-rename f u)
    ≡p〈 if-true 〉
      ⊢p-rename f t
    p∎
  ≡-renamecong-p {Γ} {Γ'} {σ} {f} (if-false {.Γ} {.σ} {t} {u}) = 
      if false then (⊢p-rename f t) else (⊢p-rename f u)
    ≡p〈 if-false 〉
      ⊢p-rename f u
    p∎


  -- Congruence of the action of renaming on normal and atomic value and producer terms
  ≡-renamecong-nv : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t u : Γ ⊢nv σ} 
    → Γ ⊢nv t ≡ u 
    → Γ' ⊢nv (⊢nv-rename f t) ≡ (⊢nv-rename f u)

  ≡-renamecong-np : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t u : Γ ⊢np σ} 
    → Γ ⊢np t ≡ u 
    → Γ' ⊢np (⊢np-rename f t) ≡ (⊢np-rename f u)

  ≡-renamecong-ap : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t u : Γ ⊢ap σ} 
    → Γ ⊢ap t ≡ u 
    → Γ' ⊢ap (⊢ap-rename f t) ≡ (⊢ap-rename f u)

  ≡-renamecong-nv {Γ} {Γ'} {σ} {f} {t} {.t} ≡-refl = 
      ⊢nv-rename f t
    nv∎
  ≡-renamecong-nv {Γ} {Γ'} {σ} {f} {t} {u} (≡-sym p) = 
      ⊢nv-rename f t
    ≡nv〈 ≡-sym (≡-renamecong-nv p) 〉
      ⊢nv-rename f u
    nv∎
  ≡-renamecong-nv {Γ} {Γ'} {σ} {f} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢nv-rename f t
    ≡nv〈 ≡-renamecong-nv p 〉
      ⊢nv-rename f u 
    ≡nv〈 ≡-renamecong-nv q 〉
      ⊢nv-rename f v
    nv∎
  ≡-renamecong-nv {Γ} {Γ'} {α} {f} {av2NV t} {av2NV u} (congav p) = 
      av2NV (⊢av-rename f t)
    ≡nv〈 congav (cong (⊢av-rename f) p) 〉
      av2NV (⊢av-rename f u)
    nv∎
  ≡-renamecong-nv {Γ} {Γ'} {σ₁ ∧ σ₂} {f} {pairNV t u} {pairNV t' u'} (congpair p q) = 
      pairNV (⊢nv-rename f t) (⊢nv-rename f u)
    ≡nv〈 congpair (≡-renamecong-nv p) (≡-renamecong-nv q) 〉
      pairNV (⊢nv-rename f t') (⊢nv-rename f u')
    nv∎
  ≡-renamecong-nv {Γ} {Γ'} {σ ⇀ τ} {f} {lamNV t} {lamNV u} (conglam p) = 
      lamNV (⊢np-rename (wk₂ f) t)
    ≡nv〈 conglam (≡-renamecong-np p) 〉
      lamNV (⊢np-rename (wk₂ f) u)
    nv∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {t} {.t} ≡-refl = 
      ⊢np-rename f t
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {t} {u} (≡-sym p) = 
      ⊢np-rename f t
    ≡np〈 ≡-sym (≡-renamecong-np p) 〉
      ⊢np-rename f u
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢np-rename f t
    ≡np〈 ≡-renamecong-np p 〉
      ⊢np-rename f u
    ≡np〈 ≡-renamecong-np q 〉
      ⊢np-rename f v
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {toNP t u} {toNP t' u'} (congto p q) = 
      toNP (⊢ap-rename f t) (⊢np-rename (wk₂ f) u)
    ≡np〈 congto (≡-renamecong-ap p) (≡-renamecong-np q) 〉
      toNP (⊢ap-rename f t') (⊢np-rename (wk₂ f) u')
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {returnNP t} {returnNP u} (congreturn p) = 
      returnNP (⊢nv-rename f t)
    ≡np〈 congreturn (≡-renamecong-nv p) 〉
      returnNP (⊢nv-rename f u)
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {orNP t u} {orNP t' u'} (congor p q) = 
      orNP (⊢np-rename f t) (⊢np-rename f u)
    ≡np〈 congor (≡-renamecong-np p) (≡-renamecong-np q) 〉
      orNP (⊢np-rename f t') (⊢np-rename f u')
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} {ifNP b then t else u} {ifNP b' then t' else u'} (congif p q r) = 
      ifNP (⊢nv-rename f b) then (⊢np-rename f t) else (⊢np-rename f u)
    ≡np〈 congif (≡-renamecong-nv p) (≡-renamecong-np q) (≡-renamecong-np r) 〉
      ifNP (⊢nv-rename f b') then (⊢np-rename f t') else (⊢np-rename f u')
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} (or-idempotency {.Γ} {.σ} {t}) = 
      orNP (⊢np-rename f t) (⊢np-rename f t)
    ≡np〈 or-idempotency 〉
      ⊢np-rename f t
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} (or-commutativity {.Γ} {.σ} {t} {u}) = 
      orNP (⊢np-rename f t) (⊢np-rename f u)
    ≡np〈 or-commutativity 〉
      orNP (⊢np-rename f u) (⊢np-rename f t)
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} (or-associativity {.Γ} {.σ} {t} {u} {v}) = 
      orNP (orNP (⊢np-rename f t) (⊢np-rename f u)) (⊢np-rename f v)
    ≡np〈 or-associativity 〉
      orNP (⊢np-rename f t) (orNP (⊢np-rename f u) (⊢np-rename f v))
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} (if-true {.Γ} {.σ} {t} {u}) = 
      ifNP trueNV then ⊢np-rename f t else (⊢np-rename f u)
    ≡np〈 if-true 〉
      ⊢np-rename f t
    np∎
  ≡-renamecong-np {Γ} {Γ'} {σ} {f} (if-false {.Γ} {.σ} {t} {u}) = 
      ifNP falseNV then ⊢np-rename f t else (⊢np-rename f u)
    ≡np〈 if-false 〉
      ⊢np-rename f u
    np∎
  ≡-renamecong-ap {Γ} {Γ'} {σ} {f} {t} {.t} ≡-refl = 
      ⊢ap-rename f t
    ap∎
  ≡-renamecong-ap {Γ} {Γ'} {σ} {f} {t} {u} (≡-sym p) = 
      ⊢ap-rename f t
    ≡ap〈 ≡-sym (≡-renamecong-ap p) 〉
      ⊢ap-rename f u
    ap∎
  ≡-renamecong-ap {Γ} {Γ'} {σ} {f} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢ap-rename f t
    ≡ap〈 ≡-renamecong-ap p 〉
      ⊢ap-rename f u 
    ≡ap〈 ≡-renamecong-ap q 〉
      ⊢ap-rename f v
    ap∎
  ≡-renamecong-ap {Γ} {Γ'} {σ} {f} {appAP t u} {appAP t' u'} (congapp p q) = 
      appAP (⊢av-rename f t) (⊢nv-rename f u)
    ≡ap〈 congapp (cong (⊢av-rename f) p) (≡-renamecong-nv q) 〉
      appAP (⊢av-rename f t') (⊢nv-rename f u')
    ap∎


  -- Naturality of reflection
  reflect-naturality-v : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢av σ) 
    → ⟦⟧-rename {σ} f (reflect-v t) ≅ reflect-v (⊢av-rename f t)

  reflect-naturality-p : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    → (t : Γ ⊢ap σ) 
    → T-rename {Denot σ} f (reflect-p t) ≅ reflect-p (⊢ap-rename f t)

  reflect-naturality-v {Γ} {Γ'} {α} {f} (varAV x) = 
      av2NV (varAV (f x))
    ∎
  reflect-naturality-v {Γ} {Γ'} {Bool} {f} (varAV x) = 
      bav2NV (varAV (f x))
    ∎
  reflect-naturality-v {Γ} {Γ'} {One} {f} (varAV x) = 
      ⋆
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ₁ ∧ σ₂} {f} (varAV x) = 
      ⟦⟧-rename {σ₁} f (reflect-v (proj₁AV (varAV x))) , ⟦⟧-rename {σ₂} f (reflect-v (proj₂AV (varAV x)))
    ≅〈 cong2 _,_ (reflect-naturality-v (proj₁AV (varAV x))) ((reflect-naturality-v (proj₂AV (varAV x)))) 〉
      reflect-v (proj₁AV (varAV (f x))) , reflect-v (proj₂AV (varAV (f x)))
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ ⇀ τ} {f} (varAV x) = 
      (λ {Γ''} g y → T-to (appAP (varAV (g (f x))) (reify-v y)) (T-return (reflect-v {τ} (varAV Hd))))
    ∎
  reflect-naturality-v {Γ} {Γ'} {α} {f} (proj₁AV t) = 
      av2NV (proj₁AV (⊢av-rename f t))
    ∎
  reflect-naturality-v {Γ} {Γ'} {Bool} {f} (proj₁AV t) = 
      bav2NV (proj₁AV (⊢av-rename f t))
    ∎
  reflect-naturality-v {Γ} {Γ'} {One} {f} (proj₁AV t) = 
      ⋆
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ₁ ∧ σ₂} {f} (proj₁AV t) = 
      ⟦⟧-rename {σ₁} f (reflect-v (proj₁AV (proj₁AV t))) , ⟦⟧-rename {σ₂} f (reflect-v (proj₂AV (proj₁AV t)))
    ≅〈 cong2 _,_ (reflect-naturality-v (proj₁AV (proj₁AV t))) (reflect-naturality-v (proj₂AV (proj₁AV t))) 〉
      reflect-v (proj₁AV (proj₁AV (⊢av-rename f t))) , reflect-v (proj₂AV (proj₁AV (⊢av-rename f t)))
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ ⇀ τ} {f} (proj₁AV t) = 
      (λ {Γ''} g y → T-to (appAP (proj₁AV (⊢av-rename (comp-ren (λ {σ} → g {σ}) f) t)) (reify-v y)) (T-return (reflect-v {τ} (varAV Hd))))
    ≅〈 iext (λ Γ'' → ext (λ g → ext (λ d → cong (λ x → T-to x (T-return (reflect-v {τ} (varAV Hd)))) (cong (λ x → appAP x (reify-v d)) (cong proj₁AV (sym (⊢av-rename-comp-lem t))))))) 〉
      (λ {Γ''} g y → T-to (appAP (proj₁AV (⊢av-rename (λ {σ} → g {σ}) (⊢av-rename f t))) (reify-v y)) (T-return (reflect-v {τ} (varAV Hd))))
    ∎
  reflect-naturality-v {Γ} {Γ'} {α} {f} (proj₂AV t) = 
      av2NV (proj₂AV (⊢av-rename f t))
    ∎
  reflect-naturality-v {Γ} {Γ'} {Bool} {f} (proj₂AV t) = 
      bav2NV (proj₂AV (⊢av-rename f t))
    ∎
  reflect-naturality-v {Γ} {Γ'} {One} {f} (proj₂AV t) = 
      ⋆
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ₁ ∧ σ₂} {f} (proj₂AV t) = 
      ⟦⟧-rename {σ₁} f (reflect-v (proj₁AV (proj₂AV t))) , ⟦⟧-rename {σ₂} f (reflect-v (proj₂AV (proj₂AV t)))
    ≅〈 cong2 _,_ (reflect-naturality-v (proj₁AV (proj₂AV t))) (reflect-naturality-v (proj₂AV (proj₂AV t))) 〉
      reflect-v (proj₁AV (proj₂AV (⊢av-rename f t))) , reflect-v (proj₂AV (proj₂AV (⊢av-rename f t)))
    ∎
  reflect-naturality-v {Γ} {Γ'} {σ ⇀ τ} {f} (proj₂AV t) = 
      (λ {Γ''} g y → T-to (appAP (proj₂AV (⊢av-rename (comp-ren (λ {σ} → g {σ}) f) t)) (reify-v y)) (T-return (reflect-v {τ} (varAV Hd))))
    ≅〈 iext (λ Γ'' → ext (λ f → ext (λ d → cong (λ x → T-to x (T-return (reflect-v {τ} (varAV Hd)))) (cong (λ x → appAP x (reify-v d)) (cong proj₂AV (sym (⊢av-rename-comp-lem t))))))) 〉
      (λ {Γ''} g y → T-to (appAP (proj₂AV (⊢av-rename (λ {σ} → g {σ}) (⊢av-rename f t))) (reify-v y)) (T-return (reflect-v {τ} (varAV Hd))))
    ∎
  reflect-naturality-p {Γ} {Γ'} {σ} {f} t = 
      T-to (⊢ap-rename f t) (T-return (⟦⟧-rename {σ} (wk₂ f) (reflect-v {σ} (varAV Hd))))
    ≅〈 cong (λ x → T-to (⊢ap-rename f t) (T-return x)) (reflect-naturality-v {Γ :: σ} {Γ' :: σ} {σ} {wk₂ f} (varAV Hd)) 〉
      T-to (⊢ap-rename f t) (T-return (reflect-v {σ} (varAV Hd)))
    ∎


  -- Naturality of interpretation of value terms
  ⟦⟧v-naturality : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {e : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⟦⟧-rename {σ} f (⟦ t ⟧v e) ≅ ⟦ t ⟧v (env-rename f e)

  ⟦⟧v-naturality (var t) = refl
  ⟦⟧v-naturality (proj₁ t) = cong fst (⟦⟧v-naturality t)
  ⟦⟧v-naturality (proj₂ t) = cong snd (⟦⟧v-naturality t)
  ⟦⟧v-naturality true = refl
  ⟦⟧v-naturality false = refl
  ⟦⟧v-naturality (pair t u) = cong2 _,_ (⟦⟧v-naturality t) (⟦⟧v-naturality u)
  ⟦⟧v-naturality ⋆ = refl
  ⟦⟧v-naturality {Γ} {Γ'} {Γ''} {σ ⇀ τ} {e} (lam t) = iext (λ Γ''' → ext (λ f → ext (λ d → cong ⟦ t ⟧p (iext (λ σ' → cong (λ (x : Env _ _) → env-extend x d) (iext (λ σ'' → ext (λ x → sym (⟦⟧-rename-comp-lem {σ = σ''} (e x))))))))))


  -- Lemma about extending the environment and weakening a renaming
  env-extend-rename-wk₂-lem' : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    {d : ⟦ σ ⟧ Γ''} 
    → (x : σ' ∈ (Γ :: σ)) 
    → env-extend (λ x' → (e (f x'))) d x ≅ env-extend e d (wk₂ f x)

  env-extend-rename-wk₂-lem' {Γ} {Γ'} {Γ''} {σ} {.σ} {f} {e} {d} Hd = 
      d
    ∎
  env-extend-rename-wk₂-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} {d} (Tl x) = 
      e (f x)
    ∎


  -- Renaming a term being interpreted is the same as renaming an environment
  rename-env-lem-v' : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⟦ t ⟧v (λ x → ⟦ var (f x) ⟧v e) ≅ ⟦ ⊢v-rename f t ⟧v e

  rename-env-lem-p' : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e : Env Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → ⟦ t ⟧p (λ x → ⟦ var (f x) ⟧v e) ≅ ⟦ ⊢p-rename f t ⟧p e

  *-rename-env-lem' : 
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

  *-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-return d) = 
      ⟦ u ⟧p (env-extend (λ {σ0} z → e (f z)) d)
    ≅〈 cong ⟦ u ⟧p (iext (λ σ' → ext (λ x → env-extend-rename-wk₂-lem' x))) 〉
      ⟦ u ⟧p (λ {σ0} z → env-extend e d (wk₂ f z))
    ≅〈 rename-env-lem-p' u 〉
      ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend e d)
    ∎
  *-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-to d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-to d d')))
    ≅〈 cong (T-to d) (*-rename-env-lem' u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-to d d')))
    ∎
  *-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-or d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-or d d')))
    ≅〈 cong2 T-or (*-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u d) (*-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-or d d')))
    ∎
  *-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (T-if b d d') = 
      * {(Env-Denot Γ) ⊗ (Denot σ')} {Denot σ} (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , (T-if b d d')))
    ≅〈 cong2 (T-if b) (*-rename-env-lem' u d) (*-rename-env-lem' u d') 〉
      * {(Env-Denot Γ') ⊗ (Denot σ')} {Denot σ}  (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , (T-if b d d')))
    ∎

  rename-env-lem-v' {Γ} {Γ'} {Γ''} {σ} {f} {e} (var x) = 
      e (f x)
    ∎
  rename-env-lem-v' {Γ} {Γ'} {Γ''} {σ} {f} {e} (proj₁ t) = 
      ⟦ proj₁ t ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong fst (rename-env-lem-v' t) 〉
      ⟦ ⊢v-rename f (proj₁ t) ⟧v e
    ∎
  rename-env-lem-v' {Γ} {Γ'} {Γ''} {σ} {f} {e} (proj₂ t) = 
      ⟦ proj₂ t ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong snd (rename-env-lem-v' t) 〉
      ⟦ ⊢v-rename f (proj₂ t) ⟧v e
    ∎
  rename-env-lem-v' {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {f} {e} (pair t u) = 
      ⟦ pair t u ⟧v (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 cong2 _,_ (rename-env-lem-v' t) (rename-env-lem-v' u) 〉
      ⟦ ⊢v-rename f (pair t u) ⟧v e
    ∎
  rename-env-lem-v' {Γ} {Γ'} {Γ''} {One} {f} {e} ⋆ = 
      ⋆
    ∎
  rename-env-lem-v' {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {e} (lam t) = 
      (λ {σ'} → ⟦ lam t ⟧v (λ x → ⟦ var (f x) ⟧v e) {σ'})
    ≅〈 iext (λ Γ''' → ext (λ f' → ext (λ d → trans (cong ⟦ t ⟧p (iext (λ σ' → ext (λ x → env-extend-rename-wk₂-lem' x)))) (rename-env-lem-p' t)))) 〉
      (λ {σ'} → ⟦ ⊢v-rename f (lam t) ⟧v e {σ'})
    ∎
  rename-env-lem-v' true = 
      trueNV
    ∎
  rename-env-lem-v' false = 
      falseNV
    ∎
  rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} (return t) = 
      T-return (⟦ t ⟧v (λ {σ'} z → e (f z)))
    ≅〈 cong T-return (rename-env-lem-v' t) 〉
      T-return (⟦ ⊢v-rename f t ⟧v e)
    ∎
  rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} (_to_ {σ'} t u) = 
      ⟦ t to u ⟧p (λ x → ⟦ var (f x) ⟧v e)
    ≅〈 *-rename-env-lem' {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} u (⟦ t ⟧p (λ x → e (f x))) 〉 
      * (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) (t-r (((λ {σ} → e {σ}) , ⟦ t ⟧p (λ x → e (f x)))))
    ≅〈 cong (λ x → * {Env-Denot Γ' ⊗ Denot σ'} {Denot σ} (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v {_}) (snd v))) (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e {σ}) , x))) (rename-env-lem-p' t) 〉
      ⟦ ⊢p-rename f (t to u) ⟧p e
    ∎
  rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} (app t u) = 
      ⟦ t ⟧v (λ {σ'} z → e (f z)) (λ {σ'} → id) (⟦ u ⟧v (λ {σ'} z → e (f z)))
    ≅〈 cong2 (λ x y → x id y) (rename-env-lem-v' t) (rename-env-lem-v' u) 〉
      ⟦ ⊢v-rename f t ⟧v e (λ {σ'} → id) (⟦ ⊢v-rename f u ⟧v e)
    ∎
  rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} (or t u) = 
      T-or (⟦ t ⟧p (λ z → e (f z))) (⟦ u ⟧p (λ z → e (f z)))
    ≅〈 cong2 T-or (rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} t) (rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} u) 〉
      T-or (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ∎
  rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} (if b then t else u) = 
      T-if (⟦ b ⟧v (λ {σ'} z → e (f z))) (⟦ t ⟧p (λ {σ'} z → e (f z))) (⟦ u ⟧p (λ {σ'} z → e (f z)))
    ≅〈 cong2 (T-if (⟦ b ⟧v (λ x → e (f x)))) (rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} t) (rename-env-lem-p' {Γ} {Γ'} {Γ''} {σ} {f} {e} u) 〉 
      T-if (⟦ b ⟧v (λ {σ'} z → e (f z))) (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ≅〈 cong (λ x → T-if x(⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)) (rename-env-lem-v' {Γ} {Γ'} {Γ''} {Bool} {f} {e} b) 〉
      T-if (⟦ ⊢v-rename f b ⟧v e) (⟦ ⊢p-rename f t ⟧p e) (⟦ ⊢p-rename f u ⟧p e)
    ∎
