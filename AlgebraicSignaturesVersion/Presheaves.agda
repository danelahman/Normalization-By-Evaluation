------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
---------------------- Presheaves --------------------
------------------------------------------------------

open import Utils
open import Syntax
open import Renamings


module Presheaves where


  -- Presheaves
  record Set^Ren : Set₁ where
    field set : Ctx → Set 
          act : {Γ Γ' : Ctx} → Ren Γ Γ' → set Γ → set Γ'
  open Set^Ren public


  -- Terminal presheaf
  Set^Ren-Terminal : Set^Ren
  Set^Ren-Terminal = 
    record {
      set = λ _ → Unit; 
      act = λ f _ → ⋆
    }


  -- Product of presheaves
  _⊗_ : (X Y : Set^Ren) → Set^Ren
  _⊗_ X Y =
    record {
      set = λ Γ → (set X Γ) × (set Y Γ);
      act = λ f x → ((act X) f (fst x)) , ((act Y) f (snd x))
    }
  infixl 10 _⊗_


  -- Natural transformations between presheaves            
  Set^Ren-Map : Set^Ren → Set^Ren → Set
  Set^Ren-Map X Y = {Γ : Ctx} → set X Γ → set Y Γ 

  
  -- Composition of natural transformations between presheaves
  _∘_ : {X Y Z : Set^Ren} → Set^Ren-Map Y Z → Set^Ren-Map X Y → Set^Ren-Map X Z
  g ∘ f = g · f


  -- Action of renaming on values and producers
  ⊢v-rename : {σ : Ty} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢v σ → Γ' ⊢v σ
  ⊢p-rename : {σ : Ty} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢p σ → Γ' ⊢p σ
  ⊢v-rename f (var x) = var (f x)
  ⊢v-rename f (proj₁ t) = proj₁ (⊢v-rename f t)
  ⊢v-rename f (proj₂ t) = proj₂ (⊢v-rename f t)
  ⊢v-rename f (pair t u) = pair (⊢v-rename f t) (⊢v-rename f u)
  ⊢v-rename f ⋆ = ⋆
  ⊢v-rename f (fn t) = fn (⊢p-rename (wk₂ f) t)
  ⊢p-rename f (return t) = return (⊢v-rename f t)
  ⊢p-rename f (t to u) = ⊢p-rename f t to ⊢p-rename (wk₂ f) u
  ⊢p-rename f (app t u) = app (⊢v-rename f t) (⊢v-rename f u)
  ⊢p-rename f (input t u) = input (⊢p-rename f t) (⊢p-rename f u)
  ⊢p-rename f (output0 t) = output0 (⊢p-rename f t)
  ⊢p-rename f (output1 t) = output1 (⊢p-rename f t)


  -- Identity renaming lemma for renaming value and producer terms
  ⊢v-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢v σ) 
    → ⊢v-rename id-ren t ≅ t

  ⊢p-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢p σ) 
    → ⊢p-rename id-ren t ≅ t

  ⊢v-rename-id-lem (var x) = 
      var x 
    ∎
  ⊢v-rename-id-lem (proj₁ t) = 
      proj₁ (⊢v-rename id-ren t) 
    ≅〈 cong proj₁ (⊢v-rename-id-lem t) 〉 
      proj₁ t 
    ∎
  ⊢v-rename-id-lem (proj₂ t) = 
      proj₂ (⊢v-rename id-ren t) 
    ≅〈 cong proj₂ (⊢v-rename-id-lem t) 〉 
      proj₂ t 
    ∎
  ⊢v-rename-id-lem (pair t u) = 
      pair (⊢v-rename id-ren t) (⊢v-rename id-ren u) 
    ≅〈 cong2 pair (⊢v-rename-id-lem t) (⊢v-rename-id-lem u) 〉 
      pair t u 
    ∎
  ⊢v-rename-id-lem ⋆ = 
      ⋆ 
    ∎
  ⊢v-rename-id-lem (fn t) = 
      fn (⊢p-rename (wk₂ id-ren) t) 
    ≅〈 cong fn (trans (cong2 ⊢p-rename (iext (λ σ → ext (λ x → wk₂-id-lem x))) refl) (⊢p-rename-id-lem t)) 〉 
      fn t 
    ∎
  ⊢p-rename-id-lem (return t) = 
      return (⊢v-rename id-ren t) 
    ≅〈 cong return (⊢v-rename-id-lem t) 〉 
      return t 
    ∎
  ⊢p-rename-id-lem (t to u) = 
      ⊢p-rename id-ren t to ⊢p-rename (wk₂ id-ren) u 
    ≅〈 cong2 _to_ (⊢p-rename-id-lem t) (trans (cong2 ⊢p-rename (iext (λ σ → ext (λ x → wk₂-id-lem x))) refl) (⊢p-rename-id-lem u)) 〉 
      t to u 
    ∎
  ⊢p-rename-id-lem (app t u) = 
      app (⊢v-rename id-ren t) (⊢v-rename id-ren u) 
    ≅〈 cong2 app (⊢v-rename-id-lem t) (⊢v-rename-id-lem u) 〉 
      app t u 
    ∎
  ⊢p-rename-id-lem (input t u) = 
      input (⊢p-rename id-ren t) (⊢p-rename id-ren u) 
    ≅〈 cong2 input (⊢p-rename-id-lem t) (⊢p-rename-id-lem u) 〉
      input t u 
    ∎
  ⊢p-rename-id-lem (output0 t) = 
      output0 (⊢p-rename id-ren t) 
    ≅〈 cong output0 (⊢p-rename-id-lem t) 〉
      output0 t 
    ∎
  ⊢p-rename-id-lem (output1 t) = 
      output1 (⊢p-rename id-ren t) 
    ≅〈 cong output1 (⊢p-rename-id-lem t) 〉
      output1 t 
    ∎


  -- Weakening of composition of renamings
  rename-wk₂-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ τ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (x : σ ∈ (Γ :: τ)) 
    → wk₂ (comp-ren g f) x ≅ comp-ren (wk₂ g) (wk₂ f) x

  rename-wk₂-comp-lem Hd = 
      Hd
    ∎
  rename-wk₂-comp-lem {_} {_} {_} {_} {_} {f} {g} (Tl x) = 
      Tl (g (f x))
    ∎


  -- Composition lemma for value and producer renamings
  ⊢v-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → ⊢v-rename g (⊢v-rename f t) ≅ ⊢v-rename (comp-ren g f) t

  ⊢p-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → ⊢p-rename g (⊢p-rename f t) ≅ ⊢p-rename (comp-ren g f) t

  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (var x) = 
      var (g (f x))
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (proj₁ t) = 
      proj₁ (⊢v-rename g (⊢v-rename f t))
    ≅〈 cong proj₁ (⊢v-rename-comp-lem t) 〉
      proj₁ (⊢v-rename (comp-ren g f) t)
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (proj₂ t) = 
      proj₂ (⊢v-rename g (⊢v-rename f t))
    ≅〈 cong proj₂ (⊢v-rename-comp-lem t) 〉
      proj₂ (⊢v-rename (comp-ren g f) t)
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {f} {g} (pair t u) = 
      pair (⊢v-rename g (⊢v-rename f t)) (⊢v-rename g (⊢v-rename f u))
    ≅〈 cong2 pair (⊢v-rename-comp-lem t) (⊢v-rename-comp-lem u) 〉
      pair (⊢v-rename (comp-ren g f) t) (⊢v-rename (comp-ren g f) u)
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {unit} {f} {g} ⋆ = 
      ⋆
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {g} (fn t) = 
      fn (⊢p-rename (wk₂ g) (⊢p-rename (wk₂ f) t))
    ≅〈 cong fn (trans (⊢p-rename-comp-lem t) (cong (λ (x : Ren _ _) → ⊢p-rename x t) (iext (λ σ → ext (λ x → sym (rename-wk₂-comp-lem x)))))) 〉
      fn (⊢p-rename (wk₂ (comp-ren g f)) t)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (return t) = 
      return (⊢v-rename g (⊢v-rename f t))
    ≅〈 cong return (⊢v-rename-comp-lem t) 〉
      return (⊢v-rename (comp-ren g f) t)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (t to u) = 
      ⊢p-rename g (⊢p-rename f t) to ⊢p-rename (wk₂ g) (⊢p-rename (wk₂ f) u)
    ≅〈 cong2 _to_ (⊢p-rename-comp-lem t) (trans (⊢p-rename-comp-lem u) (cong (λ (x : Ren _ _) → ⊢p-rename x u) (iext (λ σ → ext (λ x → sym (rename-wk₂-comp-lem x)))))) 〉
      ⊢p-rename (comp-ren g f) t to ⊢p-rename (wk₂ (comp-ren g f)) u
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (app t u) = 
      app (⊢v-rename g (⊢v-rename f t)) (⊢v-rename g (⊢v-rename f u))
    ≅〈 cong2 app (⊢v-rename-comp-lem t) (⊢v-rename-comp-lem u) 〉
      app (⊢v-rename (comp-ren g f) t) (⊢v-rename (comp-ren g f) u)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (input t u) = 
      input (⊢p-rename g (⊢p-rename f t)) (⊢p-rename g (⊢p-rename f u))
    ≅〈 cong2 input (⊢p-rename-comp-lem t) (⊢p-rename-comp-lem u) 〉
      input (⊢p-rename (comp-ren g f) t) (⊢p-rename (comp-ren g f) u)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (output0 t) = 
      output0 (⊢p-rename g (⊢p-rename f t))
    ≅〈 cong output0 (⊢p-rename-comp-lem t) 〉
      output0 (⊢p-rename (comp-ren g f) t)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (output1 t) = 
      output1 (⊢p-rename g (⊢p-rename f t))
    ≅〈 cong output1 (⊢p-rename-comp-lem t) 〉
      output1 (⊢p-rename (comp-ren g f) t)
    ∎


  -- Value terms presheaf
  VTerms : Ty → Set^Ren
  VTerms σ = record { 
    set = λ Γ → Γ ⊢v σ; 
    act = ⊢v-rename
    }


  -- Producer terms presheaf
  PTerms : Ty → Set^Ren
  PTerms σ = record { 
    set = λ Γ → Γ ⊢p σ; 
    act = ⊢p-rename
    }


  -- Action of renaming on normal and atomic values and producers
  ⊢nv-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢nv σ → Γ' ⊢nv σ
  ⊢av-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢av σ → Γ' ⊢av σ
  ⊢np-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢np σ → Γ' ⊢np σ
  ⊢ap-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢ap σ → Γ' ⊢ap σ

  ⊢nv-rename f unitNV = unitNV
  ⊢nv-rename f (pairNV t u) = pairNV (⊢nv-rename f t) (⊢nv-rename f u)
  ⊢nv-rename f (fnNV t) = fnNV (⊢np-rename (wk₂ f) t)
  ⊢av-rename f (varAV x) = varAV (f x)
  ⊢av-rename f (proj₁AV t) = proj₁AV (⊢av-rename f t)
  ⊢av-rename f (proj₂AV t) = proj₂AV (⊢av-rename f t)
  ⊢np-rename f (returnNP t) = returnNP (⊢nv-rename f t)
  ⊢np-rename f (toNP t u) = toNP (⊢ap-rename f t) (⊢np-rename (wk₂ f) u)
  ⊢np-rename f (inputNP t u) = inputNP (⊢np-rename f t) (⊢np-rename f u)
  ⊢np-rename f (output0NP t) = output0NP (⊢np-rename f t)
  ⊢np-rename f (output1NP t) = output1NP (⊢np-rename f t)
  ⊢ap-rename f (appAP t u) = appAP (⊢av-rename f t) (⊢nv-rename f u)


  -- Identity renaming lemma for renaming normal and atomic value and producer terms
  ⊢nv-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢nv σ) 
    → ⊢nv-rename id-ren t ≅ t

  ⊢av-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢av σ) 
    → ⊢av-rename id-ren t ≅ t

  ⊢np-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢np σ) 
    → ⊢np-rename id-ren t ≅ t

  ⊢ap-rename-id-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢ap σ) 
    → ⊢ap-rename id-ren t ≅ t

  ⊢nv-rename-id-lem unitNV = 
      unitNV 
    ∎
  ⊢nv-rename-id-lem (pairNV t u) = 
      pairNV (⊢nv-rename id-ren t) (⊢nv-rename id-ren u)
    ≅〈 cong2 pairNV (⊢nv-rename-id-lem t) (⊢nv-rename-id-lem u) 〉
      pairNV t u 
    ∎
  ⊢nv-rename-id-lem {Γ} {σ ⇀ τ} (fnNV t) = 
      fnNV (⊢np-rename (wk₂ id-ren) t)
    ≅〈 cong fnNV (trans (cong2 ⊢np-rename (iext (λ σ' → ext (λ x → wk₂-id-lem x))) refl) (⊢np-rename-id-lem t)) 〉
      fnNV t 
    ∎
  ⊢av-rename-id-lem (varAV x) = 
      varAV x 
    ∎
  ⊢av-rename-id-lem (proj₁AV t) = 
      proj₁AV (⊢av-rename id-ren t)
    ≅〈 cong proj₁AV (⊢av-rename-id-lem t) 〉
      proj₁AV t 
    ∎
  ⊢av-rename-id-lem (proj₂AV t) = 
      proj₂AV (⊢av-rename id-ren t) 
    ≅〈 cong proj₂AV (⊢av-rename-id-lem t) 〉
      proj₂AV t 
    ∎
  ⊢np-rename-id-lem (returnNP t) = 
      returnNP (⊢nv-rename id-ren t) 
    ≅〈 cong returnNP (⊢nv-rename-id-lem t) 〉
      returnNP t 
    ∎
  ⊢np-rename-id-lem (toNP t u) = 
      toNP (⊢ap-rename id-ren t) (⊢np-rename (wk₂ id-ren) u) 
    ≅〈 cong2 toNP (⊢ap-rename-id-lem t) (trans (cong2 ⊢np-rename (iext (λ σ' → ext (λ x → wk₂-id-lem x))) refl) (⊢np-rename-id-lem u)) 〉
      toNP t u 
    ∎
  ⊢np-rename-id-lem (inputNP t u) = 
      inputNP (⊢np-rename id-ren t) (⊢np-rename id-ren u)
    ≅〈 cong2 inputNP (⊢np-rename-id-lem t) (⊢np-rename-id-lem u) 〉
      inputNP t u 
    ∎
  ⊢np-rename-id-lem (output0NP t) = 
      output0NP (⊢np-rename id-ren t) 
    ≅〈 cong output0NP (⊢np-rename-id-lem t) 〉
      output0NP t 
    ∎
  ⊢np-rename-id-lem (output1NP t) = 
      output1NP (⊢np-rename id-ren t) 
    ≅〈 cong output1NP (⊢np-rename-id-lem t) 〉
      output1NP t 
    ∎
  ⊢ap-rename-id-lem (appAP t u) = 
      appAP (⊢av-rename id-ren t) (⊢nv-rename id-ren u)
    ≅〈 cong2 appAP (⊢av-rename-id-lem t) (⊢nv-rename-id-lem u) 〉
      appAP t u 
    ∎


  -- Composition lemma for atomic and normal value and producer renamings
  ⊢av-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢av σ) 
    → ⊢av-rename g (⊢av-rename f t) ≅ ⊢av-rename (comp-ren g f) t

  ⊢np-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢np σ) 
    → ⊢np-rename g (⊢np-rename f t) ≅ ⊢np-rename (comp-ren g f) t

  ⊢nv-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢nv σ) 
    → ⊢nv-rename g (⊢nv-rename f t) ≅ ⊢nv-rename (comp-ren g f) t

  ⊢ap-rename-comp-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (t : Γ ⊢ap σ) 
    → ⊢ap-rename g (⊢ap-rename f t) ≅ ⊢ap-rename (comp-ren g f) t

  ⊢av-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (varAV x) = 
      varAV (g (f x))
    ∎
  ⊢av-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (proj₁AV t) = 
      proj₁AV (⊢av-rename g (⊢av-rename f t))
    ≅〈 cong proj₁AV (⊢av-rename-comp-lem t) 〉
      proj₁AV (⊢av-rename (comp-ren g f) t)
    ∎
  ⊢av-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (proj₂AV t) = 
      proj₂AV (⊢av-rename g (⊢av-rename f t))
    ≅〈 cong proj₂AV (⊢av-rename-comp-lem t) 〉
      proj₂AV (⊢av-rename (comp-ren g f) t)
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {unit} {f} {g} unitNV = 
      unitNV
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} {f} {g} (pairNV t u) = 
      pairNV (⊢nv-rename g (⊢nv-rename f t)) (⊢nv-rename g (⊢nv-rename f u))
    ≅〈 cong2 pairNV (⊢nv-rename-comp-lem t) (⊢nv-rename-comp-lem u) 〉
      pairNV (⊢nv-rename (comp-ren g f) t) (⊢nv-rename (comp-ren g f) u)
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {g} (fnNV t) = 
      fnNV (⊢np-rename (wk₂ g) (⊢np-rename (wk₂ f) t))
    ≅〈 cong fnNV (trans (⊢np-rename-comp-lem t) ((cong (λ (x : Ren _ _) → ⊢np-rename x t) (iext (λ σ → ext (λ x → (sym (rename-wk₂-comp-lem x)))))))) 〉
      fnNV (⊢np-rename (wk₂ (comp-ren g f)) t)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (returnNP t) = 
      returnNP (⊢nv-rename g (⊢nv-rename f t))
    ≅〈 cong returnNP (⊢nv-rename-comp-lem t) 〉
      returnNP (⊢nv-rename (comp-ren g f) t)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (toNP t u) = 
      toNP (⊢ap-rename g (⊢ap-rename f t)) (⊢np-rename (wk₂ g) (⊢np-rename (wk₂ f) u))
    ≅〈 cong2 toNP (⊢ap-rename-comp-lem t) (trans (⊢np-rename-comp-lem u) ((cong (λ (x : Ren _ _) → ⊢np-rename x u) (iext (λ σ → ext (λ x → (sym (rename-wk₂-comp-lem x)))))))) 〉
      toNP (⊢ap-rename (comp-ren g f) t) (⊢np-rename (wk₂ (comp-ren g f)) u)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (inputNP t u) = 
      inputNP (⊢np-rename g (⊢np-rename f t)) (⊢np-rename g (⊢np-rename f u))
    ≅〈 cong2 inputNP (⊢np-rename-comp-lem t) (⊢np-rename-comp-lem u) 〉
      inputNP (⊢np-rename (comp-ren g f) t) (⊢np-rename (comp-ren g f) u)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (output0NP t) = 
      output0NP (⊢np-rename g (⊢np-rename f t))
    ≅〈 cong output0NP (⊢np-rename-comp-lem t) 〉
      output0NP (⊢np-rename (comp-ren g f) t)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (output1NP t) = 
      output1NP (⊢np-rename g (⊢np-rename f t))
    ≅〈 cong output1NP (⊢np-rename-comp-lem t) 〉
      output1NP (⊢np-rename (comp-ren g f) t)
    ∎

  ⊢ap-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (appAP t u) = 
      appAP (⊢av-rename g (⊢av-rename f t)) (⊢nv-rename g (⊢nv-rename f u))
    ≅〈 cong2 appAP (⊢av-rename-comp-lem t) (⊢nv-rename-comp-lem u) 〉
      appAP (⊢av-rename (comp-ren g f) t) (⊢nv-rename (comp-ren g f) u)
    ∎


  -- Normal values presheaf
  NVTerms : Ty → Set^Ren
  NVTerms σ = record { 
    set = λ Γ → Γ ⊢nv σ; 
    act = ⊢nv-rename
    }


  -- Normal producers presheaf
  NPTerms : Ty → Set^Ren
  NPTerms σ = record { 
    set = λ Γ → Γ ⊢np σ; 
    act = ⊢np-rename
    }


  -- Atomic values presheaf
  AVTerms : Ty → Set^Ren
  AVTerms σ = record { 
    set = λ Γ → Γ ⊢av σ; 
    act = ⊢av-rename
    }


  -- Atomic producers presheaf
  APTerms : Ty → Set^Ren
  APTerms σ = record { 
    set = λ Γ → Γ ⊢ap σ; 
    act = ⊢ap-rename 
    }


  -- Embedding atomic and normal forms to ordinary terms
  ⊢nv-embed : {σ : Ty} → Set^Ren-Map (NVTerms σ) (VTerms σ)
  ⊢av-embed : {σ : Ty} → Set^Ren-Map (AVTerms σ) (VTerms σ)
  ⊢np-embed : {σ : Ty} → Set^Ren-Map (NPTerms σ) (PTerms σ)
  ⊢ap-embed : {σ : Ty} → Set^Ren-Map (APTerms σ) (PTerms σ)
  ⊢nv-embed unitNV = ⋆
  ⊢nv-embed (pairNV t u) = pair (⊢nv-embed t) (⊢nv-embed u)
  ⊢nv-embed (fnNV t) = fn (⊢np-embed t)
  ⊢av-embed (varAV x) = var x
  ⊢av-embed (proj₁AV t) = proj₁ (⊢av-embed t)
  ⊢av-embed (proj₂AV t) = proj₂ (⊢av-embed t)
  ⊢np-embed (returnNP t) = return (⊢nv-embed t)
  ⊢np-embed (toNP t u) = ⊢ap-embed t to ⊢np-embed u
  ⊢np-embed (inputNP t u) = input (⊢np-embed t) (⊢np-embed u)
  ⊢np-embed (output0NP t) = output0 (⊢np-embed t)
  ⊢np-embed (output1NP t) = output1 (⊢np-embed t)
  ⊢ap-embed (appAP t u) = app (⊢av-embed t) (⊢nv-embed u)


