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
  ⊢v-rename f zero = zero
  ⊢v-rename f one = one
  ⊢v-rename f (pair t u) = pair (⊢v-rename f t) (⊢v-rename f u)
  ⊢v-rename f ⋆ = ⋆
  ⊢v-rename f (fn t) = fn (⊢p-rename (wk₂ f) t)
  ⊢p-rename f (return t) = return (⊢v-rename f t)
  ⊢p-rename f (t to u) = ⊢p-rename f t to ⊢p-rename (wk₂ f) u
  ⊢p-rename f (app t u) = app (⊢v-rename f t) (⊢v-rename f u)
  ⊢p-rename f (or t u) = or (⊢p-rename f t) (⊢p-rename f u)
  ⊢p-rename f (if b then t else u) = if (⊢v-rename f b) then (⊢p-rename f t) else (⊢p-rename f u)
  ⊢p-rename f (input t) = input (⊢p-rename (wk₂ f) t)
  ⊢p-rename f (output b t) = output (⊢v-rename f b) (⊢p-rename f t)


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
  ⊢v-rename-id-lem zero = 
      zero
    ∎
  ⊢v-rename-id-lem one = 
      one
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
  ⊢p-rename-id-lem (or t u) = 
      or (⊢p-rename id-ren t) (⊢p-rename id-ren u) 
    ≅〈 cong2 or (⊢p-rename-id-lem t) (⊢p-rename-id-lem u) 〉
      or t u 
    ∎
  ⊢p-rename-id-lem (if b then t else u) = 
      if (⊢v-rename id-ren b) then (⊢p-rename id-ren t) else (⊢p-rename id-ren u)
    ≅〈 cong2 (λ x y → if (⊢v-rename id-ren b) then x else y) (⊢p-rename-id-lem t) (⊢p-rename-id-lem u) 〉
      if ⊢v-rename id-ren b then t else u
    ≅〈 cong (λ x → if x then t else u) (⊢v-rename-id-lem b) 〉
      if b then t else u
    ∎
  ⊢p-rename-id-lem {Γ} (input t) = 
      input (⊢p-rename (wk₂ id-ren) t)  
    ≅〈 cong (λ (x : Ren (Γ :: bit) (Γ :: bit)) → input (⊢p-rename x t)) (iext (λ σ → ext (λ x → wk₂-id-lem x))) 〉
      input (⊢p-rename id-ren t)
    ≅〈 cong input (⊢p-rename-id-lem t) 〉
      input t
    ∎
  ⊢p-rename-id-lem (output b t) = 
      output (⊢v-rename id-ren b) (⊢p-rename id-ren t)
    ≅〈 cong (λ x → output (⊢v-rename id-ren b) x) (⊢p-rename-id-lem t) 〉
      output (⊢v-rename id-ren b) t
    ≅〈 cong (λ x → output x t) (⊢v-rename-id-lem b) 〉
      output b t
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
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {bit} {f} {g} zero = 
      zero
    ∎
  ⊢v-rename-comp-lem {Γ} {Γ'} {Γ''} {bit} {f} {g} one = 
      one
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
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (or t u) = 
      or (⊢p-rename g (⊢p-rename f t)) (⊢p-rename g (⊢p-rename f u))
    ≅〈 cong2 or (⊢p-rename-comp-lem t) (⊢p-rename-comp-lem u) 〉
      or (⊢p-rename (comp-ren g f) t) (⊢p-rename (comp-ren g f) u)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (if b then t else u) = 
      if (⊢v-rename g (⊢v-rename f b)) then (⊢p-rename g (⊢p-rename f t)) else (⊢p-rename g (⊢p-rename f u))
    ≅〈 cong2 (λ x y → if (⊢v-rename g (⊢v-rename f b)) then x else y) (⊢p-rename-comp-lem t) (⊢p-rename-comp-lem u) 〉
      if (⊢v-rename g (⊢v-rename f b)) then (⊢p-rename (comp-ren g f) t) else (⊢p-rename (comp-ren g f) u)
    ≅〈 cong (λ x → if x then (⊢p-rename (comp-ren g f) t) else (⊢p-rename (comp-ren g f) u)) (⊢v-rename-comp-lem b) 〉
      if (⊢v-rename (comp-ren g f) b) then (⊢p-rename (comp-ren g f) t) else (⊢p-rename (comp-ren g f) u)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (input t) = 
      input (⊢p-rename (wk₂ g) (⊢p-rename (wk₂ f) t))
    ≅〈 cong input (⊢p-rename-comp-lem t) 〉
      input (⊢p-rename (comp-ren (wk₂ g) (wk₂ f)) t)
    ≅〈 cong (λ (x : Ren (Γ :: bit) (Γ'' :: bit)) → input (⊢p-rename x t)) (iext (λ σ → ext (λ x → wk₂-comp-lem x))) 〉
      input (⊢p-rename (wk₂ (comp-ren g f)) t)
    ∎
  ⊢p-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (output b t) = 
      output (⊢v-rename g (⊢v-rename f b)) (⊢p-rename g (⊢p-rename f t)) 
    ≅〈 cong (λ x → output (⊢v-rename g (⊢v-rename f b)) x) (⊢p-rename-comp-lem t) 〉
      output (⊢v-rename g (⊢v-rename f b)) (⊢p-rename (comp-ren g f) t) 
    ≅〈 cong (λ x → output x (⊢p-rename (comp-ren g f) t)) (⊢v-rename-comp-lem b) 〉
      output (⊢v-rename (comp-ren g f) b) (⊢p-rename (comp-ren g f) t) 
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

  ⊢nv-rename f (bit2NV b) = bit2NV (⊢av-rename f b)
  ⊢nv-rename f zeroNV = zeroNV
  ⊢nv-rename f oneNV = oneNV
  ⊢nv-rename f unitNV = unitNV
  ⊢nv-rename f (pairNV t u) = pairNV (⊢nv-rename f t) (⊢nv-rename f u)
  ⊢nv-rename f (fnNV t) = fnNV (⊢np-rename (wk₂ f) t)
  ⊢av-rename f (varAV x) = varAV (f x)
  ⊢av-rename f (proj₁AV t) = proj₁AV (⊢av-rename f t)
  ⊢av-rename f (proj₂AV t) = proj₂AV (⊢av-rename f t)
  ⊢np-rename f (returnNP t) = returnNP (⊢nv-rename f t)
  ⊢np-rename f (toNP t u) = toNP (⊢ap-rename f t) (⊢np-rename (wk₂ f) u)
  ⊢np-rename f (orNP t u) = orNP (⊢np-rename f t) (⊢np-rename f u)
  ⊢np-rename f (ifNP b then t else u) = ifNP ⊢nv-rename f b then ⊢np-rename f t else (⊢np-rename f u)
  ⊢np-rename f (inputNP t) = inputNP (⊢np-rename (wk₂ f) t)
  ⊢np-rename f (outputNP b t) = outputNP (⊢nv-rename f b) (⊢np-rename f t)
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

  ⊢nv-rename-id-lem (bit2NV b) = 
      bit2NV (⊢av-rename id-ren b)
    ≅〈 cong bit2NV (⊢av-rename-id-lem b) 〉
      bit2NV b
    ∎
  ⊢nv-rename-id-lem unitNV = 
      unitNV 
    ∎
  ⊢nv-rename-id-lem zeroNV = 
      zeroNV 
    ∎
  ⊢nv-rename-id-lem oneNV = 
      oneNV 
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
  ⊢np-rename-id-lem (orNP t u) = 
      orNP (⊢np-rename id-ren t) (⊢np-rename id-ren u)
    ≅〈 cong2 orNP (⊢np-rename-id-lem t) (⊢np-rename-id-lem u) 〉
      orNP t u 
    ∎
  ⊢np-rename-id-lem (ifNP b then t else u) = 
      ifNP (⊢nv-rename id-ren b) then (⊢np-rename id-ren t) else (⊢np-rename id-ren u)
    ≅〈 cong2 (λ x y → ifNP (⊢nv-rename id-ren b) then x else y) (⊢np-rename-id-lem t) (⊢np-rename-id-lem u) 〉
      ifNP (⊢nv-rename id-ren b) then t else u
    ≅〈 cong (λ x → ifNP x then t else u) (⊢nv-rename-id-lem b) 〉
      ifNP b then t else u 
    ∎
  ⊢np-rename-id-lem {Γ} (inputNP t) = 
      inputNP (⊢np-rename (wk₂ id-ren) t)  
    ≅〈 cong (λ (x : Ren (Γ :: bit) (Γ :: bit)) → inputNP (⊢np-rename x t)) (iext (λ σ → ext (λ x → wk₂-id-lem x))) 〉
      inputNP (⊢np-rename id-ren t)
    ≅〈 cong inputNP (⊢np-rename-id-lem t) 〉
      inputNP t
    ∎
  ⊢np-rename-id-lem (outputNP b t) = 
      outputNP (⊢nv-rename id-ren b) (⊢np-rename id-ren t)
    ≅〈 cong (λ x → outputNP (⊢nv-rename id-ren b) x) (⊢np-rename-id-lem t) 〉
      outputNP (⊢nv-rename id-ren b) t
    ≅〈 cong (λ x → outputNP x t) (⊢nv-rename-id-lem b) 〉
      outputNP b t 
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
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {bit} {f} {g} (bit2NV b) = 
      bit2NV (⊢av-rename g (⊢av-rename f b))
    ≅〈 cong bit2NV (⊢av-rename-comp-lem b) 〉
      bit2NV (⊢av-rename (comp-ren g f) b)
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {unit} {f} {g} unitNV = 
      unitNV
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {bit} {f} {g} zeroNV = 
      zeroNV
    ∎
  ⊢nv-rename-comp-lem {Γ} {Γ'} {Γ''} {bit} {f} {g} oneNV = 
      oneNV
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
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (orNP t u) = 
      orNP (⊢np-rename g (⊢np-rename f t)) (⊢np-rename g (⊢np-rename f u))
    ≅〈 cong2 orNP (⊢np-rename-comp-lem t) (⊢np-rename-comp-lem u) 〉
      orNP (⊢np-rename (comp-ren g f) t) (⊢np-rename (comp-ren g f) u)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (ifNP b then t else u) = 
      ifNP (⊢nv-rename g (⊢nv-rename f b)) then (⊢np-rename g (⊢np-rename f t)) else (⊢np-rename g (⊢np-rename f u))
    ≅〈 cong2 (λ x y → ifNP (⊢nv-rename g (⊢nv-rename f b)) then x else y) (⊢np-rename-comp-lem t) (⊢np-rename-comp-lem u) 〉
      ifNP (⊢nv-rename g (⊢nv-rename f b)) then (⊢np-rename (comp-ren g f) t) else (⊢np-rename (comp-ren g f) u)
    ≅〈 cong (λ x → ifNP x then (⊢np-rename (comp-ren g f) t) else (⊢np-rename (comp-ren g f) u)) (⊢nv-rename-comp-lem b) 〉
      ifNP (⊢nv-rename (comp-ren g f) b) then (⊢np-rename (comp-ren g f) t) else (⊢np-rename (comp-ren g f) u)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (inputNP t) = 
      inputNP (⊢np-rename (wk₂ g) (⊢np-rename (wk₂ f) t))
    ≅〈 cong inputNP (⊢np-rename-comp-lem t) 〉
      inputNP (⊢np-rename (comp-ren (wk₂ g) (wk₂ f)) t)
    ≅〈 cong (λ (x : Ren (Γ :: bit) (Γ'' :: bit)) → inputNP (⊢np-rename x t)) (iext (λ σ → ext (λ x → wk₂-comp-lem x))) 〉
      inputNP (⊢np-rename (wk₂ (comp-ren g f)) t)
    ∎
  ⊢np-rename-comp-lem {Γ} {Γ'} {Γ''} {σ} {f} {g} (outputNP b t) = 
      outputNP (⊢nv-rename g (⊢nv-rename f b)) (⊢np-rename g (⊢np-rename f t))
    ≅〈 cong (λ x → outputNP (⊢nv-rename g (⊢nv-rename f b)) x) (⊢np-rename-comp-lem t) 〉
      outputNP (⊢nv-rename g (⊢nv-rename f b)) (⊢np-rename (comp-ren g f) t)
    ≅〈 cong (λ x → outputNP x (⊢np-rename (comp-ren g f) t)) (⊢nv-rename-comp-lem b) 〉
      outputNP (⊢nv-rename (comp-ren g f) b) (⊢np-rename (comp-ren g f) t)
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
  ⊢nv-embed (bit2NV b) = ⊢av-embed b
  ⊢nv-embed unitNV = ⋆
  ⊢nv-embed zeroNV = zero
  ⊢nv-embed oneNV = one
  ⊢nv-embed (pairNV t u) = pair (⊢nv-embed t) (⊢nv-embed u)
  ⊢nv-embed (fnNV t) = fn (⊢np-embed t)
  ⊢av-embed (varAV x) = var x
  ⊢av-embed (proj₁AV t) = proj₁ (⊢av-embed t)
  ⊢av-embed (proj₂AV t) = proj₂ (⊢av-embed t)
  ⊢np-embed (returnNP t) = return (⊢nv-embed t)
  ⊢np-embed (toNP t u) = ⊢ap-embed t to ⊢np-embed u
  ⊢np-embed (orNP t u) = or (⊢np-embed t) (⊢np-embed u)
  ⊢np-embed (ifNP b then t else u) = if (⊢nv-embed b) then (⊢np-embed t) else (⊢np-embed u)
  ⊢np-embed (inputNP t) = input (⊢np-embed t)
  ⊢np-embed (outputNP b t) = output (⊢nv-embed b) (⊢np-embed t)
  ⊢ap-embed (appAP t u) = app (⊢av-embed t) (⊢nv-embed u)


