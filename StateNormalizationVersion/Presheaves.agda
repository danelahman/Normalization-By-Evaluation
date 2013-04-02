------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
--------------------- Presheaves ---------------------
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


  -- Coproduct of presheaves
  _⊕_ : (X Y : Set^Ren) → Set^Ren
  _⊕_ X Y =
    record {
      set = λ Γ → (set X Γ) + (set Y Γ);
      act = λ f → λ {(inl x) → inl ((act X) f x) ; (inr x) → inr ((act Y) f x)}
    }
  infixl 10 _⊕_


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
  ⊢p-rename f (lookup t u) = lookup (⊢p-rename f t) (⊢p-rename f u)
  ⊢p-rename f (update0 t) = update0 (⊢p-rename f t)
  ⊢p-rename f (update1 t) = update1 (⊢p-rename f t)


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
  ⊢np'-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢np' σ → Γ' ⊢np' σ
  ⊢ap-rename : {σ : Ty} → {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢ap σ → Γ' ⊢ap σ

  ⊢nv-rename f unitNV = unitNV
  ⊢nv-rename f (pairNV t u) = pairNV (⊢nv-rename f t) (⊢nv-rename f u)
  ⊢nv-rename f (fnNV t) = fnNV (⊢np-rename (wk₂ f) t)
  ⊢av-rename f (varAV x) = varAV (f x)
  ⊢av-rename f (proj₁AV t) = proj₁AV (⊢av-rename f t)
  ⊢av-rename f (proj₂AV t) = proj₂AV (⊢av-rename f t)
  ⊢np-rename f lookupNP[ t , u ] = lookupNP[ ⊢np'-rename f t , ⊢np'-rename f u ]
  ⊢np-rename f lookupNP[update1NP[ t ], u ] = lookupNP[update1NP[ ⊢np'-rename f t ], ⊢np'-rename f u ]
  ⊢np-rename f lookupNP[ t ,update0NP[ u ]] = lookupNP[ ⊢np'-rename f t ,update0NP[ ⊢np'-rename f u ]]
  ⊢np-rename f lookupNP[update1NP[ t ],update0NP[ u ]] = lookupNP[update1NP[ ⊢np'-rename f t ],update0NP[ ⊢np'-rename f u ]]
  ⊢np'-rename f (returnNP t) = returnNP (⊢nv-rename f t)
  ⊢np'-rename f (toNP t u) = toNP (⊢ap-rename f t) (⊢np-rename (wk₂ f) u)
  ⊢ap-rename f (appAP t u) = appAP (⊢av-rename f t) (⊢nv-rename f u)


  -- Normal values presheaf
  NVTerms : Ty → Set^Ren
  NVTerms σ = record { 
    set = λ Γ → Γ ⊢nv σ; 
    act = ⊢nv-rename
    }


  -- Normal producers presheaf  
  NP'Terms : Ty → Set^Ren
  NP'Terms σ = record { 
    set = λ Γ → Γ ⊢np' σ; 
    act = ⊢np'-rename
    }

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
  ⊢np'-embed : {σ : Ty} → Set^Ren-Map (NP'Terms σ) (PTerms σ)
  ⊢np-embed : {σ : Ty} → Set^Ren-Map (NPTerms σ) (PTerms σ)
  ⊢ap-embed : {σ : Ty} → Set^Ren-Map (APTerms σ) (PTerms σ)
  ⊢nv-embed unitNV = ⋆
  ⊢nv-embed (pairNV t u) = pair (⊢nv-embed t) (⊢nv-embed u)
  ⊢nv-embed (fnNV t) = fn (⊢np-embed t)
  ⊢av-embed (varAV x) = var x
  ⊢av-embed (proj₁AV t) = proj₁ (⊢av-embed t)
  ⊢av-embed (proj₂AV t) = proj₂ (⊢av-embed t)
  ⊢np-embed lookupNP[ t , u ] = lookup (⊢np'-embed t) (⊢np'-embed u)
  ⊢np-embed lookupNP[update1NP[ t ], u ] = lookup (update1 (⊢np'-embed t)) (⊢np'-embed u)
  ⊢np-embed lookupNP[ t ,update0NP[ u ]] = lookup (⊢np'-embed t) (update0 (⊢np'-embed u))
  ⊢np-embed lookupNP[update1NP[ t ],update0NP[ u ]] = lookup (update1 (⊢np'-embed t)) (update0 (⊢np'-embed u))
  ⊢np'-embed (returnNP t) = return (⊢nv-embed t)
  ⊢np'-embed (toNP t u) = ⊢ap-embed t to ⊢np-embed u
  ⊢ap-embed (appAP t u) = app (⊢av-embed t) (⊢nv-embed u)


