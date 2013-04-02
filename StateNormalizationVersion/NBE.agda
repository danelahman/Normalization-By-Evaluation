{-# OPTIONS --no-termination-check #-}
------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
--------- NBE algorithm for the one-bit-state --------
------------------------------------------------------
------------------------------------------------------
-- PS! Agda does not see the definition of strength --
-- terminating. --------------------------------------
------------------------------------------------------

open import Utils
open import Syntax
open import Renamings
open import Presheaves
open import Monad
open import Substitutions


module NBE where


  -- Residuating interpretation of types
  ⟦_⟧ : Ty → Ctx → Set
  ⟦_⟧ unit Γ = Unit
  ⟦_⟧ (σ₁ ∧ σ₂) Γ = ⟦ σ₁ ⟧ Γ × ⟦ σ₂ ⟧ Γ
  ⟦_⟧ (σ ⇀ τ) Γ = (⟦ σ ⟧ ⇒T ⟦ τ ⟧) Γ


  -- Action of renaming on value denotations
  ⟦⟧-rename : {σ : Ty} {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ σ ⟧ Γ → ⟦ σ ⟧ Γ'
  ⟦⟧-rename {unit} f _ = ⋆
  ⟦⟧-rename {σ₁ ∧ σ₂} f p = ⟦⟧-rename {σ₁} f (fst p) , ⟦⟧-rename {σ₂} f (snd p)
  ⟦⟧-rename {σ ⇀ τ} f h = λ g d → h (g · f) d


  -- Value denotations presheaf
  Denot : Ty → Set^Ren
  Denot σ = record { 
              set = ⟦ σ ⟧; 
              act = ⟦⟧-rename {σ}
            }


  -- Monadic denotation presheaf
  T-Denot : Ty → Set^Ren
  T-Denot σ = T-Set^Ren (Denot σ)


  -- Environments
  Env : Ctx → Ctx → Set
  Env Γ Γ' = {σ : Ty} → σ ∈ Γ → ⟦ σ ⟧ Γ'


  -- Action of renaming on environments
  env-rename : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Env Γ Γ' → Env Γ Γ''
  env-rename f e {σ} x = ⟦⟧-rename {σ} f (e x)


  -- Environment presheaf
  Env-Denot : Ctx → Set^Ren
  Env-Denot Γ = record { 
                  set = Env Γ; 
                  act = env-rename
                }


  -- Extend an environment
  env-extend : {Γ Γ' : Ctx} {σ : Ty} → Env Γ Γ' → ⟦ σ ⟧ Γ' → Env (Γ :: σ) Γ'
  env-extend e d Hd = d
  env-extend e d (Tl x) = e x


  -- Interpretation of value and producer terms
  ⟦_⟧v : {Γ : Ctx} {σ : Ty} → Γ ⊢v σ → Set^Ren-Map (Env-Denot Γ) (Denot σ) 
  ⟦_⟧p : {Γ : Ctx} {σ : Ty} → Γ ⊢p σ → Set^Ren-Map (Env-Denot Γ) (T-Denot σ)
  ⟦ var x ⟧v e = e x
  ⟦ proj₁ t ⟧v e = fst (⟦ t ⟧v e)
  ⟦ proj₂ t ⟧v e = snd (⟦ t ⟧v e)
  ⟦ pair t u ⟧v e = ⟦ t ⟧v e , ⟦ u ⟧v e
  ⟦ ⋆ ⟧v e = ⋆
  ⟦ fn t ⟧v e = λ f u → ⟦ t ⟧p (env-extend (env-rename f e) u) 
  ⟦_⟧p {Γ} {σ} (return t) e = η {Denot σ} (⟦ t ⟧v e)
  ⟦_⟧p {Γ} {σ} (_to_ {σ'} t u) {Γ'} e = * {(Env-Denot Γ) ⊗ Denot σ'} {Denot σ} (λ v → ⟦ u ⟧p (env-extend ((fst v) {_}) (snd v)) ) {Γ'} ((strength {Env-Denot Γ} {Denot σ'} {Γ'} (e , ⟦ t ⟧p e)))
  ⟦_⟧p {Γ} {σ} (lookup t u) e = Alg-lookup {Denot σ} ((⟦ t ⟧p e) , (⟦ u ⟧p e))
  ⟦_⟧p {Γ} {σ} (update0 t) e = Alg-update0 {Denot σ} (⟦ t ⟧p e)
  ⟦_⟧p {Γ} {σ} (update1 t) e = Alg-update1 {Denot σ} (⟦ t ⟧p e)
  ⟦ app t u ⟧p e = (⟦ t ⟧v e) id (⟦ u ⟧v e)


  -- Reification and reflection
  reify-v : {σ : Ty} → Set^Ren-Map (Denot σ) (NVTerms σ)
  reflect-v : {σ : Ty} → Set^Ren-Map (AVTerms σ) (Denot σ)
  reify-p : {σ : Ty} → Set^Ren-Map (T-Denot σ) (NPTerms σ)
  reflect-p : {σ : Ty} → Set^Ren-Map (APTerms σ) (T-Denot σ)

  reify-v {unit} d = unitNV
  reify-v {σ₁ ∧ σ₂} d = pairNV (reify-v (fst d)) (reify-v (snd d))
  reify-v {σ ⇀ τ} d = fnNV (reify-p (d Tl (reflect-v {σ} (varAV Hd))))

  reify-p (lfp d) with d (inl ⋆) | d (inr ⋆)
  reify-p {σ} (lfp d) | inl _ , inl d' | inl _ , inl d'' = lookupNP[ (returnNP (reify-v {σ} d')) ,update0NP[ (returnNP (reify-v {σ} d'')) ]]
  reify-p {σ} (lfp d) | inl _ , inl d' | inl _ , inr d'' = lookupNP[ (returnNP (reify-v {σ} d')) ,update0NP[ (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]]
  reify-p {σ} (lfp d) | inl _ , inr d' | inl _ , inl d'' = lookupNP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ,update0NP[ (returnNP (reify-v {σ} d'')) ]]
  reify-p {σ} (lfp d) | inl _ , inr d' | inl _ , inr d'' = lookupNP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ,update0NP[ (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]]

  reify-p {σ} (lfp d) | inl _ , inl d' | inr _ , inl d'' = lookupNP[ (returnNP (reify-v {σ} d')) , (returnNP (reify-v {σ} d'')) ]
  reify-p {σ} (lfp d) | inl _ , inl d' | inr _ , inr d'' = lookupNP[ (returnNP (reify-v {σ} d')) , (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]
  reify-p {σ} (lfp d) | inl _ , inr d' | inr _ , inl d'' = lookupNP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) , (returnNP (reify-v {σ} d'')) ]
  reify-p {σ} (lfp d) | inl _ , inr d' | inr _ , inr d'' = lookupNP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) , (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]

  reify-p {σ} (lfp d) | inr _ , inl d' | inl _ , inl d'' = lookupNP[update1NP[ (returnNP (reify-v {σ} d')) ],update0NP[ (returnNP (reify-v {σ} d'')) ]]
  reify-p {σ} (lfp d) | inr _ , inl d' | inl _ , inr d'' = lookupNP[update1NP[ (returnNP (reify-v {σ} d')) ],update0NP[ (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]]
  reify-p {σ} (lfp d) | inr _ , inr d' | inl _ , inl d'' = lookupNP[update1NP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ],update0NP[ (returnNP (reify-v {σ} d'')) ]]
  reify-p {σ} (lfp d) | inr _ , inr d' | inl _ , inr d'' = lookupNP[update1NP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ],update0NP[ (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]]

  reify-p {σ} (lfp d) | inr _ , inl d' | inr _ , inl d'' = lookupNP[update1NP[ (returnNP (reify-v {σ} d')) ], (returnNP (reify-v {σ} d'')) ]
  reify-p {σ} (lfp d) | inr _ , inl d' | inr _ , inr d'' = lookupNP[update1NP[ (returnNP (reify-v {σ} d')) ], (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]
  reify-p {σ} (lfp d) | inr _ , inr d' | inr _ , inl d'' = lookupNP[update1NP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ], (returnNP (reify-v {σ} d'')) ]
  reify-p {σ} (lfp d) | inr _ , inr d' | inr _ , inr d'' = lookupNP[update1NP[ (toNP (fst (snd d')) (reify-p (snd (snd d')))) ], (toNP (fst (snd d'')) (reify-p (snd (snd d'')))) ]

  reflect-v {unit} t = ⋆
  reflect-v {σ₁ ∧ σ₂} t = reflect-v (proj₁AV t) , reflect-v (proj₂AV t)
  reflect-v {σ ⇀ τ} t = λ f v → reflect-p (appAP (⊢av-rename f t) (reify-v v))

  reflect-p {σ} t = lfp (λ b → b , (inr (σ , (t , (η {Denot σ} (reflect-v {σ} (varAV Hd)))))))


  -- Identity environment
  id-env : {Γ : Ctx} → Env Γ Γ
  id-env x = reflect-v (varAV x)


  -- Normalization function for values
  nf-v : {σ : Ty} {Γ : Ctx} → Γ ⊢v σ → Γ ⊢nv σ
  nf-v {σ} {Γ} t = (_∘_ {Env-Denot Γ} {Denot σ} {NVTerms σ} (reify-v {σ}) ⟦ t ⟧v) (id-env {Γ})


  -- Normalization function for producers
  nf-p : {σ : Ty} {Γ : Ctx} → Γ ⊢p σ → Γ ⊢np σ
  nf-p {σ} {Γ} t = (_∘_ {Env-Denot Γ} {T-Denot σ} {NPTerms σ} (reify-p {σ}) ⟦ t ⟧p) (id-env {Γ})
