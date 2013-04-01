------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
-------------------- NBE algorithm -------------------
------------------------------------------------------


open import Utils
open import Syntax
open import Renamings
open import Presheaves
open import Monad
open import Theory
open import Substitutions


module NBE where


  -- Rasiduating interpretation of types
  ⟦_⟧ : Ty → Ctx → Set
  ⟦_⟧ unit Γ = Unit
  ⟦_⟧ (σ₁ ∧ σ₂) Γ = ⟦ σ₁ ⟧ Γ × ⟦ σ₂ ⟧ Γ
  ⟦_⟧ (σ ⇀ τ) Γ = (⟦ σ ⟧ ⇒ ⟦ τ ⟧) Γ


  -- Action of renaming on value denotations
  ⟦⟧-rename : {σ : Ty} {Γ Γ' : Ctx} → Ren Γ Γ' → ⟦ σ ⟧ Γ → ⟦ σ ⟧ Γ'
  ⟦⟧-rename {unit} f _ = ⋆
  ⟦⟧-rename {σ₁ ∧ σ₂} f p = ⟦⟧-rename {σ₁} f (fst p) , ⟦⟧-rename {σ₂} f (snd p)
  ⟦⟧-rename {σ ⇀ τ} f h = λ g d → h (g · f) d


  -- Identity renaming lemma for renaming value denotations
  ⟦⟧-rename-id-lem : 
    {σ : Ty} 
    {Γ : Ctx} 
    → (d : ⟦ σ ⟧ Γ) 
    → ⟦⟧-rename {σ} {Γ} {Γ} id-ren d ≅ d

  ⟦⟧-rename-id-lem {unit} x = 
      ⋆ 
    ∎  
  ⟦⟧-rename-id-lem {σ₁ ∧ σ₂} x = 
      ⟦⟧-rename {σ₁ ∧ σ₂} id-ren x
    ≅〈 cong2 _,_ (⟦⟧-rename-id-lem {σ₁} (fst x)) (⟦⟧-rename-id-lem {σ₂} (snd x)) 〉
      x 
    ∎
  ⟦⟧-rename-id-lem {σ ⇀ τ} x = 
      (λ {Γ} → x {Γ}) 
    ∎


  -- Composition renaming lemma for renaming value denotations
  ⟦⟧-rename-comp-lem : 
    {σ : Ty} 
    {Γ Γ' Γ'' : Ctx} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (d : ⟦ σ ⟧ Γ) 
    → ⟦⟧-rename {σ} g (⟦⟧-rename {σ} f d) ≅ ⟦⟧-rename {σ} (comp-ren g f) d

  ⟦⟧-rename-comp-lem {unit} {Γ} {Γ'} {Γ''} {f} {g} d = 
      ⋆
    ∎
  ⟦⟧-rename-comp-lem {σ₁ ∧ σ₂} {Γ} {Γ'} {Γ''} {f} {g} d = 
      ⟦⟧-rename {σ₁ ∧ σ₂} g (⟦⟧-rename {σ₁ ∧ σ₂} f d)
    ≅〈 cong2 _,_ (⟦⟧-rename-comp-lem {σ₁} (fst d)) (⟦⟧-rename-comp-lem {σ₂} (snd d)) 〉
      ⟦⟧-rename {σ₁ ∧ σ₂} (comp-ren g f) d
    ∎
  ⟦⟧-rename-comp-lem {σ ⇀ τ} {Γ} {Γ'} {Γ''} {f} {g} d = 
      (λ {Γ} → ⟦⟧-rename {σ ⇀ τ} (comp-ren g f) d)
    ∎


  -- Value denotations presheaf
  Denot : Ty → Set^Ren
  Denot σ = record { 
              set = ⟦ σ ⟧; 
              act = ⟦⟧-rename {σ}
            }


  -- Identity renaming lemma for renaming monadic denotations
  T-rename-id-lem : 
    {σ : Ty} 
    {Γ : Ctx} 
    → (d : T ⟦ σ ⟧ Γ) 
    → T-rename {Denot σ} {Γ} {Γ} id-ren d ≅ d

  T-rename-id-lem {σ} {Γ} (T-return d) = 
      T-return (⟦⟧-rename {σ} id-ren d)
    ≅〈 cong T-return (⟦⟧-rename-id-lem {σ} d) 〉
      T-return d
    ∎
  T-rename-id-lem {σ} {Γ} (T-to {.Γ} {σ'} d d') = 
      T-to (⊢ap-rename id-ren d) (T-rename (wk₂ id-ren) d')
    ≅〈 cong2 T-to (⊢ap-rename-id-lem d) (trans (cong (λ (x : Ren _ _) → T-rename {Denot σ} x d') (iext (λ σ'' → ext (λ x → (wk₂-id-lem {Γ} {σ'} {σ''} x))))) (T-rename-id-lem {σ} d')) 〉
      T-to d d'
    ∎
  T-rename-id-lem {σ} (T-input d d') = 
      T-input (T-rename id-ren d) (T-rename id-ren d')
    ≅〈 cong2 T-input (T-rename-id-lem {σ} d) (T-rename-id-lem {σ} d') 〉
      T-input d d'
    ∎
  T-rename-id-lem {σ} (T-output0 d) = 
      T-output0 (T-rename id-ren d)
    ≅〈 cong T-output0 (T-rename-id-lem {σ} d) 〉
      T-output0 d
    ∎
  T-rename-id-lem {σ} (T-output1 d) = 
      T-output1 (T-rename id-ren d)
    ≅〈 cong T-output1 (T-rename-id-lem {σ} d) 〉
      T-output1 d
    ∎


  -- Composition renaming lemma for renaming monadic denotations
  T-rename-comp-lem : 
    {σ : Ty} 
    {Γ Γ' Γ'' : Ctx} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → (d : T ⟦ σ ⟧ Γ) 
    → T-rename {Denot σ} g (T-rename {Denot σ} f d) ≅ T-rename {Denot σ} (comp-ren g f) d

  T-rename-comp-lem {σ} {Γ} {Γ'} {Γ''} {f} {g} (T-return d) = 
      T-return (⟦⟧-rename {σ} g (⟦⟧-rename {σ} f d))
    ≅〈 cong T-return (⟦⟧-rename-comp-lem {σ} d) 〉
      T-return (⟦⟧-rename {σ} (comp-ren g f) d)
    ∎
  T-rename-comp-lem {σ} {Γ} {Γ'} {Γ''} {f} {g} (T-to d d') = 
      T-to (⊢ap-rename g (⊢ap-rename f d)) (T-rename (wk₂ g) (T-rename (wk₂ f) d'))
    ≅〈 cong2 T-to (⊢ap-rename-comp-lem d) (trans (T-rename-comp-lem {σ} d') (cong (λ (x : Ren _ _) → T-rename {Denot σ} x d') (iext (λ σ' → ext (λ x → sym (rename-wk₂-comp-lem x)))))) 〉
      T-to (⊢ap-rename (comp-ren g f) d) (T-rename (wk₂ (comp-ren g f)) d')
    ∎
  T-rename-comp-lem {σ} {Γ} {Γ'} {Γ''} {f} {g} (T-input d d') = 
      T-input (T-rename g (T-rename f d)) (T-rename g (T-rename f d'))
    ≅〈 cong2 T-input (T-rename-comp-lem {σ} d) (T-rename-comp-lem {σ} d') 〉
      T-input (T-rename (comp-ren g f) d) (T-rename (comp-ren g f) d')
    ∎
  T-rename-comp-lem {σ} {Γ} {Γ'} {Γ''} {f} {g} (T-output0 d) = 
      T-output0 (T-rename g (T-rename f d))
    ≅〈 cong T-output0 (T-rename-comp-lem {σ} d) 〉
      T-output0 (T-rename (comp-ren g f) d)
    ∎
  T-rename-comp-lem {σ} {Γ} {Γ'} {Γ''} {f} {g} (T-output1 d) = 
      T-output1 (T-rename g (T-rename f d))
    ≅〈 cong T-output1 (T-rename-comp-lem {σ} d) 〉
      T-output1 (T-rename (comp-ren g f) d)
    ∎


  -- Monadic denotation presheaf
  T-Denot : Ty → Set^Ren
  T-Denot σ = T-Set^Ren (Denot σ)


  -- Environments
  Env : Ctx → Ctx → Set
  Env Γ Γ' = {σ : Ty} → σ ∈ Γ → ⟦ σ ⟧ Γ'


  -- Action of renaming on environments
  env-rename : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Env Γ Γ' → Env Γ Γ''
  env-rename f e {σ} x = ⟦⟧-rename {σ} f (e x)


  -- Idendity renaming lemma for renaming environments
  env-rename-id-lem : 
    {Γ Γ' : Ctx} 
    → (e : Env Γ Γ') 
    → _≅_ {Env Γ Γ'} (env-rename id-ren e) {Env Γ Γ'} e

  env-rename-id-lem {Γ} {Γ'} e = 
      (λ {σ} → env-rename id-ren e {σ})
    ≅〈 iext (λ σ → ext (λ x → ⟦⟧-rename-id-lem {σ} (e x))) 〉
      (λ {σ} → e {σ})
    ∎


  -- Composition renaming lemma for renaming environments
  env-rename-comp-lem : 
    {Γ Γ' Γ'' Γ''' : List Ty} 
    {f : Ren Γ' Γ''} 
    {g : Ren Γ'' Γ'''} 
    (e : Env Γ Γ') 
    → _≅_ {Env Γ Γ'''} (env-rename g (env-rename f e)) {Env Γ Γ'''} (env-rename (comp-ren g f) e)

  env-rename-comp-lem {Γ} {Γ'} {Γ''} {Γ'''} {f} {g} e = 
      (λ {σ} → (env-rename g (env-rename f e)) {σ})
    ≅〈 iext (λ σ → ext (λ x → ⟦⟧-rename-comp-lem {σ} (e x))) 〉
      (λ {σ} → (env-rename (comp-ren g f) e) {σ})
    ∎


  -- Environments presheaf
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
  ⟦ pair t u ⟧v e = (⟦ t ⟧v e , ⟦ u ⟧v e)
  ⟦ ⋆ ⟧v e = ⋆
  ⟦ fn t ⟧v e = λ f u → ⟦ t ⟧p (env-extend (env-rename f e) u) 
  ⟦_⟧p {Γ} {σ} (return t) e = η {Denot σ} (⟦ t ⟧v e)
  ⟦_⟧p {Γ} {σ} (_to_ {σ'} t u) {Γ'} e = * {(Env-Denot Γ) ⊗ Denot σ'} {Denot σ} (λ v → ⟦ u ⟧p (env-extend ((fst v) {_}) (snd v)) ) {Γ'} ((t-r {Env-Denot Γ} {Denot σ'} {Γ'} (e , ⟦ t ⟧p e)))
  ⟦ app t u ⟧p e = (⟦ t ⟧v e) id (⟦ u ⟧v e)
  ⟦ input t u ⟧p e = Alg-input (⟦ t ⟧p e) (⟦ u ⟧p e)
  ⟦ output0 t ⟧p e = Alg-output0 (⟦ t ⟧p e)
  ⟦ output1 t ⟧p e = Alg-output1 (⟦ t ⟧p e)


  -- Reification and reflection
  reify-v : {σ : Ty} → Set^Ren-Map (Denot σ) (NVTerms σ)
  reflect-v : {σ : Ty} → Set^Ren-Map (AVTerms σ) (Denot σ)
  reify-p : {σ : Ty} → Set^Ren-Map (T-Denot σ) (NPTerms σ)
  reflect-p : {σ : Ty} → Set^Ren-Map (APTerms σ) (T-Denot σ)

  reify-v {unit} t = unitNV
  reify-v {σ₁ ∧ σ₂} t = pairNV (reify-v (fst t)) (reify-v (snd t))
  reify-v {σ ⇀ τ} t = fnNV (reify-p (t Tl (reflect-v {σ} (varAV Hd))))

  reflect-v {unit} t = ⋆
  reflect-v {σ₁ ∧ σ₂} t = reflect-v (proj₁AV t) , reflect-v (proj₂AV t)
  reflect-v {σ ⇀ τ} t = λ f v → reflect-p (appAP (⊢av-rename f t) (reify-v v))

  reify-p (T-return t) = returnNP (reify-v t)
  reify-p (T-to t u) = toNP t (reify-p u)
  reify-p (T-input t u) = inputNP (reify-p t) (reify-p u)
  reify-p (T-output0 t) = output0NP (reify-p t)
  reify-p (T-output1 t) = output1NP (reify-p t)

  reflect-p {σ} t = T-to t (η {Denot σ} (reflect-v {σ} (varAV Hd)))


  -- Identity environment
  id-env : {Γ : Ctx} → Env Γ Γ
  id-env x = reflect-v (varAV x)


  -- Normalization function for values
  nf-v : {σ : Ty} {Γ : Ctx} → Γ ⊢v σ → Γ ⊢nv σ
  nf-v {σ} {Γ} t = (_∘_ {Env-Denot Γ} {Denot σ} {NVTerms σ} (reify-v {σ}) ⟦ t ⟧v) (id-env {Γ})


  -- Normalization function for producers
  nf-p : {σ : Ty} {Γ : Ctx} → Γ ⊢p σ → Γ ⊢np σ
  nf-p {σ} {Γ} t = (_∘_ {Env-Denot Γ} {T-Denot σ} {NPTerms σ} (reify-p {σ}) ⟦ t ⟧p) (id-env {Γ})
