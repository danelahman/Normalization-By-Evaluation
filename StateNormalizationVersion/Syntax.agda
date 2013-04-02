------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
---------- Syntax of the intermediate language -------
------------------------------------------------------

open import Utils

module Syntax where


  -- Types
  infixl 6 _∧_
  data Ty : Set where
    unit : Ty
    _∧_ : Ty → Ty → Ty
    _⇀_ : Ty → Ty → Ty    


  -- Contexts
  Ctx : Set 
  Ctx = List Ty 
  

  -- Variable indices in context
  data _∈_ : Ty → Ctx → Set where
    Hd : {Γ : Ctx} {σ : Ty} → σ ∈ (Γ :: σ)
    Tl : {Γ : Ctx} {σ τ : Ty} → σ ∈ Γ → σ ∈ (Γ :: τ)


  -- Value and producer terms
  data _⊢v_ (Γ : Ctx) : Ty → Set
  data _⊢p_ (Γ : Ctx) : Ty → Set


  -- Value terms
  data _⊢v_ Γ where
    var : {σ : Ty} → σ ∈ Γ → Γ ⊢v σ
    proj₁ : {σ₁ σ₂ : Ty} → Γ ⊢v σ₁ ∧ σ₂ → Γ ⊢v σ₁
    proj₂ : {σ₁ σ₂ : Ty} → Γ ⊢v σ₁ ∧ σ₂ → Γ ⊢v σ₂
    pair : {σ₁ σ₂ : Ty} → Γ ⊢v σ₁ → Γ ⊢v σ₂ → Γ ⊢v σ₁ ∧ σ₂
    ⋆ : Γ ⊢v unit
    fn : {σ τ : Ty} → (Γ :: σ) ⊢p τ → Γ ⊢v σ ⇀ τ 


  -- Producer terms
  data _⊢p_ Γ where
    return : {σ : Ty} → Γ ⊢v σ → Γ ⊢p σ
    _to_ : {σ τ : Ty} → Γ ⊢p σ → (Γ :: σ) ⊢p τ → Γ ⊢p τ
    app : {σ τ : Ty} → Γ ⊢v σ ⇀ τ → Γ ⊢v σ → Γ ⊢p τ
    -- producer terms for the theory of global state
    lookup : {σ : Ty} → Γ ⊢p σ → Γ ⊢p σ → Γ ⊢p σ
    update0 : {σ : Ty} → Γ ⊢p σ → Γ ⊢p σ
    update1 : {σ : Ty} → Γ ⊢p σ → Γ ⊢p σ


  infix 4 _⊢v_ 
  infix 4 _⊢p_


    -- Normal and atomic forms
  data _⊢nv_ (Γ : Ctx) : Ty → Set
  data _⊢av_ (Γ : Ctx) : Ty → Set
  data _⊢np_ (Γ : Ctx) : Ty → Set
  data _⊢np'_ (Γ : Ctx) : Ty → Set
  data _⊢ap_ (Γ : Ctx) : Ty → Set


  -- Aomic value terms
  data _⊢av_ Γ where
    varAV : {σ : Ty} → σ ∈ Γ → Γ ⊢av σ
    proj₁AV : {σ₁ σ₂ : Ty} → Γ ⊢av σ₁ ∧ σ₂ → Γ ⊢av σ₁
    proj₂AV : {σ₁ σ₂ : Ty} → Γ ⊢av σ₁ ∧ σ₂ → Γ ⊢av σ₂


  -- Normal value terms
  data _⊢nv_ Γ where  
    unitNV : Γ ⊢nv unit
    pairNV : {σ₁ σ₂ : Ty} → Γ ⊢nv σ₁ → Γ ⊢nv σ₂ → Γ ⊢nv σ₁ ∧ σ₂
    fnNV : {σ τ : Ty} → (Γ :: σ) ⊢np τ → Γ ⊢nv σ ⇀ τ


  -- Normal producer terms
  data _⊢np'_ Γ where
    returnNP : {σ : Ty} → Γ ⊢nv σ → Γ ⊢np' σ
    toNP : {σ τ : Ty} → Γ ⊢ap σ → (Γ :: σ) ⊢np τ → Γ ⊢np' τ

  data _⊢np_ Γ where
    lookupNP[_,_] : {σ : Ty} → Γ ⊢np' σ → Γ ⊢np' σ → Γ ⊢np σ
    lookupNP[update1NP[_],_] : {σ : Ty} → Γ ⊢np' σ → Γ ⊢np' σ → Γ ⊢np σ
    lookupNP[_,update0NP[_]] : {σ : Ty} → Γ ⊢np' σ → Γ ⊢np' σ → Γ ⊢np σ
    lookupNP[update1NP[_],update0NP[_]] : {σ : Ty} → Γ ⊢np' σ → Γ ⊢np' σ → Γ ⊢np σ


  -- Atomic producer terms
  data _⊢ap_ Γ where
    appAP : {σ τ : Ty} → Γ ⊢av σ ⇀ τ → Γ ⊢nv σ → Γ ⊢ap τ

  infix 4 _⊢nv_ 
  infix 4 _⊢av_
  infix 4 _⊢np_
  infix 4 _⊢np'_
  infix 4 _⊢ap_

