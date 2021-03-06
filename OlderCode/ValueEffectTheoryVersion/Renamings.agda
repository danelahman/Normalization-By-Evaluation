------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
--------------------- Renamings ----------------------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------


open import Utils
open import Syntax

module Renamings where


  -- Renamings
  Ren : Ctx → Ctx → Set
  Ren Γ Γ' = {σ : Ty} → σ ∈ Γ → σ ∈ Γ'


  -- Identity renaming
  id-ren : {Γ : Ctx} → Ren Γ Γ 
  id-ren = id


  -- Composition of renamings
  comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 
  comp-ren f g = f · g


  -- Exchange variables
  exchange : {Γ : Ctx} {σ τ : Ty} → Ren (Γ :: τ :: σ) (Γ :: σ :: τ)
  exchange Hd = Tl Hd
  exchange (Tl Hd) = Hd
  exchange (Tl (Tl x)) = Tl (Tl x)


  -- Weakening of renamings by new variables
  wk₁ : {Γ : Ctx} {σ : Ty} → Ren Γ (Γ :: σ)
  wk₁ = Tl

  wk₂ : {Γ Γ' : Ctx} {σ : Ty} → Ren Γ Γ' → Ren (Γ :: σ) (Γ' :: σ)
  wk₂ f Hd = Hd
  wk₂ f (Tl v) = Tl (f v)


  -- Weakening an idendity renaming is still an idendity renaming
  wk₂-id-lem : 
    {Γ : Ctx} 
    {σ σ' : Ty} 
    → (x : σ' ∈ (Γ :: σ)) 
    → (wk₂ id-ren x) ≅ (id-ren x)

  wk₂-id-lem Hd = 
      Hd ∎
  wk₂-id-lem (Tl x) = 
      Tl x ∎
