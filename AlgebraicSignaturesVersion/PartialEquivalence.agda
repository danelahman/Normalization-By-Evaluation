------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------ Partial Equivalence Relations -----------
------------------------------------------------------


open import Utils
open import Syntax
open import Theory

open import NBE
open import Presheaves
open import Renamings
open import Substitutions
open import LogicalRelations
open import Lemmas
open import Monad

module PartialEquivalence where


  -- PER on the residual monad
  data _≈T_ {Γ : Ctx} {σ : Ty} {_≈_ : {Γ : Ctx} → ⟦ σ ⟧ Γ → ⟦ σ ⟧ Γ → Set} : T ⟦ σ ⟧ Γ → T ⟦ σ ⟧ Γ → Set where
    -- partial equivalence
    ≈T-sym : {d d' : T ⟦ σ ⟧ Γ} → _≈T_ {Γ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} d' d
    ≈T-trans : {d d' d'' : T ⟦ σ ⟧ Γ} → _≈T_ {Γ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} {_≈_} d' d'' → _≈T_ {Γ} {σ} d d''
    -- congruences
    congreturn : {d d' : ⟦ σ ⟧ Γ} → _≈_ {Γ} d d' → _≈T_ {Γ} {σ} (T-return d) (T-return d')
    congto : {τ : Ty} {t t' : Γ ⊢ap τ} {d d' : T ⟦ σ ⟧ (Γ :: τ)} → Γ ⊢ap t ≡ t' → _≈T_ {Γ :: τ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} (T-to t d) (T-to t' d')
    conginput : {d d' d'' d''' : T ⟦ σ ⟧ Γ} → _≈T_ {Γ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} {_≈_} d'' d''' → _≈T_ {Γ} {σ} (T-input d d'') (T-input d' d''')
    congoutput0 : {d d' : T ⟦ σ ⟧ Γ} → _≈T_ {Γ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} (T-output0 d) (T-output0 d')
    congoutput1 : {d d' : T ⟦ σ ⟧ Γ} → _≈T_ {Γ} {σ} {_≈_} d d' → _≈T_ {Γ} {σ} (T-output1 d) (T-output1 d')

  -- PER on semantic values
  _≈_ : {Γ : Ctx} {σ : Ty} → ⟦ σ ⟧ Γ → ⟦ σ ⟧ Γ → Set
  _≈_ {Γ} {unit} d d' = d ≅ d'
  _≈_ {Γ} {σ₁ ∧ σ₂} d d' = (_≈_ {Γ} {σ₁} (fst d) (fst d')) × (_≈_ {Γ} {σ₂} (snd d) (snd d'))
  _≈_ {Γ} {σ ⇀ τ} f g = {Γ' : Ctx} {h : Ren Γ Γ'} {d d' : ⟦ σ ⟧ Γ'} → _≈_ {Γ'} {σ} d d' → (_≈T_ {Γ'} {τ} {λ {Γ} → _≈_ {Γ} {τ}} (f h d) (g h d'))


  -- PER on environments
  _≈e_ : {Γ Γ' : Ctx} → Env Γ Γ' → Env Γ Γ' → Set
  _≈e_ {Γ} {Γ'} e e' = {σ : Ty} → (x : σ ∈ Γ) → _≈_ {Γ'} {σ} (e x) (e' x)


  -- Symmetry of PER on semantic values
  ≈-sym : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} t u 
    → _≈_ {Γ} {σ} u t

  ≈-sym {Γ} {unit} p = 
    sym p
  ≈-sym {Γ} {σ₁ ∧ σ₂} p = 
    ≈-sym {Γ} {σ₁} (fst p) , (≈-sym {Γ} {σ₂} (snd p))
  ≈-sym {Γ} {σ ⇀ τ} p = λ {Γ'} q → 
    ≈T-sym (p (≈-sym {Γ'} {σ} q))


  -- Local reflexivity of PER on semantic values
  ≈-refl : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} t u 
    → _≈_ {Γ} {σ} t t

  ≈-refl {Γ} {unit} p = 
    refl
  ≈-refl {Γ} {σ₁ ∧ σ₂} p = 
    (≈-refl {Γ} {σ₁} (fst p)) , (≈-refl {Γ} {σ₂} (snd p))
  ≈-refl {Γ} {σ ⇀ τ} p = λ {Γ'} q → 
    ≈T-trans (p (≈-refl {Γ'} {σ} q)) (≈T-sym (p (≈-sym {Γ'} {σ} q)))


  -- Local reflexivity of PER on residuating monad
  ≈T-refl : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : T ⟦ σ ⟧ Γ} 
    → _≈T_ {Γ} {σ} {λ {Γ} → _≈_ {Γ} {σ}} t u 
    → _≈T_ {Γ} {σ} {λ {Γ} → _≈_ {Γ} {σ}} t t

  ≈T-refl p = 
    ≈T-trans p (≈T-sym p)


  -- Transitivity of PER on semantic values
  ≈-trans : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u v : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} t u 
    → _≈_ {Γ} {σ} u v 
    → _≈_ {Γ} {σ} t v

  ≈-trans {Γ} {unit} p q = 
    trans p q
  ≈-trans {Γ} {σ₁ ∧ σ₂} p q = 
    (≈-trans {Γ} {σ₁} (fst p) (fst q)) , (≈-trans {Γ} {σ₂} (snd p) (snd q))
  ≈-trans {Γ} {σ ⇀ τ} p q = λ {Γ'} r → 
    ≈T-trans (p r) (q (≈-refl {Γ'} {σ} (≈-sym {Γ'} {σ} r)))


  -- Local reflexivity of PER on environments
  ≈e-refl : 
    {Γ Γ' : Ctx} 
    {e e' : Env Γ Γ'} 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈e_ {Γ} {Γ'} e e

  ≈e-refl {Γ} {Γ'} {e} {e'} p {σ'} x = 
    ≈-refl {Γ'} {σ'} (p x)


  -- Symmetry of PER on environments
  ≈e-sym : 
    {Γ Γ' : Ctx} 
    {e e' : Env Γ Γ'} 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈e_ {Γ} {Γ'} e' e

  ≈e-sym {Γ} {Γ'} p {σ} x = 
    ≈-sym {Γ'} {σ} (p x)


  -- transitivity of PER on environments
  ≈e-trans : 
    {Γ Γ' : Ctx} 
    {e e' e'' : Env Γ Γ'} 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈e_ {Γ} {Γ'} e' e'' 
    → _≈e_ {Γ} {Γ'} e e''

  ≈e-trans {Γ} {Γ'} p q {σ} x = 
    ≈-trans {Γ'} {σ} (p x) (q x)
