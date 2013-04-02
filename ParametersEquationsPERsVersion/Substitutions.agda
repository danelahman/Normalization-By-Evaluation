------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------------- Substitutions --------------------
------------------------------------------------------

open import Utils
open import Syntax
open import Renamings
open import Presheaves

module Substitutions where


  -- Substitutions (hom-set in the opposite of category of contexts)
  Sub : Ctx → Ctx → Set
  Sub Γ Γ' = {σ : Ty} → σ ∈ Γ → Γ' ⊢v σ


  -- Lifting (or weakening) of substitutions
  lift : {Γ Γ' : Ctx} {σ : Ty} → Sub Γ Γ' → Sub (Γ :: σ) (Γ' :: σ)
  lift s Hd = var Hd
  lift s (Tl x) = ⊢v-rename Tl (s x)


  -- Action of substitution on value and producer terms
  subst-v :  {Γ Γ' : Ctx}  → Sub Γ Γ'  → {σ : Ty}  → Γ ⊢v σ  → Γ' ⊢v σ
  subst-p :  {Γ Γ' : Ctx}  → Sub Γ Γ'  → {σ : Ty}  → Γ ⊢p σ  → Γ' ⊢p σ

  subst-v s (var x) = s x
  subst-v s zero = zero
  subst-v s one = one
  subst-v s (proj₁ t) = proj₁ (subst-v s t)
  subst-v s (proj₂ t) = proj₂ (subst-v s t)
  subst-v s (pair t u) = pair (subst-v s t) (subst-v s u)
  subst-v s ⋆ = ⋆
  subst-v s (fn t) = fn (subst-p (lift s) t)

  subst-p s (return t) = return (subst-v s t)
  subst-p s (t to u) = subst-p s t to subst-p (lift s) u
  subst-p s (app t u) = app (subst-v s t) (subst-v s u)
  subst-p s (or t u) = or (subst-p s t) (subst-p s u)
  subst-p s (if b then t else u) = if (subst-v s b) then (subst-p s t) else (subst-p s u)
  subst-p s (input[ t ]) = input[ (subst-p (lift s) t) ]
  subst-p s (output[ b , t ]) = output[ (subst-v s b) , (subst-p s t) ]


  -- Identity substitution
  id-subst : {Γ : Ctx} → Sub Γ Γ
  id-subst x = var x


  -- Lifting of identity substitutions is still identity subtitution
  id-subst-lift-lem : 
    {Γ : Ctx} 
    {σ τ : Ty} 
    → (x : σ ∈ (Γ :: τ)) 
    → lift id-subst x ≅ id-subst x

  id-subst-lift-lem Hd = 
      var Hd
    ∎
  id-subst-lift-lem (Tl x) = 
      var (Tl x)
    ∎


  -- identity subtitution preserves the term
  id-subst-lem-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢v σ) 
    → subst-v id-subst t ≅ t

  id-subst-lem-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢p σ) 
    → subst-p id-subst t ≅ t

  id-subst-lem-v (var x) = 
      var x 
    ∎
  id-subst-lem-v zero = 
      zero
    ∎
  id-subst-lem-v one = 
      one
    ∎
  id-subst-lem-v (proj₁ t) = 
      proj₁ (subst-v id-subst t)
    ≅〈 cong proj₁ (id-subst-lem-v t) 〉
      proj₁ t 
    ∎
  id-subst-lem-v (proj₂ t) = 
      proj₂ (subst-v id-subst t)
    ≅〈 cong proj₂ (id-subst-lem-v t) 〉
      proj₂ t 
    ∎
  id-subst-lem-v (pair t u) = 
      pair (subst-v id-subst t) (subst-v id-subst u)
    ≅〈 cong2 pair (id-subst-lem-v t) (id-subst-lem-v u) 〉
      pair t u 
    ∎
  id-subst-lem-v ⋆ = 
      ⋆ 
    ∎
  id-subst-lem-v (fn t) = 
      fn (subst-p (lift id-subst) t)
    ≅〈 cong fn (trans (cong (λ (x : Sub _ _) → subst-p x t) (iext (λ σ → ext (λ x → id-subst-lift-lem x)))) (id-subst-lem-p t)) 〉
      fn t 
    ∎
  id-subst-lem-p (return t) = 
      return (subst-v id-subst t)
    ≅〈 cong return (id-subst-lem-v t) 〉
      return t 
    ∎
  id-subst-lem-p (t to u) = 
      subst-p id-subst t to subst-p (lift id-subst) u
    ≅〈 cong2 _to_ (id-subst-lem-p t) (trans (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ σ → ext (λ x → id-subst-lift-lem x)))) (id-subst-lem-p u)) 〉
      t to u 
    ∎
  id-subst-lem-p (app t u) = 
      app (subst-v id-subst t) (subst-v id-subst u)
    ≅〈 cong2 app (id-subst-lem-v t) (id-subst-lem-v u) 〉
      app t u 
    ∎
  id-subst-lem-p (or t u) = 
      or (subst-p id-subst t) (subst-p id-subst u)
    ≅〈 cong2 or (id-subst-lem-p t) (id-subst-lem-p u) 〉
      or t u 
    ∎
  id-subst-lem-p (if b then t else u) = 
      if (subst-v id-subst b) then (subst-p id-subst t) else (subst-p id-subst u)
    ≅〈 cong2 (λ x y → if (subst-v id-subst b) then x else y) (id-subst-lem-p t) (id-subst-lem-p u) 〉
      if (subst-v id-subst b) then t else u
    ≅〈 cong (λ x → if x then t else u) (id-subst-lem-v b) 〉
      if b then t else u 
    ∎
  id-subst-lem-p {Γ} (input[ t ]) = 
      input[ (subst-p (lift id-subst) t) ]
    ≅〈 cong (λ (x : Sub (Γ :: bit) (Γ :: bit)) → input[ (subst-p x t) ]) (iext (λ σ → ext (λ x → id-subst-lift-lem x))) 〉
      input[ (subst-p id-subst t) ]
    ≅〈 cong (λ x → input[ x ]) (id-subst-lem-p t) 〉
      input[ t ]
    ∎
  id-subst-lem-p (output[ b , t ]) = 
      output[ (subst-v id-subst b) , (subst-p id-subst t) ]
    ≅〈 cong (λ x → output[ (subst-v id-subst b) , x ]) (id-subst-lem-p t) 〉
      output[ (subst-v id-subst b) , t ]
    ≅〈 cong (λ x → output[ x , t ]) (id-subst-lem-v b) 〉
      output[ b , t ]
    ∎


  -- Composition of substitutions
  comp-subst : {Γ Γ' Γ'' : Ctx} → Sub Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
  comp-subst s s' = subst-v s · s' 


  -- Extending a substitution
  ext-subst : {Γ Γ' : Ctx} {σ : Ty} → Sub Γ Γ' → Γ' ⊢v σ → Sub (Γ :: σ) Γ'
  ext-subst s t Hd = t
  ext-subst s t (Tl x) = s x


  -- Composing substitutions with renamings in the opposite of category of contexts
  subst-comp-ren : {Γ Γ' Γ'' : Ctx} →  Ren Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
  subst-comp-ren f s = (⊢v-rename f) · s

