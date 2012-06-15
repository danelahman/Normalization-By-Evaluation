------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
------ Extensions of value and effect theories -------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------


open import Utils
open import Syntax
open import Theory
open import NbE
open import Lemmas
open import Soundness
open import LogicalRelations
open import Substitutions
open import Renamings
open import Presheaves
open import PartialEquivalence
open import PartialEquivalenceLemmas
open import NormalizationResults

module Extensions where

  -- Base types
  data BaseTy : Set where
    α : BaseTy       
    Bool : BaseTy


  -- Value contexts
  ValCtx : Set
  ValCtx = List BaseTy


  -- Effect contexts
  EffCtx : Set
  EffCtx = List Unit


  -- De Bruijn indices for value contexts
  data _∈'_ : BaseTy → ValCtx → Set where
    Hd : {Γ : ValCtx} {σ : BaseTy} → σ ∈' (Γ :: σ)
    Tl : {Γ : ValCtx} {σ τ : BaseTy} → σ ∈' Γ → σ ∈' (Γ :: τ)


  -- De Bruijn indices for effect contexts
  data _∈''_ : Unit → EffCtx → Set where
    Hd : {Δ : EffCtx} {w : Unit} → w ∈'' (Δ :: w)
    Tl : {Δ : EffCtx} {w w' : Unit} → w ∈'' Δ → w ∈'' (Δ :: w')


  -- Value terms
  data _⊢_ (Γ : ValCtx) : BaseTy → Set where
    var : {σ : BaseTy} → σ ∈' Γ → Γ ⊢ σ
    true : Γ ⊢ Bool
    false : Γ ⊢ Bool


  -- Effect terms
  data _,_⊢E (Γ : ValCtx) (Δ : EffCtx) : Set where
    var : {n : Unit} → (w : n ∈'' Δ) → Γ , Δ ⊢E
    or : Γ , Δ ⊢E → Γ , Δ ⊢E → Γ , Δ ⊢E
    if_then_else : Γ ⊢ Bool → Γ , Δ ⊢E → Γ , Δ ⊢E → Γ , Δ ⊢E


  -- Extension of base types
  extend-ty : BaseTy → Ty
  extend-ty α = α
  extend-ty Bool = Bool


  -- Extension of value contexts
  extend-valctx : ValCtx → Ctx
  extend-valctx [] = []
  extend-valctx (Γ :: σ) = (extend-valctx Γ) :: (extend-ty σ)


  -- Extension of effect contexts
  extend-effctx : Ty → EffCtx → Ctx
  extend-effctx σ [] = []
  extend-effctx σ (Δ :: w) = extend-effctx σ Δ :: (One ⇀ σ)


  -- Extension of value contexts de Bruijn indices
  extend-valvar : {Γ : ValCtx}{σ : BaseTy} → σ ∈' Γ → (extend-ty σ) ∈ extend-valctx Γ
  extend-valvar Hd = Hd
  extend-valvar (Tl x) = Tl (extend-valvar x)


  -- Extension of effect contexts de Bruijn indices
  extend-effvar : {Γ : ValCtx}{Δ : EffCtx} {w : Unit} {σ : Ty} → w ∈'' Δ → (One ⇀ σ) ∈ concat (extend-valctx Γ) (extend-effctx σ Δ)
  extend-effvar Hd = Hd
  extend-effvar (Tl x) = Tl (extend-effvar x)


  -- Extension of value terms
  extend-val : {Γ : ValCtx}{σ : BaseTy} → Γ ⊢ σ → (extend-valctx Γ) ⊢v (extend-ty σ)
  extend-val (var x) = var (extend-valvar x)
  extend-val true = true
  extend-val false = false


  -- Weakening of contexts with all the variables from another context
  wk₃ : {Γ Γ' : Ctx} → Ren Γ (concat Γ Γ')
  wk₃ {Γ} {[]} x = x
  wk₃ {Γ} {Γ' :: σ} x = Tl (wk₃ {Γ} {Γ'} x)


  -- Extension of effect tersm
  extend-eff : {Γ : ValCtx} {Δ : EffCtx} → (σ : Ty) → Γ , Δ ⊢E → concat (extend-valctx Γ) (extend-effctx σ Δ) ⊢p σ
  extend-eff {Γ} {Δ} σ (var w) = app (var (extend-effvar w)) ⋆
  extend-eff σ (or t u) = or (extend-eff σ t) (extend-eff σ u)
  extend-eff {Γ} {Δ} σ (if b then t else u) = 
    if (⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b))
    then (extend-eff σ t) 
    else (extend-eff σ u)


  -- Extension of value terms to normal values
  extend-val-nv : {Γ : ValCtx}{σ : BaseTy} → Γ ⊢ σ → (extend-valctx Γ) ⊢nv (extend-ty σ)
  extend-val-nv {Γ} {α} (var x) = av2NV (varAV (extend-valvar x))
  extend-val-nv {Γ} {Bool} (var x) = bav2NV (varAV (extend-valvar x)) --
  extend-val-nv true = trueNV
  extend-val-nv false = falseNV


  -- Extension of effect terms to normal producers
  extend-eff-np : {Γ : ValCtx} {Δ : EffCtx} → (σ : Ty) → Γ , Δ ⊢E → concat (extend-valctx Γ) (extend-effctx σ Δ) ⊢np σ
  extend-eff-np σ (var w) = nf-p (app (var (extend-effvar w)) ⋆)
  extend-eff-np σ (or t u) = orNP (extend-eff-np σ t) (extend-eff-np σ u)
  extend-eff-np {Γ} {Δ} σ (if_then_else b t u) = 
    ifNP (⊢nv-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val-nv b))
    then extend-eff-np σ t 
    else (extend-eff-np σ u)


  -- Equivalence relation on the value terms (i.e., value theory)
  data _⊢_≡_ : (Γ : ValCtx) → {σ : BaseTy} → Γ ⊢ σ → Γ ⊢ σ → Set where 
    -- equivalence
    ≡-refl : {Γ : ValCtx} {σ : BaseTy} {t : Γ ⊢ σ} → Γ ⊢ t ≡ t
    ≡-symm : {Γ : ValCtx} {σ : BaseTy} {t u : Γ ⊢ σ} → Γ ⊢ t ≡ u → Γ ⊢ u ≡ t
    ≡-trans :  {Γ : ValCtx} {σ : BaseTy} {t u v : Γ ⊢ σ} → Γ ⊢ t ≡ u → Γ ⊢ u ≡ v → Γ ⊢ t ≡ v


  -- Equivalence relation on the effect terms (i.e., effect theory)
  data _,_⊢E_≡_ : (Γ : ValCtx) → (Δ : EffCtx) → Γ , Δ ⊢E → Γ , Δ ⊢E → Set where 
    -- equivalence
    ≡-refl : {Γ : ValCtx} {Δ : EffCtx} {t : Γ , Δ ⊢E} → Γ , Δ ⊢E t ≡ t
    ≡-symm : {Γ : ValCtx} {Δ : EffCtx} {t u : Γ , Δ ⊢E} → Γ , Δ ⊢E t ≡ u → Γ , Δ ⊢E u ≡ t
    ≡-trans :  {Γ : ValCtx} {Δ : EffCtx} {t u v : Γ , Δ ⊢E} → Γ , Δ ⊢E t ≡ u → Γ , Δ ⊢E u ≡ v → Γ , Δ ⊢E t ≡ v
    -- congruence
    congor : {Γ : ValCtx} {Δ : EffCtx} {t u t' u' : Γ , Δ ⊢E} → Γ , Δ ⊢E t ≡ t' → Γ , Δ ⊢E u ≡ u' → Γ , Δ ⊢E or t u ≡ or t' u'
    congif : {Γ : ValCtx} {Δ : EffCtx} {b b' : Γ ⊢ Bool} {t u t' u' : Γ , Δ ⊢E} → Γ ⊢ b ≡ b' → Γ , Δ ⊢E t ≡ t' → Γ , Δ ⊢E u ≡ u' → Γ , Δ ⊢E if b then t else u ≡ if b' then t' else u'
    -- effect theory of nondeterministic choice
    or-idempotency : {Γ : ValCtx} {Δ : EffCtx} {t : Γ , Δ ⊢E} → Γ , Δ ⊢E or t t ≡ t
    or-commutativity : {Γ : ValCtx} {Δ : EffCtx} {t u : Γ , Δ ⊢E} → Γ , Δ ⊢E or t u ≡ or u t
    or-associativity : {Γ : ValCtx} {Δ : EffCtx} {t u v : Γ , Δ ⊢E} → Γ , Δ ⊢E or (or t u) v ≡ or t (or u v)
    -- effect theory of deterministic choice
    if-true : {Γ : ValCtx} {Δ : EffCtx} {t u : Γ , Δ ⊢E} → Γ , Δ ⊢E if true then t else u ≡ t
    if-false : {Γ : ValCtx} {Δ : EffCtx} {t u : Γ , Δ ⊢E} → Γ , Δ ⊢E if false then t else u ≡ u


  -- Normal forms of extended terms are equal to the extensions into normal forms
  normalization-result4-v : 
    {Γ : ValCtx} 
    {σ : BaseTy} 
    → (t : Γ ⊢ σ) 
    → nf-v (extend-val t) ≅ (extend-val-nv t)

  normalization-result4-p : 
    {Γ : ValCtx}
    {Δ : EffCtx}
    {σ : Ty} 
    → (t : Γ , Δ ⊢E) 
    → nf-p (extend-eff σ t) ≅ (extend-eff-np σ t)

  normalization-result4-v {Γ} {α} (var x) = 
      av2NV (varAV (extend-valvar x))
    ∎
  normalization-result4-v {Γ} {Bool} (var x) = 
      bav2NV (varAV (extend-valvar x))
    ∎
  normalization-result4-v true = 
      trueNV
    ∎
  normalization-result4-v false = 
      falseNV
    ∎

  normalization-result4-p {Γ} {Δ} {σ} (var w) =
      toNP (appAP (varAV (extend-effvar w)) unitNV) (returnNP (reify-v (reflect-v {σ} (varAV Hd))))
    ∎
  normalization-result4-p {Γ} {Δ} {σ} (or t u) = 
      orNP (reify-p (⟦ extend-eff σ t ⟧p id-env)) (reify-p (⟦ extend-eff σ u ⟧p id-env))
    ≅〈 cong2 orNP (normalization-result4-p t) (normalization-result4-p u) 〉
      orNP (extend-eff-np σ t) (extend-eff-np σ u)
    ∎
  normalization-result4-p {Γ} {Δ} {σ} (if_then_else b t u) = 
      ifNP (⟦ ⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b) ⟧v id-env) then (reify-p (⟦ extend-eff σ t ⟧p id-env)) else (reify-p (⟦ extend-eff σ u ⟧p id-env))
    ≅〈 cong2 (λ x y → ifNP ⟦ ⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b) ⟧v (λ {σ'} x → reflect-v (varAV x)) then x else y) (normalization-result4-p t) (normalization-result4-p u) 〉
      ifNP (⟦ ⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b) ⟧v id-env) then (extend-eff-np σ t) else (extend-eff-np σ u)
    ≅〈 cong (λ x → ifNP x then (extend-eff-np σ t) else (extend-eff-np σ u)) (trans (sym (trans (trans (⟦⟧v-naturality (extend-val b)) (cong (⟦ extend-val b ⟧v) (iext (λ σ' → ext (λ x → reflect-naturality-v {f = (wk₃ {extend-valctx Γ} {extend-effctx σ Δ})} (varAV x)))))) (rename-env-lem-v' {f = (wk₃ {extend-valctx Γ} {extend-effctx σ Δ})} {e = id-env} (extend-val b)))) (cong (⊢nv-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ})) (normalization-result4-v b))) 〉 
      ifNP (⊢nv-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val-nv b)) then (extend-eff-np σ t) else (extend-eff-np σ u)
    ∎


  -- => direction of the conservativity theorem
  conservativity-result1-v : 
    {Γ : ValCtx} 
    {σ : BaseTy} 
    {t u : Γ ⊢ σ} 
    → Γ ⊢ t ≡ u 
    → (extend-valctx Γ) ⊢v (extend-val t) ≡ (extend-val u)

  conservativity-result1-p : 
    {Γ : ValCtx}
    {Δ : EffCtx} 
    {σ : Ty} 
    {t u : Γ , Δ ⊢E} 
    → Γ , Δ ⊢E t ≡ u 
    → concat (extend-valctx Γ) (extend-effctx σ Δ) ⊢p (extend-eff σ t) ≡ (extend-eff σ u) 

  conservativity-result1-v {Γ} {σ} {.u} {u} ≡-refl = 
      extend-val u
    v∎
  conservativity-result1-v {Γ} {σ} {t} {u} (≡-symm p) = 
      extend-val t
    ≡v〈 ≡-sym (conservativity-result1-v p) 〉
      extend-val u
    v∎
  conservativity-result1-v {Γ} {σ} {t} {v} (≡-trans {.Γ} {.σ} {.t} {u} {.v} p q) = 
      extend-val t
    ≡v〈 conservativity-result1-v p 〉
      extend-val u
    ≡v〈 conservativity-result1-v q 〉
      extend-val v
    v∎

  conservativity-result1-p {Γ} {Δ} {σ} {.u} {u} ≡-refl = 
      extend-eff σ u
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {t} {u} (≡-symm p) = 
      extend-eff σ t
    ≡p〈 ≡-sym (conservativity-result1-p p) 〉
      extend-eff σ u
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {t} {v} (≡-trans {.Γ} {.Δ} {.t} {u} {.v} p q) = 
      extend-eff σ t
    ≡p〈 conservativity-result1-p p 〉 
      extend-eff σ u
    ≡p〈 conservativity-result1-p q 〉
      extend-eff σ v
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {or t u} {or t' u'} (congor p q) = 
      or (extend-eff σ t) (extend-eff σ u)
    ≡p〈 congor (conservativity-result1-p p) (conservativity-result1-p q) 〉
      or (extend-eff σ t') (extend-eff σ u')
    p∎
  conservativity-result1-p {.Γ} {.Δ} {σ} {if b then t else u} {if b' then t' else u'} (congif {Γ} {Δ} p q r) = 
      if (⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b)) then (extend-eff σ t) else (extend-eff σ u)
    ≡p〈 congif (≡-renamecong-v (conservativity-result1-v p)) (conservativity-result1-p q) (conservativity-result1-p r) 〉
      if (⊢v-rename (wk₃ {extend-valctx Γ} {extend-effctx σ Δ}) (extend-val b')) then (extend-eff σ t') else (extend-eff σ u')
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {.(or t t)} {t} or-idempotency = 
      or (extend-eff σ t) (extend-eff σ t)
    ≡p〈 or-idempotency 〉
      extend-eff σ t
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {.(or t u)} {or u t} or-commutativity = 
      or (extend-eff σ t) (extend-eff σ u)
    ≡p〈 or-commutativity 〉
      or (extend-eff σ u) (extend-eff σ t)
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {.(or (or t u) v)} {or t (or u v)} or-associativity = 
      or (or (extend-eff σ t) (extend-eff σ u)) (extend-eff σ v)
    ≡p〈 or-associativity 〉
      or (extend-eff σ t) (or (extend-eff σ u) (extend-eff σ v))
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {if true then t else u} {.t} if-true = 
      if true then extend-eff σ t else (extend-eff σ u)
    ≡p〈 if-true 〉
      extend-eff σ t
    p∎
  conservativity-result1-p {Γ} {Δ} {σ} {if false then t else u} {.u} if-false = 
      if false then extend-eff σ t else (extend-eff σ u)
    ≡p〈 if-false 〉
      extend-eff σ u
    p∎


  -- <= direction of the conservativity theorem for the extension to normal forms
  -- ToDo: Currently not proved in Agda
  postulate
    conservativity-result2-nv : 
      {Γ : ValCtx} 
      {σ : BaseTy} 
      {t u : Γ ⊢ σ} 
      → (extend-valctx Γ) ⊢nv (extend-val-nv t) ≡ (extend-val-nv u) 
      → Γ ⊢ t ≡ u

  postulate
    conservativity-result2-np : 
      {Γ : ValCtx} 
      {Δ : EffCtx} 
      {σ : BaseTy} 
      {t u : Γ , Δ ⊢E} 
      → concat (extend-valctx Γ) (extend-effctx (extend-ty σ) Δ) ⊢np (extend-eff-np (extend-ty σ) t) ≡ (extend-eff-np (extend-ty σ) u)
      → Γ , Δ ⊢E t ≡ u

  --conservativity-result2-nv {Γ} {σ} {t} {u} p = {!!}

  --conservativity-result2-np {Γ} {Δ} {σ} {t} {u} p = {!!}


  -- <= direction of the conservativity theorem
  conservativity-result2-v : 
    {Γ : ValCtx} 
    {σ : BaseTy} 
    {t u : Γ ⊢ σ} 
    → (extend-valctx Γ) ⊢v (extend-val t) ≡ (extend-val u) 
    → Γ ⊢ t ≡ u

  conservativity-result2-p : 
    {Γ : ValCtx}
    {Δ : EffCtx} 
    {σ : BaseTy} 
    {t u : Γ , Δ ⊢E} 
    → concat (extend-valctx Γ) (extend-effctx (extend-ty σ) Δ) ⊢p (extend-eff (extend-ty σ) t) ≡ (extend-eff (extend-ty σ) u)
    → Γ , Δ ⊢E t ≡ u

  conservativity-result2-v {Γ} {σ} {t} {u} p = 
    conservativity-result2-nv (
        extend-val-nv t
      ≡nv〈 ≡-sym (≅2≡-nv (normalization-result4-v t)) 〉
        nf-v (extend-val t)
      ≡nv〈 normalization-result3-v (extend-val t) (extend-val u) p 〉
        nf-v (extend-val u)
      ≡nv〈 ≅2≡-nv (normalization-result4-v u) 〉
        extend-val-nv u
      nv∎
    )

  conservativity-result2-p {Γ} {Δ} {σ} {t} {u} p =
   conservativity-result2-np (
        extend-eff-np (extend-ty σ) t
      ≡np〈 ≡-sym (≅2≡-np (normalization-result4-p t)) 〉
        nf-p (extend-eff (extend-ty σ) t)
      ≡np〈 normalization-result3-p (extend-eff (extend-ty σ) t) (extend-eff (extend-ty σ) u) p 〉
        nf-p (extend-eff (extend-ty σ) u)
      ≡np〈 ≅2≡-np (normalization-result4-p u) 〉
        extend-eff-np (extend-ty σ) u
      np∎
    )

