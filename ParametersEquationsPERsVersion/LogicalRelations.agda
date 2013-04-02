------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
-------------- Kripke Logical Relations --------------
------------------------------------------------------

open import Utils
open import Syntax
open import Theory
open import NBE
open import Presheaves
open import Substitutions
open import Renamings
open import Monad
open import Lemmas


module LogicalRelations where


  -- Kripke logical relations relating syntax with semantics
  _◁v_ : {Γ : Ctx} {σ : Ty} → Γ ⊢v σ → ⟦ σ ⟧ Γ → Set
  _◁p_ : {Γ : Ctx} → {σ : Ty} → Γ ⊢p σ → T ⟦ σ ⟧ Γ → Set    
  _◁e_ : {Γ Γ' : Ctx} → Sub Γ Γ' → Env Γ Γ' → Set

  _◁v_ {Γ} {bit} t d = Γ ⊢v t ≡ ⊢nv-embed d
  _◁v_ {Γ} {unit} t d = True
  _◁v_ {Γ} {σ₁ ∧ σ₂} t d = ((proj₁ t) ◁v (fst d)) × ((proj₂ t) ◁v (snd d))
  _◁v_ {Γ} {σ ⇀ τ} t d = {Γ' : Ctx} → (f : Ren Γ Γ') → {u : Γ' ⊢v σ} → {e : ⟦ σ ⟧ Γ'} → u ◁v e → app (⊢v-rename f t) u ◁p d f e
  _◁p_ {Γ} {σ} t (T-return d) = Σ (Γ ⊢v σ) (λ u → (Γ ⊢p t ≡ (return u)) × (u ◁v d))
  _◁p_ {Γ} {σ} t (T-to {.Γ} {τ} u d') = Σ (Γ :: τ ⊢p σ) (λ v → (Γ ⊢p t ≡ ((⊢ap-embed u) to v)) × (v ◁p d'))
  _◁p_ {Γ} {σ} t (T-or d d') = Σ (Γ ⊢p σ) (λ u → Σ (Γ ⊢p σ) (λ v → ((Γ ⊢p t ≡ (or u v)) × (u ◁p d) × (v ◁p d'))))
  _◁p_ {Γ} {σ} t (T-if b d d') = Σ (Γ ⊢p σ) (λ u → Σ (Γ ⊢p σ) (λ v → (Γ ⊢p t ≡ (if (⊢nv-embed b) then u else v)) × (u ◁p d) × (v ◁p d')))
  _◁p_ {Γ} {σ} t (T-input d) = Σ (Γ :: bit ⊢p σ) (λ u → ((Γ ⊢p t ≡ (input[ u ])) × (u ◁p d)))
  _◁p_ {Γ} {σ} t (T-output b d) = Σ (Γ ⊢p σ) (λ u → (Γ ⊢p t ≡ (output[ (⊢nv-embed b) , u ])) × (u ◁p d))
  _◁e_ {Γ} {Γ'} s e = {σ : Ty} → (x : σ ∈ Γ) → (s x) ◁v (e x)


  -- Extending a substitutions-environments relation
  ◁c-extend-lem : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ Γ'} 
    {t : Γ' ⊢v σ} 
    {d : ⟦ σ ⟧ Γ'} 
    → s ◁e e 
    → t ◁v d 
    → ext-subst s t  ◁e env-extend e d

  ◁c-extend-lem r r' Hd = r'
  ◁c-extend-lem r r' (Tl x) = r x


  -- Monotonicity of Kripke relations
  ◁v-monotonicity : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t : Γ ⊢v σ} 
    {d : ⟦ σ ⟧ Γ} 
    → t ◁v d 
    → (⊢v-rename f t) ◁v (⟦⟧-rename {σ} f d)

  ◁p-monotonicity : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {t : Γ ⊢p σ} 
    {d : T ⟦ σ ⟧ Γ} 
    → t ◁p d 
    → (⊢p-rename f t) ◁p (T-rename {Denot σ} f d)

  ◁c-monotonicity : 
    {Γ Γ' Γ'' : Ctx} 
    {f : Sub Γ Γ'} 
    {e : Env Γ Γ'} 
    {g : Ren Γ' Γ''} 
    → f ◁e e 
    → subst-comp-ren g f ◁e env-rename g e

  -- Invariance under equational theory
  ◁v-invariance : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢v σ} 
    {d : ⟦ σ ⟧ Γ} 
    → t ◁v d 
    → (Γ ⊢v t ≡ t') 
    → t' ◁v d

  ◁p-invariance : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢p σ} 
    {d : T ⟦ σ ⟧ Γ} 
    → t ◁p d 
    → (Γ ⊢p t ≡ t') 
    → t' ◁p d

  ◁v-monotonicity {Γ} {Γ'} {bit} {f} {t} {d} r = 
    ≡-trans (≡-renamecong-v r) (⊢nv-embed-naturality d)
  ◁v-monotonicity {Γ} {Γ'} {unit} r = 
    void
  ◁v-monotonicity {Γ} {Γ'} {σ₁ ∧ σ₂} (p , q) = 
    ◁v-monotonicity {Γ} {Γ'} {σ₁} p , ◁v-monotonicity {Γ} {Γ'} {σ₂} q
  ◁v-monotonicity {Γ} {Γ'} {σ ⇀ τ} {f} {t} {d} r = λ f' {u} {e} r' → 
    ◁p-invariance 
      {t = app (⊢v-rename (comp-ren f' f) t) u} 
      {t' = app (⊢v-rename f' (⊢v-rename f t)) u} 
      {d = d (comp-ren f' f) e} 
      (r (comp-ren f' f) r') 
      (congapp (≡-sym (≅2≡-v (⊢v-rename-comp-lem t))) ≡-refl)
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-return d} r = 
    (⊢v-rename f (fst r)) , 
    ((≡-renamecong-p (fst (snd r))), 
      ◁v-monotonicity {f = f} {t = fst r} {d = d} (snd (snd r)))
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-to d d'} r = 
    (⊢p-rename (wk₂ f) (fst r)) , 
      (≡-trans 
        (≡-renamecong-p (fst (snd r))) 
        (congto (⊢ap-embed-naturality d) ≡-refl) , 
      (◁p-monotonicity {f = wk₂ f} {t = fst r} {d = d'} (snd (snd r))))
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-or d d'} r = 
    (⊢p-rename f (fst r)) , 
    ((⊢p-rename f (fst (snd r))) , 
      (((≡-renamecong-p (fst (fst (snd (snd r))))) , ◁p-monotonicity {f = f} {t = fst r} {d = d} (snd (fst (snd (snd r))))) , 
      ◁p-monotonicity {f = f} {t = fst (snd r)} {d = d'} (snd (snd (snd r)))))
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-if b d d'} r = 
    (⊢p-rename f (fst r)) , ((⊢p-rename f (fst (snd r))) , ((≡-trans (≡-renamecong-p (fst (fst (snd (snd r))))) (congif (⊢nv-embed-naturality b) ≡-refl ≡-refl)  , ◁p-monotonicity {f = f} {t = fst r} {d = d} (snd (fst (snd (snd r))))) , ◁p-monotonicity {f = f} {t = fst (snd r)} {d = d'} (snd (snd (snd r)))))
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-input d} r = 
    (⊢p-rename (wk₂ f) (fst r)) , 
    ((≡-renamecong-p (fst (snd r))) , 
      (◁p-monotonicity {f = wk₂ f} {t = fst r} {d = d} (snd (snd r))))
  ◁p-monotonicity {Γ} {Γ'} {σ} {f} {t} {T-output b d} r = 
    (⊢p-rename f (fst r)) , ((≡-trans (≡-renamecong-p (fst (snd r))) (congoutput (⊢nv-embed-naturality b) ≡-refl)) , ◁p-monotonicity {f = f} {t = fst r} {d = d} (snd (snd r)))

  ◁c-monotonicity {_} {_} {_} {_} {_} {g} r {σ} x = 
    ◁v-monotonicity {σ = σ} {f = g} (r x)

  ◁v-invariance {Γ} {bit} {t} {t'} {d} r p = 
    ≡-trans (≡-sym p) (r)
  ◁v-invariance {Γ} {unit} r p = 
    void
  ◁v-invariance {Γ} {σ₁ ∧ σ₂} (r , r') p = 
    (◁v-invariance r (congproj₁ p)) , (◁v-invariance r' (congproj₂ p))
  ◁v-invariance {Γ} {σ ⇀ τ} {t} {t'} {d} r p = λ {Γ'} f {u} {e} r' → 
    ◁p-invariance {d = d f e} (r f r') (congapp (≡-renamecong-v p) ≡-refl)
  ◁p-invariance {Γ} {σ} {t} {t'} {T-return d} r p = 
    fst r , ((≡-trans (≡-sym p) (fst (snd r))) , snd (snd r))
  ◁p-invariance {Γ} {σ} {t} {t'} {T-to d d'} r p = 
    (fst r) , ((≡-trans (≡-sym p) (fst (snd r))) , (snd (snd r))) 
  ◁p-invariance {Γ} {σ} {t} {t'} {T-or d d'} r p = 
    (fst r) , ((fst (snd r)) , (((≡-trans (≡-sym p) (fst (fst (snd (snd r))))) , (snd (fst (snd (snd r))))) , (snd (snd (snd r)))))
  ◁p-invariance {Γ} {σ} {t} {t'} {T-if b d d'} r p = 
    fst r , ((fst (snd r)) , (((≡-trans (≡-sym p) (fst (fst (snd (snd r))))) , (snd (fst (snd (snd r))))) , (snd (snd (snd r)))))
  ◁p-invariance {Γ} {σ} {t} {t'} {T-input d} r p = 
    (fst r) , ((≡-trans (≡-sym p) (fst (snd r))) , (snd (snd r)))
  ◁p-invariance {Γ} {σ} {t} {t'} {T-output b d} r p = 
    (fst r) , ((≡-trans (≡-sym p) (fst (snd r))) , (snd (snd r)))


  -- Reflect and reify lemmas
  reflect-v-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢av σ) 
    → (⊢av-embed t) ◁v (reflect-v t)

  reflect-p-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢ap σ) 
    → (⊢ap-embed t) ◁p (reflect-p t)

  reify-v-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢v σ) 
    → (d : ⟦ σ ⟧ Γ) 
    → t ◁v d 
    → Γ ⊢v t ≡ (⊢nv-embed (reify-v d))

  reify-p-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢p σ) 
    → (d : T ⟦ σ ⟧ Γ) 
    → t ◁p d 
    → Γ ⊢p t ≡ (⊢np-embed (reify-p d))

  reflect-v-lem {Γ} {bit} t = 
    ≡-refl
  reflect-v-lem {Γ} {unit} t = 
    void
  reflect-v-lem {Γ} {σ₁ ∧ σ₂} t = 
    (reflect-v-lem (proj₁AV t)) , reflect-v-lem (proj₂AV t)
  reflect-v-lem {Γ} {σ ⇀ τ} t = λ f {u} {e} r → 
    return (var Hd) , 
    (≡-trans (congapp (⊢av-embed-naturality t) (reify-v-lem u e r )) ηto , ((var Hd) , (≡-refl , (reflect-v-lem {σ = τ} (varAV Hd)))))
  reflect-p-lem {Γ} {σ} (appAP {τ} t u) = 
    return (var Hd) , (ηto , ((var Hd) , (≡-refl , (reflect-v-lem {σ = σ} (varAV Hd))))) 

  reify-v-lem {Γ} {bit} t d r = 
    r
  reify-v-lem {Γ} {unit} t d r = 
    η⋆
  reify-v-lem {Γ} {σ₁ ∧ σ₂} t (d , d') (r , r') = 
    ≡-trans 
      η× 
      (congpair (reify-v-lem (proj₁ t) d r) (reify-v-lem (proj₂ t) d' r'))
  reify-v-lem {Γ} {σ ⇀ τ} t d r = 
    ≡-trans 
      (≡-sym η⇀) 
      (congfn (reify-p-lem 
                 (app (⊢v-rename wk₁ t) (var Hd)) 
                 (d (λ {σ'} → Tl) (reflect-v {σ} (varAV Hd))) 
                 (r wk₁ (reflect-v-lem {Γ :: σ} {σ} (varAV Hd)))))
  reify-p-lem t (T-return d) r = 
    ≡-trans 
      (fst (snd r)) 
      (congreturn (reify-v-lem (fst r) d (snd (snd r))))
  reify-p-lem t (T-to u d) r = 
    ≡-trans 
      (fst (snd r)) 
      (congto ≡-refl (reify-p-lem (fst r) d (snd (snd r))))
  reify-p-lem t (T-or d d') r = 
    ≡-trans 
      (fst (fst (snd (snd r)))) 
      (congor (reify-p-lem (fst r) d (snd (fst (snd (snd r))))) 
              (reify-p-lem (fst (snd r)) d' (snd (snd (snd r)))))
  reify-p-lem t (T-if b d d') r = 
    ≡-trans 
      (fst (fst (snd (snd r)))) 
      (congif ≡-refl 
              (reify-p-lem (fst r) d (snd (fst (snd (snd r))))) 
              (reify-p-lem (fst (snd r)) d' (snd (snd (snd r)))))
  reify-p-lem t (T-input d) r = 
    ≡-trans 
      (fst (snd r)) 
      (conginput (reify-p-lem (fst r) d (snd (snd r))))
  reify-p-lem t (T-output b d) r = 
    ≡-trans 
      (fst (snd r)) 
      (congoutput ≡-refl (reify-p-lem (fst r) d (snd (snd r))))


  -- Identity substitutions and identity environments are related
  ◁c-id-subst-id-env : 
    {Γ : Ctx} 
    → (id-subst {Γ}) ◁e id-env

  ◁c-id-subst-id-env x = 
    reflect-v-lem (varAV x)


  -- Liftings of substitutions and weakenings of environments are related
  ◁c-lift-extend-lem : 
    {Γ Γ' : Ctx}
    {σ : Ty}
    {s : Sub Γ Γ'}
    {e : Env Γ Γ'}
    → s ◁e e
    → (x : σ ∈ (Γ :: bit))
    → (lift s) x ◁v env-extend (env-rename wk₁ e) (bit2NV (varAV Hd)) x
  
  ◁c-lift-extend-lem p Hd = ≡-refl
  ◁c-lift-extend-lem {Γ} {Γ'} {σ} {s} {e} p (Tl x) = ◁v-monotonicity {f = wk₁} {t = s x} {d = e x} (p x)


  -- Fundamental lemma of Kripke logical relations
  ◁v-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    → (s : Sub Γ Γ') 
    → (e : Env Γ Γ') 
    → (t : Γ ⊢v σ) 
    → s ◁e e 
    → (subst-v s t) ◁v (⟦ t ⟧v e)

  ◁p-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    → (s : Sub Γ Γ') 
    → (e : Env Γ Γ') 
    → (t : Γ ⊢p σ) 
    → s ◁e e 
    → (subst-p s t) ◁p (⟦ t ⟧p e)

  ◁p-*-strength-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ τ : Ty} 
    {s : Sub Γ Γ'} 
    {e : Env Γ Γ'} 
    → (t : Γ' ⊢p σ) 
    → (d : T ⟦ σ ⟧ Γ') 
    → (t ◁p d) 
    → (u : Γ :: σ ⊢p τ) 
    → (r : s ◁e e) 
    → (t to subst-p (lift s) u) 
      ◁p 
      * {(Env-Denot Γ) ⊗ (Denot σ)} {Denot τ} (λ v → ⟦ u ⟧p (env-extend ((fst v) {_}) (snd v))) 
        {Γ'} 
        (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d))

  ◁v-fundamental-lemma s e (var x) r = 
    r x
  ◁v-fundamental-lemma s e (proj₁ t) r = 
    fst (◁v-fundamental-lemma s e t r)
  ◁v-fundamental-lemma s e (proj₂ t) r = 
    snd (◁v-fundamental-lemma s e t r)
  ◁v-fundamental-lemma {Γ} {Γ'} {σ₁ ∧ σ₂} s e (pair t u) r = 
    ◁v-invariance 
      {t = subst-v s t} 
      {t' = proj₁ (pair (subst-v s t) (subst-v s u))} 
      {d = ⟦ t ⟧v e} 
      (◁v-fundamental-lemma s e t r) 
      (≡-sym β×₁)  , 
    ◁v-invariance 
      {t = subst-v s u} 
      {t' = proj₂ (pair (subst-v s t) (subst-v s u))} 
      {d = ⟦ u ⟧v e} 
      (◁v-fundamental-lemma s e u r) 
      (≡-sym β×₂)
  ◁v-fundamental-lemma s e ⋆ r = 
    void
  ◁v-fundamental-lemma s e zero r = 
    ≡-refl
  ◁v-fundamental-lemma s e one r = 
    ≡-refl
  ◁v-fundamental-lemma {Γ} {Γ'} {σ ⇀ τ} s e (fn t) r = λ {Γ''} f' {u} {d} r' → 
    ◁p-invariance 
      {t' = (app (fn (⊢p-rename (wk₂ f') (subst-p (lift s) t))) u)} 
      {d = (⟦ t ⟧p (env-extend (λ {σ'} x → ⟦⟧-rename {σ'} f' (e x)) d))} 
      (◁p-invariance 
        {t = subst-p (ext-subst (subst-comp-ren f' s) u) t} 
        {t' = subst-p (ext-subst (λ {σ'} → var) u) (⊢p-rename (λ {σ'} → wk₂ (λ {σ0} → f')) (subst-p (λ {σ'} → lift (λ {σ0} → s)) t))} 
        {d = ⟦ t ⟧p (λ {σ'} → env-extend (λ {σ0} x → ⟦⟧-rename {σ0} (λ {σ1} → f') (e x)) d)} 
        (◁p-fundamental-lemma 
          (λ {σ} → ext-subst (λ {σ'} x → ⊢v-rename (λ {σ0} → f') (s x)) u) 
          (λ {σ'} → env-extend (λ {σ0} x → ⟦⟧-rename {σ0} (λ {σ1} → f') (e x)) d) 
          t 
          (◁c-extend-lem (◁c-monotonicity r) r')) 
        (≅2≡-p 
          (trans 
            (trans 
              (cong 
                (λ (x : Sub _ _) → subst-p x t) 
                (iext (λ τ' → ext (λ x → 
                  trans 
                    (sym (subst-ext-lift-lem u x)) 
                    (sym (cong (subst-v (λ {σ} → ext-subst (λ {σ'} → var) u)) (rename-wk₂-lift-lem2 x))))))) 
              (sym (subst-comp-lem-p t))) 
            (sym (cong (subst-p (λ {σ} → ext-subst (λ {σ'} → var) u)) (rename-subst-lem-p t)))))) 
      β⇀
  ◁p-fundamental-lemma s e (return t) r = 
    (subst-v s t) , 
    (≡-refl , (◁v-fundamental-lemma s e t r))
  ◁p-fundamental-lemma {Γ} {Γ'} {σ} f e (_to_ {τ} t u) r = 
    ◁p-*-strength-fundamental-lemma 
      (subst-p f t) 
      (⟦ t ⟧p e) 
      (◁p-fundamental-lemma f e t r) 
      u 
      r
  ◁p-fundamental-lemma s e (app t u) r = 
    ◁p-invariance 
      {d = (⟦ t ⟧v e id-ren (⟦ u ⟧v e))} 
      (◁v-fundamental-lemma s e t r (id-ren) (◁v-fundamental-lemma s e u r)) 
      (congapp (≅2≡-v (⊢v-rename-id-lem (subst-v s t))) ≡-refl)
  ◁p-fundamental-lemma s e (or t u) r = 
    (subst-p s t) , 
    ((subst-p s u) , 
      ((≡-refl , 
      (◁p-fundamental-lemma s e t r)) , 
        (◁p-fundamental-lemma s e u r)))
  ◁p-fundamental-lemma s e (if b then t else u) r = 
    (subst-p s t) , 
    ((subst-p s u) , 
      (((congif (◁v-fundamental-lemma s e b r) ≡-refl ≡-refl) , 
        (◁p-fundamental-lemma s e t r)) , (◁p-fundamental-lemma s e u r)))
  ◁p-fundamental-lemma s e (input[ t ]) r = 
    (subst-p (lift s) t) , 
    (≡-refl , 
      (◁p-fundamental-lemma (lift s) (env-extend (env-rename wk₁ e) (bit2NV (varAV Hd))) t (λ x → ◁c-lift-extend-lem r x)))
  ◁p-fundamental-lemma s e (output[ b , t ]) r = 
    (subst-p s t) , 
    ((congoutput (◁v-fundamental-lemma s e b r) ≡-refl) , (◁p-fundamental-lemma s e t r))

  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-return d) (v , (p , r'')) u r' = 
    ◁p-invariance 
      {t' = (t to subst-p (lift s) u)} 
      {d = ⟦ u ⟧p (env-extend e d)} 
      (◁p-fundamental-lemma (ext-subst s v) (env-extend e d) u (◁c-extend-lem r' r'')) 
      (≡-trans 
        (≡-sym (≡-trans βto (≅2≡-p (ext-subst-lem-p u v)))) 
        (≡-sym (congto p ≡-refl)))
  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-to {.Γ'} {σ'} d d') r u r' = 
    ((fst r) to ⊢p-rename exchange (⊢p-rename wk₁ (subst-p (lift s) u))) , 
      (≡-trans 
        (congto (fst (snd r)) ≡-refl) 
        assocto , 
      ◁p-invariance
        {t' = fst r to ⊢p-rename exchange (⊢p-rename wk₁ (subst-p (lift s) u))}
        {d = * (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
               {Γ' :: σ'} 
               (t-r ((λ {σ} → env-rename wk₁ e {σ}) , d'))}
        (◁p-*-strength-fundamental-lemma (fst r) d' (snd (snd r)) u (◁c-monotonicity r')) 
        (congto ≡-refl 
          (≡-trans 
            (≡-trans 
              (≅2≡-p (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ τ' → ext lift-exchange-rename-lem)))) 
              (≡-sym (≅2≡-p (rename-subst-lem-p u)))) 
            (≡-sym (≅2≡-p (⊢p-rename-comp-lem (subst-p (lift s) u)))))))
  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-or d d') r u r' = 
    ((fst r) to (subst-p (lift s) u)) , 
    (((fst (snd r)) to (subst-p (lift s) u)) , 
      ((≡-trans 
         (congto (fst (fst (snd (snd r)))) ≡-refl) 
         orto , 
      ◁p-*-strength-fundamental-lemma 
        (fst r) 
        d 
        (snd (fst (snd (snd r)))) 
        u 
        r') , 
      ◁p-*-strength-fundamental-lemma 
        (fst (snd r)) 
        d' 
        (snd (snd (snd r))) 
        u 
        r'))
  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-if b d d') r u r' = 
    ((fst r) to (subst-p (lift s) u)) , 
    (((fst (snd r)) to (subst-p (lift s) u)) , 
      ((≡-trans 
         (congto (fst (fst (snd (snd r)))) ≡-refl) 
         ifto , 
      ◁p-*-strength-fundamental-lemma 
        (fst r) 
        d 
        (snd (fst (snd (snd r)))) 
        u 
        r') , 
      ◁p-*-strength-fundamental-lemma 
        (fst (snd r)) 
        d' 
        (snd (snd (snd r))) 
        u 
        r'))
  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-input d) r u r' = 
    (fst r to ⊢p-rename exchange (⊢p-rename wk₁ (subst-p (lift s) u))) , 
    (≡-trans 
      (congto (fst (snd r)) ≡-refl) 
      inputto , 
      ◁p-invariance
        {t' = (fst r to ⊢p-rename exchange (⊢p-rename wk₁ (subst-p (lift s) u)))}
        {d = * (λ v → ⟦ u ⟧p (env-extend (fst v {_}) (snd v))) 
               {Γ' :: bit} 
               (t-r ((λ {σ} → env-rename wk₁ e {σ}) , d))}
        (◁p-*-strength-fundamental-lemma 
          (fst r) 
          d 
          (snd (snd r)) 
          u 
          (◁c-monotonicity r'))
        (congto ≡-refl 
          (≡-trans 
            (≡-trans 
              (≅2≡-p (cong (λ (x : Sub _ _) → subst-p x u) (iext (λ τ' → ext lift-exchange-rename-lem)))) 
              (≡-sym (≅2≡-p (rename-subst-lem-p u)))) 
            (≡-sym (≅2≡-p (⊢p-rename-comp-lem (subst-p (lift s) u)))))))
  ◁p-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {s} {e} t (T-output b d) r u r' = 
    ((fst r) to (subst-p (lift s) u)) , 
    ((≡-trans (congto (fst (snd r)) ≡-refl) outputto) , 
      (◁p-*-strength-fundamental-lemma (fst r) d (snd (snd r)) u r'))


