------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
--------- Partial equivalence relations lemmas -------
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
open import PartialEquivalence

module PartialEquivalenceLemmas where


  -- PER on environments is preserved under extensions
  ≈e-extend-lem : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    {d d' : ⟦ σ ⟧ Γ'} 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈_ {Γ'} {σ} d d' 
    → _≈e_ {Γ :: σ} {Γ'} 
      (env-extend e d) 
      (env-extend e' d')

  ≈e-extend-lem p q Hd = 
    q
  ≈e-extend-lem p q (Tl x) = 
    p x


  -- PER on semantic values is preserved under renaming
  ≈-monotonicity : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {d d' : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} d d' 
    → _≈_ {Γ'} {σ} 
      (⟦⟧-rename {σ} f d) 
      (⟦⟧-rename {σ} f d')

  ≈-monotonicity {Γ} {Γ'} {unit} p = 
    refl
  ≈-monotonicity {Γ} {Γ'} {σ₁ ∧ σ₂} p = 
    (≈-monotonicity {Γ} {Γ'} {σ₁} (fst p)) , ≈-monotonicity {Γ} {Γ'} {σ₂} (snd p)
  ≈-monotonicity {Γ} {Γ'} {σ ⇀ τ} {d} {d'} p = 
    p


  -- PER on environments is preserved under renaming
  ≈e-monotonicity : 
    {Γ Γ' Γ'' : Ctx} 
    {e e' : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈e_ {Γ} {Γ''} 
      (env-rename f e) 
      (env-rename f e')

  ≈e-monotonicity {Γ} {Γ'} {Γ''} {e} {e'} {f} p {σ} x = 
    ≈-monotonicity {Γ'} {Γ''} {σ} {f} (p x)

  -- PER on environments is preserved by interpretations
  ≈-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (t : Γ ⊢v σ) 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈_ {Γ'} {σ} 
      (⟦ t ⟧v e) 
      (⟦ t ⟧v e')

  ≈T-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (t : Γ ⊢p σ) 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ'} → _≈_ {Γ'} {σ} } 
      (⟦ t ⟧p e) 
      (⟦ t ⟧p e')

  -- Composition of Kleisli extensions ans strength preserves PER on monad
  ≈-*-strength-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ τ : Ty} 
    {e e' : Env Γ Γ'} 
    {d d' : T ⟦ σ ⟧ Γ'} 
    → (t : Γ :: σ ⊢p τ) 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}}  d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {τ} {λ {Γ} → _≈_ {Γ} {τ}} 
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot τ}
         (λ v → ⟦ t ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v))) 
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d))) 
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot τ}
         (λ v → ⟦ t ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v))) 
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e' , d')))

  ≈-fundamental-lemma (var x) p = 
    p x
  ≈-fundamental-lemma (proj₁ t) p = 
    fst (≈-fundamental-lemma t p)
  ≈-fundamental-lemma (proj₂ t) p = 
    snd (≈-fundamental-lemma t p)
  ≈-fundamental-lemma (pair t u) p = 
    (≈-fundamental-lemma t p) , (≈-fundamental-lemma u p)
  ≈-fundamental-lemma ⋆ p = 
    refl
  ≈-fundamental-lemma (fn {σ} {τ} t) p = λ {Γ''} {f} {d} {d'} q → 
    ≈T-fundamental-lemma t (≈e-extend-lem (≈e-monotonicity p) q)

  ≈T-fundamental-lemma (return t) p = 
    congreturn (≈-fundamental-lemma t p)
  ≈T-fundamental-lemma {Γ} {Γ'} {τ} {e} {e'} (_to_ {σ} t u) p = 
    ≈-*-strength-fundamental-lemma u (≈T-fundamental-lemma t p) p
  ≈T-fundamental-lemma {Γ} {Γ'} {τ} {e} {e'} (app {σ} t u) p = 
    ≈-fundamental-lemma {e = e} {e' = e'} t p (≈-fundamental-lemma u p)
  ≈T-fundamental-lemma (input[ t , u ]) p = 
    conginput (≈T-fundamental-lemma t p) (≈T-fundamental-lemma u p)
  ≈T-fundamental-lemma (output0[ t ]) p = 
    congoutput0 (≈T-fundamental-lemma t p)
  ≈T-fundamental-lemma (output1[ t ]) p = 
    congoutput1 (≈T-fundamental-lemma t p)

  ≈-*-strength-fundamental-lemma t (≈T-sym p) q = 
    ≈T-sym (≈-*-strength-fundamental-lemma t p (≈e-sym q))
  ≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {e} {e'} t (≈T-trans p q) r = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma t p r) 
      (≈-*-strength-fundamental-lemma t q (λ {σ} x → ≈-refl {Γ'} {σ} (≈-sym {Γ'} {σ} (r x)) ))
  ≈-*-strength-fundamental-lemma t (congreturn p) q = 
    ≈T-fundamental-lemma t (≈e-extend-lem q p)
  ≈-*-strength-fundamental-lemma t (conginput p q) r = 
    conginput (≈-*-strength-fundamental-lemma t p r) (≈-*-strength-fundamental-lemma t q r)
  ≈-*-strength-fundamental-lemma t (congoutput0 p) r = 
    congoutput0 (≈-*-strength-fundamental-lemma t p r)
  ≈-*-strength-fundamental-lemma t (congoutput1 p) r = 
    congoutput1 (≈-*-strength-fundamental-lemma t p r)
  ≈-*-strength-fundamental-lemma t (congto p q) r = 
    congto p (≈-*-strength-fundamental-lemma t q (≈e-monotonicity r))


  -- Composition of two Kleisli extensions and strengths preserves PER on monad 
  *≈-*-strength-fundamental-lemma : 
    {Γ Γ' : Ctx} 
    {σ τ ρ : Ty} 
    {e e' : Env Γ Γ'} 
    {t : Γ :: σ :: τ ⊢p ρ} 
    {u : Γ :: σ ⊢p τ} 
    {d d' : T ⟦ σ ⟧ Γ'} 
    → _≈T_ {Γ'} {σ} {λ {Γ} 
    → _≈_ {Γ} {σ}} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {ρ} {λ {Γ} → _≈_ {Γ} {ρ}}
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot ρ}
         (λ {Γ''} v →
         * {(Env-Denot (Γ :: σ)) ⊗ (Denot τ)}
           {Denot ρ}
           (λ {Γ'''} v' →
            ⟦ t ⟧p (env-extend (λ {σ} → fst v' {σ}) (snd v')))
            {Γ''}
            (t-r {Env-Denot (Γ :: σ)} {Denot τ} {Γ''}
              (env-extend (λ {σ} → fst v {σ}) (snd v) ,
               ⟦ u ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v)))))
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d)))
      (* (λ {Γ''} v →
         * (λ {Γ'''} v' →
            ⟦ t ⟧p
            (env-extend (λ {σ} → fst v' {σ}) (snd v')))
           {Γ''}
           (t-r {Env-Denot (Γ :: σ)} {Denot τ} {Γ''}
             (env-extend (λ {σ} → fst v {σ}) (snd v) ,
              ⟦ u ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v)))))
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e' , d')))

  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (≈T-sym p) q = 
    ≈T-sym (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e'} {e} {t} {u} p (≈e-sym q))
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (≈T-trans p p') q = 
    ≈T-trans 
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} p q) 
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e'} {e'} {t} {u} p' (≈e-refl (≈e-sym q)))
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (congreturn p) q = 
    ≈-*-strength-fundamental-lemma t (≈T-fundamental-lemma u (≈e-extend-lem q p)) (≈e-extend-lem q p)
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (conginput p p') q = 
    conginput
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} p q) 
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} p' q)
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (congoutput0 p) q = 
    congoutput0
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} p q) 
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (congoutput1 p) q = 
    congoutput1
      (*≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} p q) 
  *≈-*-strength-fundamental-lemma {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} {u} (congto {σ'} p p') q = 
    congto p (*≈-*-strength-fundamental-lemma {Γ} {Γ' :: σ'} {σ} {τ} {ρ} {env-rename wk₁ e} {env-rename wk₁ e'} {t} {u} p' (≈e-monotonicity q))


  -- Congruence of reification and reflection for PERs
  reify-cong-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    {d d' : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} d d' 
    → Γ ⊢nv (reify-v {σ} d) ≡ (reify-v {σ} d')

  reify-cong-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    {d d' : T ⟦ σ ⟧ Γ} 
    → _≈T_ {Γ} {σ} {λ {Γ} 
    → _≈_ {Γ} {σ}} d d' 
    → Γ ⊢np (reify-p {σ} d) ≡ (reify-p {σ} d')

  reflect-cong-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : Γ ⊢av σ} 
    → Γ ⊢av t ≡ u 
    → _≈_ {Γ} {σ} (reflect-v {σ} t) (reflect-v {σ} u)

  reflect-cong-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : Γ ⊢ap σ} 
    → Γ ⊢ap t ≡ u 
    → _≈T_ {Γ} {σ} {λ {Γ} 
    → _≈_ {Γ} {σ}} (reflect-p {σ} t) (reflect-p {σ} u)


  reify-cong-v {Γ} {unit} p = 
    ≡-refl
  reify-cong-v {Γ} {σ₁ ∧ σ₂} p = 
    congpair (reify-cong-v (fst p)) (reify-cong-v (snd p))
  reify-cong-v {Γ} {σ ⇀ τ} p = 
    congfn (reify-cong-p (p (reflect-cong-v {Γ :: σ} {σ} refl)))
  reify-cong-p (≈T-sym p) = 
    ≡-sym (reify-cong-p p)
  reify-cong-p (≈T-trans p q) = 
    ≡-trans (reify-cong-p p) (reify-cong-p q)
  reify-cong-p (congreturn p) = 
    congreturn (reify-cong-v p)
  reify-cong-p (conginput p q) = 
    conginput (reify-cong-p p) (reify-cong-p q)
  reify-cong-p (congoutput0 p) = 
    congoutput0 (reify-cong-p p)
  reify-cong-p (congoutput1 p) = 
    congoutput1 (reify-cong-p p)
  reify-cong-p (congto p q) = 
    congto p (reify-cong-p q)

  reflect-cong-v {Γ} {unit} p = 
    refl
  reflect-cong-v {Γ} {σ₁ ∧ σ₂} refl = 
    reflect-cong-v {Γ} {σ₁} refl , reflect-cong-v {Γ} {σ₂} refl
  reflect-cong-v {Γ} {σ ⇀ τ} refl = λ {Γ'} {h} {d} {d'} p → 
    congto (congapp refl (reify-cong-v p)) (congreturn (reflect-cong-v {Γ' :: τ} {τ} refl))
  reflect-cong-p {Γ} {σ} p = 
    congto p (congreturn (reflect-cong-v {Γ :: σ} {σ} refl))


  -- Identity environments are related by PERs
  ≈-id-env : 
    {Γ : Ctx} 
    → _≈e_ {Γ} {Γ} id-env id-env
  ≈-id-env {Γ} {σ} x = 
    reflect-cong-v {Γ} {σ} refl


  -- Identity law of the action of renaming for semantics for PERs
  ⟦⟧-rename-id-lem' : 
    {σ : Ty} 
    {Γ : Ctx} 
    → (d d' : ⟦ σ ⟧ Γ) 
    → _≈_ {Γ} {σ} d d' 
    → _≈_ {Γ} {σ} (⟦⟧-rename {σ} {Γ} {Γ} id-ren d) d'

  ⟦⟧-rename-id-lem' {unit} d ⋆ p = 
    refl
  ⟦⟧-rename-id-lem' {σ₁ ∧ σ₂} d d' p = 
    (⟦⟧-rename-id-lem' {σ₁} (fst d) (fst d') (fst p)) , (⟦⟧-rename-id-lem' {σ₂} (snd d) (snd d') (snd p))
  ⟦⟧-rename-id-lem' {σ ⇀ τ} d d' p = λ q → 
    p q


  -- Composition law of the action of renaming for semantics for PERs
  ⟦⟧-rename-comp-lem' : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {g : Ren Γ' Γ''} 
    {d d' : ⟦ σ ⟧ Γ} 
    → _≈_ {Γ} {σ} d d' 
    → _≈_ {Γ''} {σ} 
      (⟦⟧-rename {σ} (comp-ren g f) d) 
      (⟦⟧-rename {σ} g (⟦⟧-rename {σ} f d'))

  ⟦⟧-rename-comp-lem' {Γ} {Γ'} {Γ''} {unit} p = 
    refl
  ⟦⟧-rename-comp-lem' {Γ} {Γ'} {Γ''} {σ₁ ∧ σ₂} p = 
    (⟦⟧-rename-comp-lem' {Γ} {Γ'} {Γ''} {σ₁} (fst p)) , (⟦⟧-rename-comp-lem' {Γ} {Γ'} {Γ''} {σ₂} (snd p))
  ⟦⟧-rename-comp-lem' {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {g} {d} {d'} p = λ q → 
    p q


  -- Relation between environment extensions and environments derived from substitutions
  sub-to-env-ext-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {s : Sub Γ Γ'}
    {e e' : Env Γ' Γ''} 
    → (u : Γ' ⊢v σ) 
    → _≈e_ {Γ'} {Γ''} e e' 
    → (x : σ' ∈ (Γ :: σ)) 
    → _≈_ {Γ''} {σ'} 
      (sub-to-env (ext-subst s u) e x) 
      ((env-extend (sub-to-env s e') (⟦ u ⟧v e')) x)

  sub-to-env-ext-lem u p Hd = 
    ≈-fundamental-lemma u p
  sub-to-env-ext-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} u p (Tl x) = 
    ≈-fundamental-lemma (s x) p


  -- Congruence for the composition Kleisli extensions, unit and strength
  *-strength-leaf-lem' : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (d d' : T ⟦ σ ⟧ Γ') 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}} 
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot σ}
         (λ v → η {Denot σ} (snd v)) 
         {Γ'}
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d))) 
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot σ}
         (λ v → η {Denot σ} (snd v)) 
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e' , d')))

  *-strength-leaf-lem' d d' (≈T-sym p) q = 
    ≈T-sym (*-strength-leaf-lem' d' d p (≈e-sym q))
  *-strength-leaf-lem' .d .d'' (≈T-trans {d} {d'} {d''} p p') q = 
    ≈T-trans 
      (*-strength-leaf-lem' d d' p q) 
      (*-strength-leaf-lem' d' d'' p' (≈e-refl (≈e-sym q)))
  *-strength-leaf-lem' .(T-return d) .(T-return d') (congreturn {d} {d'} p) q = 
    congreturn p
  *-strength-leaf-lem' .(T-input d d'') .(T-input d' d''') (conginput {d} {d'} {d''} {d'''} p p') q = 
    conginput (*-strength-leaf-lem' d d' p q) (*-strength-leaf-lem' d'' d''' p' q)
  *-strength-leaf-lem' .(T-output0 d) .(T-output0 d') (congoutput0 {d} {d'} p) q = 
    congoutput0 (*-strength-leaf-lem' d d' p q)
  *-strength-leaf-lem' .(T-output1 d) .(T-output1 d') (congoutput1 {d} {d'} p) q = 
    congoutput1 (*-strength-leaf-lem' d d' p q)
  *-strength-leaf-lem' .(T-to t d) .(T-to t' d') (congto {τ} {t} {t'} {d} {d'} p p') q = 
    congto p (*-strength-leaf-lem' d d' p' (≈e-monotonicity q))


  -- An eta law for Kleisli extensions
  *-strength-leaf-lem : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (d d' : T ⟦ σ ⟧ Γ') 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}} 
      d 
      (* {(Env-Denot Γ) ⊗ (Denot σ)}
         {Denot σ}
         (λ v → η {Denot σ} (snd v)) 
         {Γ'}
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d')))

  *-strength-leaf-lem d d' (≈T-sym p) q = 
    ≈T-trans 
      (≈T-sym p) 
      (≈T-trans 
        (*-strength-leaf-lem d' d p q) 
        (*-strength-leaf-lem' d d' (≈T-sym p) (≈e-refl q)))
  *-strength-leaf-lem .d .d'' (≈T-trans {d} {d'} {d''} p p') q = 
    ≈T-trans 
      p 
      (*-strength-leaf-lem d' d'' p' q)
  *-strength-leaf-lem .(T-return d) .(T-return d') (congreturn {d} {d'} p) q = 
    congreturn p
  *-strength-leaf-lem .(T-input d d'') .(T-input d' d''') (conginput {d} {d'} {d''} {d'''} p p') q = 
    conginput (*-strength-leaf-lem d d' p q) (*-strength-leaf-lem d'' d''' p' q)
  *-strength-leaf-lem .(T-output0 d) .(T-output0 d') (congoutput0 {d} {d'} p) q = 
    congoutput0 (*-strength-leaf-lem d d' p q)
  *-strength-leaf-lem .(T-output1 d) .(T-output1 d') (congoutput1 {d} {d'} p) q = 
    congoutput1 (*-strength-leaf-lem d d' p q)
  *-strength-leaf-lem .(T-to t d) .(T-to t' d') (congto {τ} {t} {t'} {d} {d'} p p') q = 
    congto p (*-strength-leaf-lem d d' p' (≈e-monotonicity q))


  -- Renaming variables in environment extensions
  env-extend-rename-wk₂-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    {d d' : ⟦ σ ⟧ Γ''} 
    → _≈_ {Γ''} {σ} d d' 
    → _≈e_ {Γ'} {Γ''} e e' 
    → (x : σ' ∈ (Γ :: σ)) 
    → _≈_ {Γ''} {σ'} 
      (env-extend (λ x' → (e (f x'))) d x) 
      (env-extend e' d' (wk₂ f x))

  env-extend-rename-wk₂-lem p q Hd = 
    p
  env-extend-rename-wk₂-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} p q (Tl x) = 
    q (f x)


  -- Naturality of environment extensions
  env-extend-naturality : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {e e' : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    {d d' : ⟦ σ ⟧ Γ'} 
    → _≈_ {Γ'} {σ} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → (x : σ' ∈ (Γ :: σ)) 
    → _≈_ {Γ''} {σ'} 
      (env-extend (env-rename f e) (⟦⟧-rename {σ} f d) x) 
      (⟦⟧-rename {σ'} f (env-extend e' d' x))

  env-extend-naturality {Γ} {Γ'} {Γ''} {σ} {.σ} p q Hd = 
    ≈-monotonicity {Γ'} {Γ''} {σ} p
  env-extend-naturality {Γ} {Γ'} {Γ''} {σ} {σ'} p q (Tl x) = 
    ≈-monotonicity {Γ'} {Γ''} {σ'} (q x)


  -- Adding (removing) redundant values to environments
  env-extend-exchange-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' σ'' : Ty} 
    {e e' : Env Γ Γ'} 
    {d d' : ⟦ σ'' ⟧ Γ'} 
    {d'' : ⟦ σ' ⟧ Γ'} 
    → _≈_ {Γ'} {σ''} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → (x : σ ∈ (Γ :: σ'')) 
    → _≈_ {Γ'} {σ} 
      (env-extend e d x) 
      (env-extend (env-extend {Γ} {Γ'} {σ'} e' d'') d' (exchange (Tl x)))

  env-extend-exchange-lem p q Hd = 
    p
  env-extend-exchange-lem p q (Tl x) = 
    q x


  -- Renaming variables in environments before interpreting terms
  rename-env-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈_ {Γ''} {σ} 
      (⟦ t ⟧v (λ x → ⟦ var (f x) ⟧v e)) 
      (⟦ ⊢v-rename f t ⟧v e')

  rename-env-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {f : Ren Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈T_ {Γ''} {σ} {λ {Γ} → _≈_ {Γ} {σ}} 
      (⟦ t ⟧p (λ x → ⟦ var (f x) ⟧v e)) 
      (⟦ ⊢p-rename f t ⟧p e')

  *-rename-env-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {f : Ren Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (u : Γ :: σ' ⊢p σ) 
    → (d d' : T ⟦ σ' ⟧ Γ'') 
    → _≈T_ {Γ''} {σ'} {λ {Γ} → _≈_ {Γ} {σ'}} d d' 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈T_ {Γ''} {σ} {λ {Γ} → _≈_ {Γ} {σ}}
    (* {(Env-Denot Γ) ⊗ (Denot σ')} 
      (λ v → ⟦ u ⟧p (env-extend (fst v) (snd v))) 
      {Γ''} 
      (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((λ {σ} x → e {σ} (f x)) , d))) 
    (* {(Env-Denot Γ') ⊗ (Denot σ')} 
      (λ v → ⟦ ⊢p-rename (wk₂ f) u ⟧p (env-extend (fst v) (snd v))) 
      {Γ''} 
      (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e' {σ}) , d')))

  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} {e'} u d d' (≈T-sym p) q = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma {e = λ x → e (f x)} {e' = λ x → e (f x)} {d = d} {d' = d'} u (≈T-sym p) (λ {σ} x → ≈-refl {Γ''} {σ} (q (f x)))) 
      (≈T-trans 
        (*-rename-env-lem u d' d p q) 
        (≈-*-strength-fundamental-lemma {e = e'} {e' = e'} {d = d} {d' = d'} (⊢p-rename (wk₂ f) u) (≈T-sym p) (≈e-refl (≈e-sym q))))
  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} {e'} u .d .d'' (≈T-trans {d} {d'} {d''} p p') q = 
    ≈T-trans 
      (*-rename-env-lem u d d' p q) 
      (≈-*-strength-fundamental-lemma (⊢p-rename (wk₂ f) u) p' (≈e-refl (≈e-sym q)))
  *-rename-env-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {f} {e} {e'} u .(T-return d) .(T-return d') (congreturn {d} {d'} p) q = 
    ≈T-trans 
      (≈T-fundamental-lemma u (λ x → env-extend-rename-wk₂-lem (≈-refl {Γ''} {σ'} p) (≈e-refl {Γ'} {Γ''} q) x )) 
      (rename-env-lem-p {f = wk₂ f} {e = env-extend e d} {e' = env-extend e' d'} u (≈e-extend-lem q p))
  *-rename-env-lem u .(T-input d d'') .(T-input d' d''') (conginput {d} {d'} {d''} {d'''} p p') q = 
    conginput (*-rename-env-lem u d d' p q) (*-rename-env-lem u d'' d''' p' q)
  *-rename-env-lem u .(T-output0 d) .(T-output0 d') (congoutput0 {d} {d'} p) q = 
    congoutput0 (*-rename-env-lem u d d' p q)
  *-rename-env-lem u .(T-output1 d) .(T-output1 d') (congoutput1 {d} {d'} p) q = 
    congoutput1 (*-rename-env-lem u d d' p q)
  *-rename-env-lem u .(T-to t d) .(T-to t' d') (congto {τ} {t} {t'} {d} {d'} p p') q = 
    congto p (*-rename-env-lem u d d' p' (≈e-monotonicity q))

  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ} {f} (var x) p = 
    p (f x)
  rename-env-lem-v (proj₁ t) p = 
    fst (rename-env-lem-v t p)
  rename-env-lem-v (proj₂ t) p = 
    snd (rename-env-lem-v t p)
  rename-env-lem-v (pair t u) p = 
    (rename-env-lem-v t p) , (rename-env-lem-v u p)
  rename-env-lem-v ⋆ p = 
    refl
  rename-env-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {f} {e} {e'} (fn t) p = λ {Γ'''} {h} {d} {d'} q → 
    ≈T-trans (≈T-fundamental-lemma t (λ {σ'} x → env-extend-rename-wk₂-lem {e = env-rename h e} {e' = env-rename h e} (≈-refl {Γ'''} {σ} q) (≈e-monotonicity (≈e-refl p)) x)) (rename-env-lem-p t (≈e-extend-lem (≈e-monotonicity p) q))
  rename-env-lem-p (return t) p = 
    congreturn (rename-env-lem-v t p)
  rename-env-lem-p {Γ} {Γ'} {Γ''} {σ} {f} {e} {e'} (t to u) p = 
    *-rename-env-lem u (⟦ t ⟧p (λ x → e (f x))) (⟦ ⊢p-rename f t ⟧p e') (rename-env-lem-p t p) p
  rename-env-lem-p (app t u) p = 
    (rename-env-lem-v t p) (rename-env-lem-v u p)
  rename-env-lem-p (input[ t , u ]) p = 
    conginput (rename-env-lem-p t p) (rename-env-lem-p u p)
  rename-env-lem-p (output0[ t ]) p = 
    congoutput0 (rename-env-lem-p t p)
  rename-env-lem-p (output1[ t ]) p = 
    congoutput1 (rename-env-lem-p t p)


  -- Extending environments derived from substitutions
  sub-to-env-lift-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {s : Sub Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (d d' : ⟦ σ ⟧ Γ'') 
    → _≈_ {Γ''} {σ} d d' 
    → _≈e_ {Γ'} {Γ''} e e' 
    → (x : σ' ∈ (Γ :: σ)) 
    → _≈_ {Γ''} {σ'} 
      (env-extend (sub-to-env s e) d x) 
      (sub-to-env (lift s) (env-extend e' d') x)

  sub-to-env-lift-lem d d' p q Hd = 
    p
  sub-to-env-lift-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} {e'} d d' p q (Tl x) = 
    rename-env-lem-v (s x) (≈e-extend-lem q p) 


  -- Naturality of the interpretation map for PERs
  ⟦⟧v-naturality' : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    {f : Ren Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈_ {Γ''} {σ} 
      (⟦⟧-rename {σ} f (⟦ t ⟧v e)) 
      (⟦ t ⟧v (env-rename f e'))

  ⟦⟧v-naturality' (var x) p = 
    ≈e-monotonicity p x
  ⟦⟧v-naturality' (proj₁ t) p = 
    fst (⟦⟧v-naturality' t p)
  ⟦⟧v-naturality' (proj₂ t) p = 
    snd (⟦⟧v-naturality' t p)
  ⟦⟧v-naturality' (pair t u) p = 
    (⟦⟧v-naturality' t p) , (⟦⟧v-naturality' u p)
  ⟦⟧v-naturality' ⋆ p = 
    refl
  ⟦⟧v-naturality' {Γ} {Γ'} {Γ''} {σ ⇀ τ} {e} {e'} {f} (fn t) p = λ {Γ'''} q → 
    ≈T-fundamental-lemma t (≈e-extend-lem (λ {σ'} x → ⟦⟧-rename-comp-lem' {Γ'} {Γ''} {Γ'''} {σ'} (p x)) q)


  -- Interpretation maps are natural for substitutions 
  env-extend-subst-lem-v : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (t : Γ ⊢v σ) 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈_ {Γ''} {σ} 
      (⟦ t ⟧v (sub-to-env s e)) 
      (⟦ subst-v s t ⟧v e')

  env-extend-subst-lem-p : 
    {Γ Γ' Γ'' : Ctx} 
    {σ : Ty} 
    {s : Sub Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (t : Γ ⊢p σ) 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈T_ {Γ''} {σ} {λ {Γ} → _≈_ {Γ} {σ}} 
      (⟦ t ⟧p (sub-to-env s e)) 
      (⟦ subst-p s t ⟧p e')

  *-env-extend-subst-lem : 
    {Γ Γ' Γ'' : Ctx} 
    {σ σ' : Ty} 
    {s : Sub Γ Γ'} 
    {e e' : Env Γ' Γ''} 
    → (u : Γ :: σ' ⊢p σ) 
    → (d d' : T ⟦ σ' ⟧ Γ'') 
    → _≈T_ {Γ''} {σ'} {λ {Γ} → _≈_ {Γ} {σ'}} d d' 
    → _≈e_ {Γ'} {Γ''} e e' 
    → _≈T_ {Γ''} {σ} {λ {Γ} → _≈_ {Γ} {σ}}
      (* {(Env-Denot Γ) ⊗ (Denot σ')} 
        (λ v → ⟦ u ⟧p (env-extend (fst v) (snd v))) 
        {Γ''} 
        (t-r {Env-Denot Γ} {Denot σ'} {Γ''} ((sub-to-env s e) , d)))
      (* {(Env-Denot Γ') ⊗ (Denot σ')} 
        (λ v → ⟦ subst-p (lift s) u ⟧p (env-extend (fst v) (snd v))) 
        {Γ''} 
        (t-r {Env-Denot Γ'} {Denot σ'} {Γ''} ((λ {σ} → e' {σ}) , d')))

  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} {e'} u d d' (≈T-sym p) q = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma {d = d} {d' = d'} u (≈T-sym p) (λ x → ≈-fundamental-lemma (s x) (≈e-refl q))) 
      (≈T-trans 
        (*-env-extend-subst-lem u d' d p q) 
        (≈-*-strength-fundamental-lemma {d = d} {d' = d'} (subst-p (lift s) u) (≈T-sym p) (≈e-refl (≈e-sym q)) ))
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} {e'} u .d .d'' (≈T-trans {d} {d'} {d''} p p') q = 
    ≈T-trans 
      (*-env-extend-subst-lem {s = s} u d d' p q) 
      (≈-*-strength-fundamental-lemma {d = d'} {d' = d''} (subst-p (lift s) u) p' (≈e-refl (≈e-sym q)))
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} {e'} u .(T-return d) .(T-return d') (congreturn {d} {d'} p) q = 
    ≈T-trans 
      (≈T-fundamental-lemma u (sub-to-env-lift-lem d d (≈-refl {Γ''} {σ'} p) (≈e-refl q))) 
      (env-extend-subst-lem-p {s = lift s} {e' = env-extend e' d'} u (≈e-extend-lem q p))
  *-env-extend-subst-lem u .(T-input d d'') .(T-input d' d''') (conginput {d} {d'} {d''} {d'''} p p') q = 
    conginput (*-env-extend-subst-lem u d d' p q) (*-env-extend-subst-lem u d'' d''' p' q)
  *-env-extend-subst-lem u .(T-output0 d) .(T-output0 d') (congoutput0 {d} {d'} p) q = 
    congoutput0 (*-env-extend-subst-lem u d d' p q)
  *-env-extend-subst-lem u .(T-output1 d) .(T-output1 d') (congoutput1 {d} {d'} p) q = 
    congoutput1 (*-env-extend-subst-lem u d d' p q)
  *-env-extend-subst-lem {Γ} {Γ'} {Γ''} {σ} {σ'} {s} {e} {e'} u .(T-to t d) .(T-to t' d') (congto {τ} {t} {t'} {d} {d'} p p') q = 
    congto 
      p 
      (≈T-trans 
        (≈-*-strength-fundamental-lemma {d = d} {d' = d} u (≈T-refl p') (λ x → ⟦⟧v-naturality' (s x) (≈e-refl q))) 
        (*-env-extend-subst-lem u d d' p' (≈e-monotonicity q)))

  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ} {s} (var x) p = 
    ≈-fundamental-lemma (s x) p 
  env-extend-subst-lem-v (proj₁ t) p = 
    fst (env-extend-subst-lem-v t p)
  env-extend-subst-lem-v (proj₂ t) p = 
    snd (env-extend-subst-lem-v t p)
  env-extend-subst-lem-v (pair t u) p = 
    (env-extend-subst-lem-v t p) , (env-extend-subst-lem-v u p)
  env-extend-subst-lem-v ⋆ p = 
    refl
  env-extend-subst-lem-v {Γ} {Γ'} {Γ''} {σ ⇀ τ} {s} {e} {e'} (fn t) p = λ {Γ'''} {h} {d} {d'} q → 
    ≈T-trans 
      (≈T-fundamental-lemma 
        t 
        (≈e-trans 
          {e = env-extend (λ {σ} x' → ⟦⟧-rename {σ} h (⟦ s x' ⟧v e)) d} 
          (≈e-extend-lem (λ x → ⟦⟧v-naturality' (s x) (≈e-refl p)) (≈-refl {Γ'''} {σ} q)) 
          (sub-to-env-lift-lem {e = env-rename h e} {e' = env-rename h e} d d (≈-refl {Γ'''} {σ} q) (≈e-monotonicity (≈e-refl p))))) 
      (env-extend-subst-lem-p 
        {s = lift s} 
        {e = env-extend (env-rename h e) d} 
        {e' = env-extend (env-rename h e') d'} 
        t 
        (≈e-extend-lem (≈e-monotonicity p) q))
  env-extend-subst-lem-p (return t) p = 
    congreturn (env-extend-subst-lem-v t p)
  env-extend-subst-lem-p {Γ} {Γ'} {Γ''} {σ} {s} {e} {e'} (t to u) p = 
    *-env-extend-subst-lem u (⟦ t ⟧p (λ x → ⟦ s x ⟧v e)) (⟦ subst-p s t ⟧p e') (env-extend-subst-lem-p t p) p
  env-extend-subst-lem-p (app t u) p = 
    env-extend-subst-lem-v t p (env-extend-subst-lem-v u p)
  env-extend-subst-lem-p (input[ t , u ]) p = 
    conginput (env-extend-subst-lem-p t p) (env-extend-subst-lem-p u p)
  env-extend-subst-lem-p (output0[ t ]) p = 
    congoutput0 (env-extend-subst-lem-p t p) 
  env-extend-subst-lem-p (output1[ t ]) p = 
    congoutput1 (env-extend-subst-lem-p t p) 

  **-strength-lem' : 
    {Γ Γ' : Ctx} 
    {σ σ' τ : Ty} 
    {e e' : Env Γ Γ'} 
    {t : Γ :: τ ⊢p σ} 
    → (d d' : T ⟦ τ ⟧ Γ') 
    → (d'' : ⟦ σ' ⟧ Γ') 
    → _≈T_ {Γ'} {τ} {λ {Γ} → _≈_ {Γ} {τ}} d d' 
    → _≈_ {Γ'} {σ'} d'' d'' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}}
      (* (λ v → ⟦ t ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v))) 
         {Γ'}
         (t-r {Env-Denot Γ} {Denot τ} {Γ'} (e , d)))
      (* (λ v → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ t) ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v)))
         {Γ'}
         (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ'} (env-extend e' d'' , d')))

  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} d d' d'' (≈T-sym p) q r = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma t (≈T-sym p) (≈e-refl r)) 
      (≈T-trans 
        (**-strength-lem' {t = t} d' d d'' p q r) 
        (≈-*-strength-fundamental-lemma (⊢p-rename exchange (⊢p-rename wk₁ t)) (≈T-sym p) (≈e-extend-lem (≈e-refl (≈e-sym r)) q)))
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .d .d'' d''' (≈T-trans {d} {d'} {d''} p p') q r = 
    ≈T-trans 
      (**-strength-lem' {t = t} d d' d''' p q r) 
      (≈-*-strength-fundamental-lemma (⊢p-rename exchange (⊢p-rename wk₁ t)) p' (≈e-extend-lem (≈e-refl (≈e-sym r)) q))
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .(T-return d) .(T-return d') d'' (congreturn {d} {d'} p) q r = 
    ≈T-trans 
      (≈T-fundamental-lemma t (λ {σ'} x → env-extend-exchange-lem {Γ} {Γ'} {σ'} {τ} {ρ} {d'' = d''} p r x)) 
      (≈T-trans 
        (≈T-trans 
          (≈T-fundamental-lemma 
            t 
            (λ x → 
              ≈e-extend-lem 
                (≈e-extend-lem (≈e-refl (≈e-sym r)) q) 
                (≈-refl {Γ'} {ρ} (≈-sym {Γ'} {ρ} p)) 
                (exchange (Tl x)))) 
          (rename-env-lem-p 
            {f = wk₁} 
            {e = (λ x → env-extend (env-extend e' d'') d' (exchange x))} 
            {e' = (λ x → env-extend (env-extend e' d'') d' (exchange x))} 
            t 
            (λ x → ≈e-extend-lem (≈e-extend-lem (≈e-refl (≈e-sym r)) q) (≈-refl {Γ'} {ρ} (≈-sym {Γ'} {ρ} p)) (exchange x)))) 
        (rename-env-lem-p 
         {e = env-extend (env-extend e' d'') d'} 
         {e' = env-extend (env-extend e' d'') d'} 
         (⊢p-rename wk₁ t) 
         (≈e-extend-lem 
           (≈e-extend-lem (≈e-refl (≈e-sym r)) q) 
           (≈-refl {Γ'} {ρ} (≈-sym {Γ'} {ρ} p)))))
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .(T-input d d') .(T-input d'' d''') d'''' (conginput {d} {d''} {d'} {d'''} p p') q r = 
    conginput (**-strength-lem' {t = t} d d'' d'''' p q r) (**-strength-lem' {t = t} d' d''' d'''' p' q r)
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .(T-output0 d) .(T-output0 d'') d'''' (congoutput0 {d} {d''} p) q r = 
    congoutput0 (**-strength-lem' {t = t} d d'' d'''' p q r)
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .(T-output1 d) .(T-output1 d'') d'''' (congoutput1 {d} {d''} p) q r = 
    congoutput1 (**-strength-lem' {t = t} d d'' d'''' p q r)
  **-strength-lem' {Γ} {Γ'} {σ} {τ} {ρ} {e} {e'} {t} .(T-to u d) .(T-to u' d') d'' (congto {τ'} {u} {u'} {d} {d'} p p') q r = 
    congto p 
      (≈T-trans 
        (**-strength-lem' {t = t} d d' (⟦⟧-rename {τ} wk₁ d'') p' (≈-monotonicity {Γ'} {Γ' :: τ'} {τ} {wk₁} q) (≈e-monotonicity r)) 
        (≈-*-strength-fundamental-lemma 
          {e = env-extend (env-rename wk₁ e') (⟦⟧-rename {τ} wk₁ d'')} 
          {e' = env-rename wk₁ (env-extend e' d'')} 
          {d = d'} 
          {d' = d'} 
          (⊢p-rename exchange (⊢p-rename (λ {σ'} → Tl) t)) 
          (≈T-refl {Γ' :: τ'} {ρ} (≈T-sym p')) 
          (env-extend-naturality q (≈e-refl (≈e-sym r)))))


  **-strength-lem : 
    {Γ Γ' : Ctx} 
    {σ σ' τ : Ty} 
    {e e' : Env Γ Γ'} 
    {u : Γ :: σ' ⊢p τ} 
    {v : Γ :: τ ⊢p σ}  
    → (d d' : T ⟦ σ' ⟧ Γ') 
    → _≈T_ {Γ'} {σ'} {λ {Γ} → _≈_ {Γ} {σ'}} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}}
      (* (λ v' → ⟦ v ⟧p (env-extend ((fst v') {_}) (snd v'))) 
        {Γ'}
        (t-r {Env-Denot Γ} {Denot τ} {Γ'}
          ((λ {σ} → e {σ}) , 
            * (λ v' → ⟦ u ⟧p (env-extend ((fst v') {_}) (snd v'))) 
              {Γ'} 
              (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e {σ}) , d))))) 
      (* (λ {Γ''} v' → 
        * (λ v0 → ⟦ ⊢p-rename exchange (⊢p-rename wk₁ v) ⟧p (env-extend ((fst v0) {_}) (snd v0))) 
          {Γ''}
          (t-r {Env-Denot (Γ :: σ')} {Denot τ} {Γ''} ((λ {σ} → env-extend ((fst v') {_}) (snd v') {σ}) , ⟦ u ⟧p (env-extend ((fst v') {_}) (snd v'))))) 
        {Γ'}
        (t-r {Env-Denot Γ} {Denot σ'} {Γ'} ((λ {σ} → e' {σ}) , d')))

  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} d d' (≈T-sym p) q = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma v (≈-*-strength-fundamental-lemma u (≈T-sym p) (≈e-refl q)) (≈e-refl q)) 
      (≈T-trans 
        (**-strength-lem {u = u} {v = v} d' d p q) 
        (*≈-*-strength-fundamental-lemma {t = ⊢p-rename exchange (⊢p-rename wk₁ v)} {u = u} (≈T-sym p) (≈e-refl (≈e-sym q))))
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .d .d'' (≈T-trans {d} {d'} {d''} p p') q = 
    ≈T-trans 
      (**-strength-lem {u = u} {v = v} d d' p q) 
      (*≈-*-strength-fundamental-lemma {t = ⊢p-rename exchange (⊢p-rename wk₁ v)} {u = u} p' (≈e-refl (≈e-sym q)))
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .(T-return d) .(T-return d') (congreturn {d} {d'} p) q = 
      **-strength-lem' 
        {t = v} 
        (⟦ u ⟧p (env-extend e d)) 
        (⟦ u ⟧p (env-extend e' d')) 
        d' 
        (≈T-fundamental-lemma u (≈e-extend-lem q p)) 
        (≈-refl {Γ'} {σ'} (≈-sym {Γ'} {σ'} p)) 
        q
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .(T-input d d'') .(T-input d' d''') (conginput {d} {d'} {d''} {d'''} p p') q = 
    conginput (**-strength-lem {u = u} {v = v} d d' p q) (**-strength-lem {u = u} {v = v} d'' d''' p' q)
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .(T-output0 d) .(T-output0 d') (congoutput0 {d} {d'} p) q = 
    congoutput0 (**-strength-lem {u = u} {v = v} d d' p q)
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .(T-output1 d) .(T-output1 d') (congoutput1 {d} {d'} p) q = 
    congoutput1 (**-strength-lem {u = u} {v = v} d d' p q)
  **-strength-lem {Γ} {Γ'} {σ} {σ'} {τ} {e} {e'} {u} {v} .(T-to t d) .(T-to t' d') (congto {τ'} {t} {t'} {d} {d'} p p') q = 
    congto p 
      (≈T-trans 
        (≈-*-strength-fundamental-lemma 
          {d = * (λ v' → ⟦ u ⟧p (env-extend ((fst v') {_}) (snd v'))) {Γ' :: τ'} (t-r ((λ {σ} x → ⟦⟧-rename {σ} wk₁ (e x)) , d))} 
          {d' = * (λ v' → ⟦ u ⟧p (env-extend ((fst v') {_}) (snd v'))) {Γ' :: τ'} (t-r ((λ {σ} x → ⟦⟧-rename {σ} wk₁ (e x)) , d))} 
          v 
          (≈-*-strength-fundamental-lemma u (≈T-refl {Γ' :: τ'} {σ'} p') (≈e-monotonicity (≈e-refl q))) 
          (≈e-refl (≈e-monotonicity q))) 
        (**-strength-lem {e = env-rename wk₁ e} {e' = env-rename wk₁ e'} {u = u} {v = v} d d' p' (≈e-monotonicity q)))



