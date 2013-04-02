------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
--------------------- Soundness ----------------------
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
open import PartialEquivalenceLemmas

module Soundness where


  -- Soundness of the residualizing interpretations
  soundness-v : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (t u : Γ ⊢v σ) 
    → Γ ⊢v t ≡ u 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈_ {Γ'} {σ} 
      (⟦ t ⟧v e) 
      (⟦ u ⟧v e')

  soundness-p : 
    {Γ Γ' : Ctx} 
    {σ : Ty} 
    {e e' : Env Γ Γ'} 
    → (t u : Γ ⊢p σ) 
    → Γ ⊢p t ≡ u 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {σ} {λ {Γ} → _≈_ {Γ} {σ}} 
      (⟦ t ⟧p e) 
      (⟦ u ⟧p e')

  -- Soundness for the Kleisli extensions and strength composition
  *-strength-soundness : 
    {Γ Γ' : Ctx} 
    {σ τ : Ty} 
    {e e' : Env Γ Γ'} 
    {d d' : T ⟦ σ ⟧ Γ'} 
    → (t u : Γ :: σ ⊢p τ) 
    → Γ :: σ ⊢p t ≡ u 
    → _≈T_ {Γ'} {σ} {λ {Γ} 
    → _≈_ {Γ} {σ}} d d' 
    → _≈e_ {Γ} {Γ'} e e' 
    → _≈T_ {Γ'} {τ} {λ {Γ} → _≈_ {Γ} {τ}} 
      (* (λ v → ⟦ t ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v))) 
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e , d))) 
      (* (λ v → ⟦ u ⟧p (env-extend (λ {σ} → fst v {σ}) (snd v))) 
         {Γ'} 
         (t-r {Env-Denot Γ} {Denot σ} {Γ'} (e' , d')))

  soundness-v .u u ≡-refl q = 
    ≈-fundamental-lemma u q
  soundness-v {Γ} {Γ'} {σ} t u (≡-sym p) q = 
    ≈-sym {Γ'} {σ} (soundness-v u t p (≈e-sym q))
  soundness-v {Γ} {Γ'} {σ} t v (≡-trans {.Γ} {.σ} {.t} {u} {.v} p p') q = 
    ≈-trans {Γ'} {σ} 
      (soundness-v t u p q) 
      (soundness-v u v p' (≈e-refl (≈e-sym q)))
  soundness-v .(pair t u) .(pair t' u') (congpair {Γ} {σ₁} {σ₂} {t} {t'} {u} {u'} p p') q = 
    (soundness-v t t' p q) , (soundness-v u u' p' q)
  soundness-v .(proj₁ t) .(proj₁ t') (congproj₁ {Γ} {σ} {σ₂} {t} {t'} p) q = 
    fst (soundness-v t t' p q)
  soundness-v .(proj₂ t) .(proj₂ t') (congproj₂ {Γ} {σ₁} {σ} {t} {t'} p) q = 
    snd (soundness-v t t' p q)
  soundness-v .(fn t) .(fn t') (congfn {Γ} {σ} {τ} {t} {t'} p) q = λ r → 
    soundness-p t t' p (≈e-extend-lem (≈e-monotonicity q) r)
  soundness-v .(proj₁ (pair u u')) u (β×₁ {Γ} {σ} {σ₂} {.u} {u'}) q = 
    ≈-fundamental-lemma u q
  soundness-v .(proj₂ (pair t u)) u (β×₂ {Γ} {σ₁} {σ} {t}) q = 
    ≈-fundamental-lemma u q
  soundness-v {Γ} {Γ'} {unit} {e} {e'} t .⋆ η⋆ q with ⟦ t ⟧v e
  soundness-v {Γ} {Γ'} {unit} t .⋆ η⋆ q | ⋆ = refl
  soundness-v t .(pair (proj₁ t) (proj₂ t)) η× q = 
    ≈-fundamental-lemma t q
  soundness-v {Γ} {Γ'} {σ ⇀ τ} {e} {e'} .(fn (app (⊢v-rename (λ {σ} → Tl) u) (var Hd))) u η⇀ p = λ {Γ''} {h} {d} {d'} q → 
    ≈T-trans 
      (≈-fundamental-lemma (⊢v-rename wk₁ u) (≈e-extend-lem (≈e-monotonicity p) q) q) 
      (≈T-sym (≈T-trans 
        (⟦⟧v-naturality' {f = h} u (≈e-refl (≈e-sym p)) {h = id-ren} (≈-refl {Γ''} {σ} (≈-sym {Γ''} {σ} q))) 
        (rename-env-lem-v 
          {f = wk₁} 
          {e = env-extend (env-rename h e') d'} 
          {e' = λ x → env-extend (env-rename h e') d' x} 
          u 
          (≈e-extend-lem (≈e-monotonicity (≈e-refl (≈e-sym p))) (≈-refl {Γ''} {σ} (≈-sym {Γ''} {σ} q))) 
          {h = id-ren} 
          (≈-refl {Γ''} {σ} (≈-sym {Γ''} {σ} q)))))
  soundness-p .u u ≡-refl q = 
    ≈T-fundamental-lemma u q
  soundness-p {Γ} {Γ'} {σ} t u (≡-sym p) q = 
    ≈T-sym {Γ'} {σ} (soundness-p u t p (≈e-sym q))
  soundness-p {Γ} {Γ'} {σ} t v (≡-trans {.Γ} {.σ} {.t} {u} {.v} p p') q = 
    ≈T-trans {Γ'} {σ} 
      (soundness-p t u p q) 
      (soundness-p u v p' (≈e-refl (≈e-sym q)))
  soundness-p .(app t u) .(app t' u') (congapp {Γ} {σ'} {σ} {t} {t'} {u} {u'} p p') q = 
    soundness-v t t' p q (soundness-v u u' p' q)
  soundness-p {Γ} {Γ'} {τ} {e} {e'} .(t to u) .(t' to u') (congto {.Γ} {σ} {.τ} {t} {t'} {u} {u'} p p') q = 
    *-strength-soundness u u' p' (soundness-p t t' p q) q
  soundness-p .(return t) .(return t') (congreturn {Γ} {σ} {t} {t'} p) q = 
    congreturn (soundness-v t t' p q)
  soundness-p .(or t u) .(or t' u') (congor {Γ} {σ} {t} {t'} {u} {u'} p p') q = 
    congor (soundness-p t t' p q) (soundness-p u u' p' q)
  soundness-p .(if b then t else u) .(if b' then t' else u') (congif {Γ} {σ} {b} {b'} {t} {u} {t'} {u'} p p' p'') q = 
    congif (soundness-v b b' p q) (soundness-p t t' p' q) (soundness-p u u' p'' q)
  soundness-p .(input[ t ]) .(input[ t' ]) (conginput {Γ} {σ} {t} {t'} p) q = 
    conginput (soundness-p t t' p (≈e-extend-lem (≈e-monotonicity q) ≡-refl))
  soundness-p .(output[ b , t ]) .(output[ b' , t' ]) (congoutput {Γ} {σ} {b} {b'} {t} {t'} p p') q = 
    congoutput (soundness-v b b' p q) (soundness-p t t' p' q)
  soundness-p {Γ} {Γ'} {τ} {e} {e'} .(subst-p (ext-subst var u) t) .(app (fn t) u) (β⇀ {.Γ} {σ} {.τ} {t} {u}) q = 
    ≈T-trans 
      (≈T-sym (env-extend-subst-lem-p {s = ext-subst id-subst u} t (≈e-sym q))) 
      (≈T-fundamental-lemma 
        t 
        (≈e-trans 
          {e = λ x → ⟦ ext-subst id-subst u x ⟧v e'} 
          {e' = env-extend e' (⟦ u ⟧v e')} 
          {e'' = λ x → env-extend (env-rename id-ren e') (⟦ u ⟧v e') x} 
          (sub-to-env-ext-lem {s = id-subst} u (≈e-refl (≈e-sym q))) 
          (≈e-extend-lem 
          (λ {σ} x → ≈-sym {Γ'} {σ} (⟦⟧-rename-id-lem' {σ} (e' x) (e' x) (≈-refl {Γ'} {σ} (≈-sym {Γ'} {σ} (q x))))) 
          (≈-fundamental-lemma u (≈e-refl (≈e-sym q))))))
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .(return u to t) .(subst-p (ext-subst var u) t) (βto {.Γ} {σ'} {.σ} {t} {u}) q = 
    ≈T-trans 
      (≈T-fundamental-lemma t (λ {σ} x → ≈-sym {Γ'} {σ} (sub-to-env-ext-lem u (≈e-refl q) x))) 
      (env-extend-subst-lem-p t q)
  soundness-p {Γ} {Γ'} {σ} {e} {e'} t .(t to return (var Hd)) ηto q = 
    *-strength-leaf-lem (⟦ t ⟧p e) (⟦ t ⟧p e') (≈T-fundamental-lemma t q) (≈e-sym q)
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .((t to u) to v) .(t to (u to ⊢p-rename exchange (⊢p-rename (λ {σ} → Tl) v))) (assocto {.Γ} {σ'} {τ} {.σ} {t} {u} {v}) q = 
    **-strength-lem {u = u} {v = v} (⟦ t ⟧p e) (⟦ t ⟧p e') (≈T-fundamental-lemma t q) q
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .(or t u to v) .(or (t to v) (u to v)) (orto {.Γ} {σ'} {.σ} {t} {u} {v}) q = 
    congor 
      (≈-*-strength-fundamental-lemma {d = ⟦ t ⟧p e} {d' = ⟦ t ⟧p e'} v (≈T-fundamental-lemma t q) q) 
      (≈-*-strength-fundamental-lemma {d = ⟦ u ⟧p e} {d' = ⟦ u ⟧p e'} v (≈T-fundamental-lemma u q) q)
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .(if b then t else u to v) .(if b then (t to v) else (u to v)) (ifto {.Γ} {σ'} {.σ} {b} {t} {u} {v}) q = 
    congif 
      (≈-fundamental-lemma b q) 
      (≈-*-strength-fundamental-lemma {d = ⟦ t ⟧p e} {d' = ⟦ t ⟧p e'} v (≈T-fundamental-lemma t q) q) 
      (≈-*-strength-fundamental-lemma {d = ⟦ u ⟧p e} {d' = ⟦ u ⟧p e'} v (≈T-fundamental-lemma u q) q)
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .(input[ t ] to u) .(input[ (t to ⊢p-rename exchange (⊢p-rename wk₁ u)) ]) (inputto {.Γ} {σ'} {.σ} {t} {u}) q = 
    conginput 
      (**-strength-lem' 
        {e = env-rename wk₁ e} 
        {e' = env-rename wk₁ e'} 
        {t = u} 
        (⟦ t ⟧p (env-extend (λ {σ₁} x → ⟦⟧-rename {σ₁} wk₁ (e x)) (bit2NV (varAV Hd)))) 
        (⟦ t ⟧p (env-extend (λ {σ₁} x → ⟦⟧-rename {σ₁} wk₁ (e' x)) (bit2NV (varAV Hd)))) 
        (bit2NV (varAV Hd)) 
        (≈T-fundamental-lemma t (≈e-extend-lem (≈e-monotonicity q) ≡-refl)) 
        ≡-refl 
        (≈e-monotonicity q))
  soundness-p {Γ} {Γ'} {σ} {e} {e'} .(output[ b , t ] to u) .(output[ b , (t to u) ]) (outputto {.Γ} {σ'} {.σ} {b} {t} {u}) q = 
    congoutput 
      (≈-fundamental-lemma b q) 
      (≈-*-strength-fundamental-lemma {d = ⟦ t ⟧p e} {d' = ⟦ t ⟧p e'} u (≈T-fundamental-lemma t q) q) 
  soundness-p .(or u u) u or-idempotency q = 
    or-idempotency (≈T-fundamental-lemma u q) (≈T-fundamental-lemma u q)
  soundness-p .(or t u) (or u t) or-commutativity q =
    or-commutativity (≈T-fundamental-lemma t q) (≈T-fundamental-lemma u q) 
  soundness-p .(or (or t u) v) (or t (or u v)) or-associativity q = 
    or-associativity (≈T-fundamental-lemma t q) (≈T-fundamental-lemma u q) (≈T-fundamental-lemma v q)
  soundness-p (if zero then t else u) .t if-zero q = 
    if-zero (≈T-fundamental-lemma t q) (≈T-fundamental-lemma u q)
  soundness-p (if one then t else u) .u if-one q = 
    if-one (≈T-fundamental-lemma u q) (≈T-fundamental-lemma t q)

  *-strength-soundness {Γ}  {Γ'} {σ} {τ} {e} {e'} {d} {d'} t u p (≈T-sym q) r = 
    ≈T-trans 
      (≈-*-strength-fundamental-lemma t (≈T-sym q) (≈e-refl r)) 
      (≈T-trans 
        (*-strength-soundness t u p q r) 
        (≈-*-strength-fundamental-lemma u (≈T-sym q) (≈e-refl (≈e-sym r))))
  *-strength-soundness t u p (≈T-trans q q') r = 
    ≈T-trans 
      (*-strength-soundness t u p q r) 
      (≈-*-strength-fundamental-lemma u q' (≈e-refl (≈e-sym r)))
  *-strength-soundness t u p (congreturn q) r = 
    soundness-p t u p (≈e-extend-lem r q)
  *-strength-soundness t u p (congor q q') r = 
    congor (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r)
  *-strength-soundness t u p (congif q q' q'') r = 
    congif 
      q 
      (*-strength-soundness t u p q' r) 
      (*-strength-soundness t u p q'' r)
  *-strength-soundness t u p (conginput q) r = 
    conginput (*-strength-soundness t u p q (≈e-monotonicity r))
  *-strength-soundness t u p (congoutput q q') r = 
    congoutput
      q 
      (*-strength-soundness t u p q' r) 
  *-strength-soundness t u p (congto q q') r = 
    congto q (*-strength-soundness t u p q' (≈e-monotonicity r))
  *-strength-soundness t u p (or-idempotency q q') r = 
    or-idempotency (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r)
  *-strength-soundness t u p (or-commutativity q q') r = 
    or-commutativity (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r)
  *-strength-soundness t u p (or-associativity q q' q'') r = 
    or-associativity (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r) (*-strength-soundness t u p q'' r)
  *-strength-soundness t u p (if-zero q q') r = 
    if-zero (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r)
  *-strength-soundness t u p (if-one q q') r = 
    if-one (*-strength-soundness t u p q r) (*-strength-soundness t u p q' r)


  -- Renaming reflection with wk₁ moves wk₁ under reflection
  env-ext-reflect-lem : 
    {Γ : Ctx} 
    {σ σ' : Ty} 
    → (x : σ' ∈ (Γ :: σ)) 
    → (env-extend (env-rename wk₁ id-env) (reflect-v (varAV (Hd {_} {σ}))) x) ≅ id-env x

  env-ext-reflect-lem Hd = refl
  env-ext-reflect-lem (Tl x) = reflect-naturality-v (varAV x)


  -- Stability of the reflection and reification functions ("reification is the inverse of evaluation")
  reify-stability-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢nv σ) 
    → reify-v {σ} (⟦ ⊢nv-embed t ⟧v id-env) ≅ t

  reify-stability-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢np σ) 
    → reify-p {σ} (⟦ ⊢np-embed t ⟧p id-env) ≅ t

  reflect-stability-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢av σ) 
    → ⟦ ⊢av-embed t ⟧v id-env ≅ reflect-v t

  reflect-stability-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    → (t : Γ ⊢ap σ) 
    → ⟦ ⊢ap-embed t ⟧p id-env ≅ reflect-p t  

  reify-stability-v (bit2NV (varAV x)) = 
    refl
  reify-stability-v (bit2NV (proj₁AV t)) = 
    cong fst (reflect-stability-v t)
  reify-stability-v (bit2NV (proj₂AV t)) = 
    cong snd (reflect-stability-v t)
  reify-stability-v unitNV = 
    refl
  reify-stability-v zeroNV = 
    refl
  reify-stability-v oneNV = 
    refl
  reify-stability-v (pairNV t u) = 
    cong2 pairNV (reify-stability-v t) (reify-stability-v u)
  reify-stability-v {Γ} {σ ⇀ τ} (fnNV t) = 
    cong fnNV (trans (cong reify-p (cong ⟦ ⊢np-embed t ⟧p (iext (λ σ' → ext env-ext-reflect-lem)))) (reify-stability-p t))
  reify-stability-p (returnNP u) = 
    cong returnNP (reify-stability-v u)
  reify-stability-p {Γ} {σ} (toNP {σ'} {.σ} t u) = 
    trans 
      (cong 
        (λ y → 
          reify-p 
            (* {(Env-Denot Γ) ⊗ (Denot σ')}
               {Denot σ}
               (λ v → ⟦ ⊢np-embed u ⟧p (env-extend ((fst v) {_}) (snd v))) 
               {Γ} 
               (t-r {Env-Denot Γ} {Denot σ'} {Γ} ((λ {σ'} x → reflect-v (varAV x)) , y)))) 
        (reflect-stability-p t)) 
      (cong 
        (toNP t) 
        (trans 
          (cong reify-p (cong ⟦ ⊢np-embed u ⟧p (iext (λ σ'' → ext (env-ext-reflect-lem))))) 
          (reify-stability-p u)))
  reify-stability-p (orNP t u) = 
    cong2 orNP (reify-stability-p t) (reify-stability-p u)
  reify-stability-p (ifNP_then_else b t u) = 
    trans 
      (cong (λ x → reify-p (T-if x (⟦ ⊢np-embed t ⟧p id-env) (⟦ ⊢np-embed u ⟧p id-env))) (reify-stability-v b)) 
      (cong2 (λ x y → ifNP b then x else y) (reify-stability-p t) (reify-stability-p u))
  reify-stability-p (inputNP[ t ]) = 
    cong (λ x → inputNP[ x ]) (trans (cong (λ (x : Env _ _) → reify-p (⟦ ⊢np-embed t ⟧p x)) (iext (λ σ → ext (env-ext-reflect-lem)))) (reify-stability-p t))
  reify-stability-p (outputNP[ b , t ]) = 
    cong2 (λ x y → outputNP[ x , y ]) {⟦ ⊢nv-embed b ⟧v id-env} {b} (reify-stability-v b) {reify-p (⟦ ⊢np-embed t ⟧p id-env)} {t} (reify-stability-p t)

  reflect-stability-v (varAV x) = 
    refl
  reflect-stability-v (proj₁AV t) = 
    cong fst (reflect-stability-v t)
  reflect-stability-v (proj₂AV t) = 
    cong snd (reflect-stability-v t)
  reflect-stability-p {Γ} {σ} (appAP t u) = 
    trans 
      (cong 
        (λ y → y id-ren (⟦ ⊢nv-embed u ⟧v (λ {σ} x → reflect-v (varAV x)))) 
        (reflect-stability-v t)) 
      (cong 
        (λ y → T-to y (T-return (reflect-v {σ} (varAV Hd)))) 
        ((cong2 appAP (⊢av-rename-id-lem t) (reify-stability-v u))))
