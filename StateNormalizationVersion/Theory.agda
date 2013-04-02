------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
------------------ Equational theory -----------------
------------------------------------------------------



open import Utils
open import Syntax
open import Substitutions
open import Presheaves
open import Renamings

module Theory where


  -- Equality proofs
  infix 4 _⊢v_≡_
  infix 4 _⊢p_≡_
  data _⊢v_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢v σ → Γ ⊢v σ → Set
  data _⊢p_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢p σ → Γ ⊢p σ → Set

  data _⊢v_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢v σ} → Γ ⊢v t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢v σ} → Γ ⊢v t ≡ u → Γ ⊢v u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢v σ} → Γ ⊢v t ≡ u → Γ ⊢v u ≡ v → Γ ⊢v t ≡ v
    -- congruence
    congpair : {Γ : Ctx} {σ₁ σ₂ : Ty} {t t' : Γ ⊢v σ₁} {u u' : Γ ⊢v σ₂} → Γ ⊢v t ≡ t' → Γ ⊢v u ≡ u' → Γ ⊢v (pair t u) ≡ pair t' u'
    congproj₁ : {Γ : Ctx} {σ₁ σ₂ : Ty} {t t' : Γ ⊢v σ₁ ∧ σ₂} → Γ ⊢v t ≡ t' → Γ ⊢v proj₁ t ≡ proj₁ t' 
    congproj₂ : {Γ : Ctx} {σ₁ σ₂ : Ty} {t t' : Γ ⊢v σ₁ ∧ σ₂} → Γ ⊢v t ≡ t' → Γ ⊢v proj₂ t ≡ proj₂ t'
    congfn : {Γ : Ctx} {σ τ : Ty} {t t' : Γ :: σ ⊢p τ} → Γ :: σ ⊢p t ≡ t' → Γ ⊢v fn t ≡ fn t'
    -- beta
    β×₁ : {Γ : Ctx} {σ₁ σ₂ : Ty} {t : Γ ⊢v σ₁} {u : Γ ⊢v σ₂} → Γ ⊢v proj₁ (pair t u) ≡ t
    β×₂ : {Γ : Ctx} {σ₁ σ₂ : Ty} {t : Γ ⊢v σ₁} {u : Γ ⊢v σ₂} → Γ ⊢v proj₂ (pair t u) ≡ u
    -- eta
    η⋆ : {Γ : Ctx} {t :  Γ ⊢v unit} → Γ ⊢v t ≡ ⋆
    η× : {Γ : Ctx} {σ₁ σ₂ : Ty} {t : Γ ⊢v σ₁ ∧ σ₂} → Γ ⊢v t ≡ (pair (proj₁ t) (proj₂ t))
    η⇀ : {Γ : Ctx} {σ τ : Ty} {t : Γ ⊢v σ ⇀ τ} → Γ ⊢v fn (app ((⊢v-rename wk₁ t)) (var Hd)) ≡ t

  data _⊢p_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢p σ} → Γ ⊢p t ≡ u → Γ ⊢p u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢p σ} → Γ ⊢p t ≡ u → Γ ⊢p u ≡ v → Γ ⊢p t ≡ v
    -- congruence
    congapp : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢v σ ⇀ τ} {u u' : Γ ⊢v σ} → Γ ⊢v t ≡ t' → Γ ⊢v u ≡ u' → Γ ⊢p app t u ≡ app t' u'
    congto : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢p σ} {u u' : Γ :: σ ⊢p τ} → Γ ⊢p t ≡ t' → Γ :: σ ⊢p u ≡ u' → Γ ⊢p (t to u) ≡ (t' to u')
    congreturn : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢v σ} → Γ ⊢v t ≡ t' → Γ ⊢p (return t) ≡ (return t')
    conglookup : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p u ≡ u' → Γ ⊢p lookup t u ≡ lookup t' u'
    congupdate0 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p update0 t ≡ update0 t'
    congupdate1 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p update1 t ≡ update1 t'
    -- beta
    β⇀ : {Γ : Ctx} {σ τ : Ty} {t : Γ :: σ ⊢p τ} {u : Γ ⊢v σ} → Γ ⊢p subst-p (ext-subst id-subst u) t ≡ (app (fn t) u)
    βto : {Γ : Ctx} {σ τ : Ty} {t : Γ :: σ ⊢p τ} {u : Γ ⊢v σ} → Γ ⊢p ((return u) to t) ≡ subst-p (ext-subst id-subst u) t
    -- eta
    ηto : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p t ≡ (t to return (var Hd))
    -- associativity
    assocto : {Γ : Ctx} {σ τ ρ : Ty} {t : Γ ⊢p σ} {u : Γ :: σ ⊢p τ} {v : Γ :: τ ⊢p ρ} → Γ ⊢p (t to u) to v ≡ (t to (u to ⊢p-rename exchange (⊢p-rename wk₁ v)))
    -- to-op
    lookupto : {Γ : Ctx} {σ τ : Ty} {t u : Γ ⊢p σ} {v : Γ :: σ ⊢p τ} → Γ ⊢p (lookup t u) to v ≡ lookup (t to v) (u to v)
    update0to : {Γ : Ctx} {σ τ : Ty} {t : Γ ⊢p σ} {u : Γ :: σ ⊢p τ} → Γ ⊢p (update0 t) to u ≡ update0 (t to u)
    update1to : {Γ : Ctx} {σ τ : Ty} {t : Γ ⊢p σ} {u : Γ :: σ ⊢p τ} → Γ ⊢p (update1 t) to u ≡ update1 (t to u)
    -- effect theory of global state
    state-ax1 : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p t ≡ lookup (update0 t) (update1 t)
    state-ax2 : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢p σ} → Γ ⊢p update0 (lookup t u) ≡ update0 t
    state-ax3 : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢p σ} → Γ ⊢p update1 (lookup t u) ≡ update1 u
    state-ax4 : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p update0 (update0 t) ≡ update0 t
    state-ax5 : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p update0 (update1 t) ≡ update1 t
    state-ax6 : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p update1 (update0 t) ≡ update0 t
    state-ax7 : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p update1 (update1 t) ≡ update1 t


  -- Equational theories of normal and atomic terms
  infix 4 _⊢av_≡_
  infix 4 _⊢ap_≡_
  infix 4 _⊢nv_≡_
  infix 4 _⊢np_≡_


  data _⊢nv_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢nv σ → Γ ⊢nv σ → Set
  data _⊢np_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢np σ → Γ ⊢np σ → Set
  data _⊢np'_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢np' σ → Γ ⊢np' σ → Set
  data _⊢ap_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢ap σ → Γ ⊢ap σ → Set

  _⊢av_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢av σ → Γ ⊢av σ → Set
  Γ ⊢av t ≡ u = t ≅ u 

  data _⊢nv_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢nv σ} → Γ ⊢nv t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢nv σ} → Γ ⊢nv t ≡ u → Γ ⊢nv u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢nv σ} → Γ ⊢nv t ≡ u → Γ ⊢nv u ≡ v → Γ ⊢nv t ≡ v
    -- congruence
    congpair : {Γ : Ctx} {σ₁ σ₂ : Ty} {t t' : Γ ⊢nv σ₁} {u u' : Γ ⊢nv σ₂} → Γ ⊢nv t ≡ t' → Γ ⊢nv u ≡ u' → Γ ⊢nv (pairNV t u) ≡ (pairNV t' u')
    congfn : {Γ : Ctx} {σ τ : Ty} {t u : Γ :: σ ⊢np τ} → Γ :: σ ⊢np t ≡ u → Γ ⊢nv fnNV t ≡ fnNV u

  data _⊢np'_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢np' σ} → Γ ⊢np' t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢np' σ} → Γ ⊢np' t ≡ u → Γ ⊢np' u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢np' σ} → Γ ⊢np' t ≡ u → Γ ⊢np' u ≡ v → Γ ⊢np' t ≡ v
    -- congruence
    congreturn : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢nv σ} → Γ ⊢nv t ≡ u → Γ ⊢np' (returnNP t) ≡ (returnNP u)
    congto : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢ap σ} {u u' : Γ :: σ ⊢np τ} → Γ ⊢ap t ≡ t' → Γ :: σ ⊢np u ≡ u' → Γ ⊢np' (toNP t u) ≡ (toNP t' u')

  data _⊢np_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢np σ} → Γ ⊢np t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢np σ} → Γ ⊢np t ≡ u → Γ ⊢np u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢np σ} → Γ ⊢np t ≡ u → Γ ⊢np u ≡ v → Γ ⊢np t ≡ v
    -- congruence
    conglookup : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢np' σ} → Γ ⊢np' t ≡ t' → Γ ⊢np' u ≡ u' → Γ ⊢np lookupNP[ t , u ] ≡ lookupNP[ t' , u' ]
    conglookup0 : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢np' σ} → Γ ⊢np' t ≡ t' → Γ ⊢np' u ≡ u' → Γ ⊢np lookupNP[ t ,update0NP[ u ]] ≡ lookupNP[ t' ,update0NP[ u' ]]
    conglookup1 : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢np' σ} → Γ ⊢np' t ≡ t' → Γ ⊢np' u ≡ u' → Γ ⊢np lookupNP[update1NP[ t ], u ] ≡ lookupNP[update1NP[ t' ], u' ]
    conglookup10 : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢np' σ} → Γ ⊢np' t ≡ t' → Γ ⊢np' u ≡ u' → Γ ⊢np lookupNP[update1NP[ t ],update0NP[ u ]] ≡ lookupNP[update1NP[ t' ],update0NP[ u' ]]

  data _⊢ap_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢ap σ} → Γ ⊢ap t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢ap σ} → Γ ⊢ap t ≡ u → Γ ⊢ap u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢ap σ} → Γ ⊢ap t ≡ u → Γ ⊢ap u ≡ v → Γ ⊢ap t ≡ v
    -- congruence
    congapp : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢av σ ⇀ τ} {u u' : Γ ⊢nv σ} → Γ ⊢av t ≡ t' → Γ ⊢nv u ≡ u' → Γ ⊢ap appAP t u ≡ appAP t' u'
