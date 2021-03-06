------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
----------------- Equational Theory ------------------
------------------------------------------------------


open import Utils
open import Syntax
open import Substitutions
open import Presheaves
open import Renamings

module Theory where


  -- Equational theory for values and producers
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
    conginput : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p u ≡ u' → Γ ⊢p input[ t , u ] ≡ input[ t' , u' ]
    congoutput0 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p output0[ t ] ≡ output0[ t' ]
    congoutput1 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢p σ} → Γ ⊢p t ≡ t' → Γ ⊢p output1[ t ] ≡ output1[ t' ]
    -- beta
    β⇀ : {Γ : Ctx} {σ τ : Ty} {t : Γ :: σ ⊢p τ} {u : Γ ⊢v σ} → Γ ⊢p subst-p (ext-subst id-subst u) t ≡ (app (fn t) u)
    βto : {Γ : Ctx} {σ τ : Ty} {t : Γ :: σ ⊢p τ} {u : Γ ⊢v σ} → Γ ⊢p ((return u) to t) ≡ subst-p (ext-subst id-subst u) t
    -- eta
    ηto : {Γ : Ctx} {σ : Ty} {t : Γ ⊢p σ} → Γ ⊢p t ≡ (t to return (var Hd))
    -- associativity
    assocto : {Γ : Ctx} {σ τ ρ : Ty} {t : Γ ⊢p σ} {u : Γ :: σ ⊢p τ} {v : Γ :: τ ⊢p ρ} → Γ ⊢p (t to u) to v ≡ (t to (u to ⊢p-rename exchange (⊢p-rename wk₁ v)))
    -- to-op
    inputto : {Γ : Ctx} {σ τ : Ty} {t u : Γ ⊢p σ} {v : Γ :: σ ⊢p τ} → Γ ⊢p (input[ t , u ]) to v ≡ input[ (t to v) , (u to v) ]
    output0to : {Γ : Ctx} {σ τ : Ty} {t : Γ ⊢p σ} {v : Γ :: σ ⊢p τ} → Γ ⊢p (output0[ t ]) to v ≡ output0[ (t to v) ]
    output1to : {Γ : Ctx} {σ τ : Ty} {t : Γ ⊢p σ} {v : Γ :: σ ⊢p τ} → Γ ⊢p (output1[ t ]) to v ≡ output1[ (t to v) ]

  -- Equal value terms are equivalent
  ≅2≡-v : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢v σ} 
    → t ≅ t' 
    → Γ ⊢v t ≡ t'

  ≅2≡-v refl = ≡-refl


  -- Equal producer terms are equivalent
  ≅2≡-p : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢p σ} 
    → t ≅ t' 
    → Γ ⊢p t ≡ t'

  ≅2≡-p refl = ≡-refl


  -- Equational reasoning for the equational theory
  _≡v〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢v σ) 
    {y z : Γ ⊢v σ} 
    → (Γ ⊢v x ≡ y) 
    → (Γ ⊢v y ≡ z) 
    → (Γ ⊢v x ≡ z)

  x ≡v〈 p 〉 q = ≡-trans p q

  _≡p〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢p σ) 
    {y z : Γ ⊢p σ} 
    → (Γ ⊢p x ≡ y) 
    → (Γ ⊢p y ≡ z) 
    → (Γ ⊢p x ≡ z)

  x ≡p〈 p 〉 q = ≡-trans p q

  _v∎ : {Γ : Ctx} {σ : Ty} (x : Γ ⊢v σ) → Γ ⊢v x ≡ x
  x v∎ = ≡-refl

  _p∎ : {Γ : Ctx} {σ : Ty} (x : Γ ⊢p σ) → Γ ⊢p x ≡ x
  x p∎ = ≡-refl

  infix  2 _v∎
  infixr 2 _≡v〈_〉_
  infix  2 _p∎
  infixr 2 _≡p〈_〉_



  -- Equational theory of normal and atomic terms
  infix 4 _⊢av_≡_
  infix 4 _⊢ap_≡_
  infix 4 _⊢nv_≡_
  infix 4 _⊢np_≡_


  data _⊢nv_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢nv σ → Γ ⊢nv σ → Set
  data _⊢np_≡_ : (Γ : Ctx) → {σ : Ty} → Γ ⊢np σ → Γ ⊢np σ → Set
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


  data _⊢np_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢np σ} → Γ ⊢np t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢np σ} → Γ ⊢np t ≡ u → Γ ⊢np u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢np σ} → Γ ⊢np t ≡ u → Γ ⊢np u ≡ v → Γ ⊢np t ≡ v
    -- congruence
    congreturn : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢nv σ} → Γ ⊢nv t ≡ u → Γ ⊢np (returnNP t) ≡ (returnNP u)
    congto : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢ap σ} {u u' : Γ :: σ ⊢np τ} → Γ ⊢ap t ≡ t' → Γ :: σ ⊢np u ≡ u' → Γ ⊢np (toNP t u) ≡ (toNP t' u')
    conginput : {Γ : Ctx} {σ : Ty} {t t' u u' : Γ ⊢np σ} → Γ ⊢np t ≡ t' → Γ ⊢np u ≡ u' → Γ ⊢np inputNP[ t , u ] ≡ inputNP[ t' , u' ]
    congoutput0 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢np σ} → Γ ⊢np t ≡ t' → Γ ⊢np output0NP[ t ] ≡ output0NP[ t' ]
    congoutput1 : {Γ : Ctx} {σ : Ty} {t t' : Γ ⊢np σ} → Γ ⊢np t ≡ t' → Γ ⊢np output1NP[ t ] ≡ output1NP[ t' ]


  data _⊢ap_≡_ where
    -- equivalence
    ≡-refl : {Γ : Ctx} {σ : Ty} {t : Γ ⊢ap σ} → Γ ⊢ap t ≡ t
    ≡-sym : {Γ : Ctx} {σ : Ty} {t u : Γ ⊢ap σ} → Γ ⊢ap t ≡ u → Γ ⊢ap u ≡ t
    ≡-trans : {Γ : Ctx} {σ : Ty} {t u v : Γ ⊢ap σ} → Γ ⊢ap t ≡ u → Γ ⊢ap u ≡ v → Γ ⊢ap t ≡ v
    -- congruence
    congapp : {Γ : Ctx} {σ τ : Ty} {t t' : Γ ⊢av σ ⇀ τ} {u u' : Γ ⊢nv σ} → Γ ⊢av t ≡ t' → Γ ⊢nv u ≡ u' → Γ ⊢ap appAP t u ≡ appAP t' u'


  -- Equational reasoning for the equational theory
  _≡nv〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢nv σ) 
    {y z : Γ ⊢nv σ} 
    → (Γ ⊢nv x ≡ y) 
    → (Γ ⊢nv y ≡ z) 
    → (Γ ⊢nv x ≡ z)

  x ≡nv〈 p 〉 q = ≡-trans p q

  _≡np〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢np σ) 
    {y z : Γ ⊢np σ} 
    → (Γ ⊢np x ≡ y) 
    → (Γ ⊢np y ≡ z) 
    → (Γ ⊢np x ≡ z)

  x ≡np〈 p 〉 q = ≡-trans p q

  _≡av〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢av σ) 
    {y z : Γ ⊢av σ} 
    → (Γ ⊢av x ≡ y) 
    → (Γ ⊢av y ≡ z) 
    → (Γ ⊢av x ≡ z)

  x ≡av〈 p 〉 q = trans p q

  _≡ap〈_〉_ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢ap σ) 
    {y z : Γ ⊢ap σ} 
    → (Γ ⊢ap x ≡ y) 
    → (Γ ⊢ap y ≡ z) 
    → (Γ ⊢ap x ≡ z)

  x ≡ap〈 p 〉 q = ≡-trans p q

  _nv∎ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢nv σ) 
    → Γ ⊢nv x ≡ x

  x nv∎ = ≡-refl

  _np∎ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢np σ) 
    → Γ ⊢np x ≡ x

  x np∎ = ≡-refl

  _av∎ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢av σ) 
    → Γ ⊢av x ≡ x

  x av∎ = refl

  _ap∎ : 
    {Γ : Ctx} 
    {σ : Ty} 
    (x : Γ ⊢ap σ) 
    → Γ ⊢ap x ≡ x

  x ap∎ = ≡-refl


  infix  2 _nv∎
  infixr 2 _≡nv〈_〉_
  infix  2 _np∎
  infixr 2 _≡np〈_〉_
  infix  2 _av∎
  infixr 2 _≡av〈_〉_
  infix  2 _ap∎
  infixr 2 _≡ap〈_〉_



  -- Equal normal value terms are equivalent
  ≅2≡-nv : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢nv σ} 
    → t ≅ t' 
    → Γ ⊢nv t ≡ t'

  ≅2≡-nv refl = ≡-refl


  -- Equal normal producer terms are equivalent
  ≅2≡-np : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢np σ} 
    → t ≅ t' 
    → Γ ⊢np t ≡ t'

  ≅2≡-np refl = ≡-refl


  -- Equal atomic producer terms are equivalent
  ≅2≡-ap : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t t' : Γ ⊢ap σ} 
    → t ≅ t' 
    → Γ ⊢ap t ≡ t'

  ≅2≡-ap refl = ≡-refl


  -- Congruence of normal and atomic forms embeddings
  ⊢nv-embed-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : Γ ⊢nv σ} 
    → Γ ⊢nv t ≡ u 
    → Γ ⊢v (⊢nv-embed t) ≡ (⊢nv-embed u)

  ⊢np-embed-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : Γ ⊢np σ} 
    → Γ ⊢np t ≡ u 
    → Γ ⊢p (⊢np-embed t) ≡ (⊢np-embed u)

  ⊢ap-embed-lem : 
    {Γ : Ctx} 
    {σ : Ty} 
    {t u : Γ ⊢ap σ} 
    → Γ ⊢ap t ≡ u 
    → Γ ⊢p (⊢ap-embed t) ≡ (⊢ap-embed u)

  ⊢nv-embed-lem {Γ} {σ} {.t} {t} ≡-refl = 
      ⊢nv-embed t 
    v∎
  ⊢nv-embed-lem {Γ} {σ} {t} {u} (≡-sym p) = 
      ⊢nv-embed t
    ≡v〈 ≡-sym (⊢nv-embed-lem p) 〉
      ⊢nv-embed u 
    v∎
  ⊢nv-embed-lem {Γ} {σ} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢nv-embed t
    ≡v〈 ⊢nv-embed-lem p 〉
      ⊢nv-embed u
    ≡v〈 ⊢nv-embed-lem q 〉
      ⊢nv-embed v 
    v∎
  ⊢nv-embed-lem {Γ} {σ₁ ∧ σ₂} {pairNV t u} {pairNV t' u'} (congpair p q) = 
      pair (⊢nv-embed t) (⊢nv-embed u)
    ≡v〈 congpair (⊢nv-embed-lem p) (⊢nv-embed-lem q) 〉
      pair (⊢nv-embed t') (⊢nv-embed u')
    v∎
  ⊢nv-embed-lem {Γ} {σ ⇀ τ} {fnNV t} {fnNV u} (congfn p) = 
      fn (⊢np-embed t)
    ≡v〈 congfn (⊢np-embed-lem p) 〉
      fn (⊢np-embed u)
    v∎

  ⊢np-embed-lem {Γ} {σ} {.t} {t} ≡-refl = 
      ⊢np-embed t
    p∎
  ⊢np-embed-lem {Γ} {σ} {t} {u} (≡-sym p) = 
      ⊢np-embed t
    ≡p〈 ≡-sym (⊢np-embed-lem p) 〉
      ⊢np-embed u
    p∎
  ⊢np-embed-lem {Γ} {σ} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢np-embed t
    ≡p〈 ⊢np-embed-lem p 〉
      ⊢np-embed u 
    ≡p〈 ⊢np-embed-lem q 〉
      ⊢np-embed v
    p∎
  ⊢np-embed-lem {Γ} {σ} {returnNP t} {returnNP u} (congreturn p) = 
      return (⊢nv-embed t)
    ≡p〈 congreturn (⊢nv-embed-lem p) 〉
      return (⊢nv-embed u)
    p∎
  ⊢np-embed-lem {Γ} {σ} {toNP t u} {toNP t' u'} (congto p q) = 
      ⊢ap-embed t to ⊢np-embed u
    ≡p〈 congto (⊢ap-embed-lem p) (⊢np-embed-lem q) 〉
      ⊢ap-embed t' to ⊢np-embed u'
    p∎
  ⊢np-embed-lem {Γ} {σ} {inputNP[ t , u ]} {inputNP[ t' , u' ]} (conginput p q) = 
      input[ (⊢np-embed t) , (⊢np-embed u) ]
    ≡p〈 conginput (⊢np-embed-lem p) (⊢np-embed-lem q) 〉
      input[ (⊢np-embed t') , (⊢np-embed u') ]
    p∎
  ⊢np-embed-lem {Γ} {σ} {output0NP[ t ]} {output0NP[ t' ]} (congoutput0 p) = 
      output0[ (⊢np-embed t) ]
    ≡p〈 congoutput0 (⊢np-embed-lem p) 〉
      output0[ (⊢np-embed t') ]
    p∎
  ⊢np-embed-lem {Γ} {σ} {output1NP[ t ]} {output1NP[ t' ]} (congoutput1 p) = 
      output1[ (⊢np-embed t) ]
    ≡p〈 congoutput1 (⊢np-embed-lem p) 〉
      output1[ (⊢np-embed t') ]
    p∎


  ⊢ap-embed-lem {Γ} {σ} {.t} {t} ≡-refl = 
      ⊢ap-embed t
    p∎
  ⊢ap-embed-lem {Γ} {σ} {t} {u} (≡-sym p) = 
      ⊢ap-embed t
    ≡p〈 ≡-sym (⊢ap-embed-lem p) 〉
      ⊢ap-embed u
    p∎
  ⊢ap-embed-lem {Γ} {σ} {.t} {.v} (≡-trans {.Γ} {.σ} {t} {u} {v} p q) = 
      ⊢ap-embed t
    ≡p〈 ⊢ap-embed-lem p 〉
      ⊢ap-embed u
    ≡p〈 ⊢ap-embed-lem q 〉
      ⊢ap-embed v
    p∎
  ⊢ap-embed-lem {Γ} {σ} {appAP .t u} {appAP t u'} (congapp refl q) = 
      app (⊢av-embed t) (⊢nv-embed u)
    ≡p〈 congapp ≡-refl (⊢nv-embed-lem q) 〉
      app (⊢av-embed t) (⊢nv-embed u')
    p∎
