------------------------------------------------------
------------------- MPhil project --------------------
------------------------------------------------------
--- Computational effects, algebraic theories and ----
------------ normalization by evaluation -------------
------------------------------------------------------
----------------------- Readme -----------------------
------------------------------------------------------
-------------------- Danel Ahman ---------------------
------------------------------------------------------
------------------------------------------------------
-- Includes the extension of value and effect       --
-- theories WITHOUT EQUATIONS to FGCBV illustrated  --
-- by non-determinism deterministic choice.         --
-- This version includes soundness up to equality.  --
------------------------------------------------------
------------------------------------------------------


module README where

  -- Utilities
  -- =========

  -- Danel's standard library
  open import Utils


  -- FGCBV_eff basics
  -- ================

  -- syntax of FGCBV_eff
  open import Syntax

  -- equational theory of FGCBV_eff (without the equations from the value and effect theories)
  open import Theory

  -- context renamings
  open import Renamings

  -- parallel substitutions
  open import Substitutions


  -- Categorical notions
  -- ===================

  -- presheaves (of values, producers, normal and atomic forms)
  open import Presheaves

  -- free monad over the signature of normal producers
  open import Monad

  -- NbE for FGCBV_eff
  -- =================

  -- NbE algorithm together with the residualizing interpretation
  open import NbE

  -- various lemmas concerning renamings, substitutions and environments
  open import Lemmas

  -- Kripke logical relations for syntax and semantics, fundamental lemma
  open import LogicalRelations

  -- soundness of interpretation (up to equality) and stability of reification
  open import Soundness

  -- three normalization results
  open import NormalizationResults
