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
-- theories to FGCBV_eff illustrated by theories of --
-- non-determinism and deterministic choice.        --
-- This version includes soundness up to Kripke     --
-- logical relations (i.e. the PERs)                --
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

  -- equational theory of FGCBV_eff
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

  -- Kripke logical relations for syntax and semantics
  open import LogicalRelations

  -- Kripke logical relations (i.e., the partial equivalence relations) for semantic values and the free monad
  open import PartialEquivalence

  -- lemmas about the Kripke logical relations for semantic values
  open import PartialEquivalenceLemmas

  -- soundness of interpretation (up to the Kripke logical relations)
  open import Soundness

  -- three normalization results
  open import NormalizationResults


  -- Value and effect theories
  -- =========================

  -- fourth normalization result, extension to FGCBV_eff and to normal forms, conservativity theorem
  open import Extensions
