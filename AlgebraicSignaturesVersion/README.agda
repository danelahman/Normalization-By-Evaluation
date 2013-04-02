------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
----------------------- Readme -----------------------
------------------------------------------------------
------------------------------------------------------
-- Includes NBE for simple and parametrized         --
-- algebraic signatures with equations.             --
-- Normalization uses residualizing monad and       --
-- normal forms are identified up-to equations      --
-- for the effects.                                 --
------------------------------------------------------
--------- Code tested with Agda version 2.3.1 --------
------------------------------------------------------

module README where

  -- Utilities
  -- =========

  -- Small standard library
  open import Utils


  -- The intermediate language
  -- ================

  -- Syntax of the intermediate language
  open import Syntax

  -- Equational theory of the intermediate language
  open import Theory

  -- Renamings
  open import Renamings

  -- Substitutions
  open import Substitutions


  -- Categorical notions
  -- ===================

  -- Presheaves (of values, producers, normal and atomic forms)
  open import Presheaves

  -- Residualizing monad
  open import Monad

  -- Normalization by evaluation
  -- =================

  -- NbE algorithm together with the residualizing interpretation
  open import NBE

  -- Various lemmas concerning renamings, substitutions and environments
  open import Lemmas

  -- Kripke logical relations relating syntax and residual semantics
  open import LogicalRelations

  -- Kripke logical relations (partial equivalence relations) for the residual model
  open import PartialEquivalence

  -- Lemmas about the Kripke logical relations
  open import PartialEquivalenceLemmas

  -- Soundness of interpretation (up to the Kripke logical relations)
  open import Soundness

  -- Three normalization results
  open import NormalizationResults