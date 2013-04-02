------------------------------------------------------
------------- Normalization by evaluation ------------
---------------- and algebraic effects ---------------
------------------------------------------------------
----------------------- README -----------------------
------------------------------------------------------
------------------------------------------------------
--- Includes NBE algorithm for the theory of state ---
--- which uses an explicit least fixpoint taken on ---
--- a signature of strictly positive residuating   ---
--- functors Ren -> Set                            ---
------------------------------------------------------
--------- Code tested with Agda version 2.3.1 --------
------------------------------------------------------


module README where

  -- Utilities
  -- =========

  -- Little standard library
  open import Utils


  -- The intermediate language
  -- ================

  -- Syntax of the intermediate language
  open import Syntax

  -- Equational theory
  open import Theory

  -- Renamings
  open import Renamings

  -- Substitutions
  open import Substitutions


  -- Categorical notions
  -- ===================

  -- Presheaves (of values, producers, normal and atomic forms)
  open import Presheaves

  -- Residuating monad
  open import Monad

  -- Normalization by evaluation
  -- =================

  -- NBE algorithm together with the residuating interpretation
  open import NBE