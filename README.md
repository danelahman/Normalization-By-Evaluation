Normalization-By-Evaluation
===========================

Formalization of normalization by evaluation for a fine-grained call-by-value language extended with algebraic effects.


   AlgebraicSignaturesVersion
     
      - The normalization by evaluation algorithm and its correctness proofs for a language extended with simple algebraic signatures (no equations, no parameters)


   ParametersEquationsPERsVersion 
    
      - The version of normalization by evaluation and its correctness proofs for a language extended with parametrized algebraic signatures and equations. Normalization finds normal forms up-to PERs.
      
      
   StateNormalizationVersion
   
      - Work in progress implementation of normalization by evaluation for a language extended with algebraic operations for global state. Normalization uses a sum of two monads defined as a fixpoint of strictly positive functors and finds canonical normal forms (the state theory gets normalized).
      
      
   OlderCode
      
      - Older code mostly from the MPhil dissertation time
      
      
NOTICE: The code has been tested on Agda version 2.3.1. Newer versions of Agda might cause Monad.agda throw strange pattern-matching errors.