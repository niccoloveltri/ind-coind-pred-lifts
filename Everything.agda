
-- =================================================================
-- Inductive and Coinductive Predicate Liftings
-- for Effectful Programs

-- Niccolò Veltri   and   Niels Voorneveld
-- =================================================================


module Everything where


-- Basic tools

-- A test logic for formulating predicates
open import Tests

-- Some signature/container definitions
open import Signatures

-- Coinductive trees for describing effectful computations
open import Trees-Coinductive


-- =================================================================

-- Predicate liftings for effectful program

-- Inductive predicate lifting for total properties
open import Pred-Lift-a

-- Coinductive predicate lifting for partial properties
open import Pred-Lift-b

-- How the inductive and coinductive are eachothers duals
open import Pred-Lift-ab


-- =================================================================

-- Describing higher-order effectful programs

-- Types for program denotations
open import Program-Types

-- Logic of behavioural properties for programs
open import Logic

-- Sequentiality properties of logic due to decomposability
open import Logic-decomp

-- Applicative simulations for describing similarities between programs
open import Relations


-- =================================================================

-- Examples of effects

-- Basic comutation trees examples and properties
open import Trees-Comp

-- Example: pure computation
open import Examples.Pure

-- Example: undetectable skip computation (in paper)
open import Examples.Skip

-- Example: Execution cost (in paper)
open import Examples.Cost

-- Example: binary nondeterminism (in paper)
open import Examples.Nondeterminism

-- Example: Global store (in paper)
open import Examples.Global-Store

-- Example: User binary input (in paper)
open import Examples.Input

-- Example: error
open import Examples.Error

-- Example: Reading and flipping bits
open import Examples.Bit-toggle

-- Example: Probability
open import Examples.Probability


-- =================================================================

-- Examples of computational systems

-- Call-by-value PCF
open import Languages.CBV-PCF

-- Automata like language exhibiting effectful behaviour
open import Languages.Automata

-- Logic for typed partial combinatory algebras
-- Variation on the code of Logic and Logic-decomp
open import Languages.Logic-typed


-- =================================================================

-- Additional code, regarding topics from earlier in the developement

-- Applicative simulations using more traditional relators
-- which formally lack some useful properties
open import Relators

-- Logic for call-by-value PCF (variation on the above denotation logic)
open import Languages.CBV-PCF-logic

-- Examples with explicit executions steps
open import Trees-Comp-skip

open import Examples.Nondet-skip

open import Examples.Bittog-skip
