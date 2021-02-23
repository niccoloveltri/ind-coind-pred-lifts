module Trees-Comp where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size

open import Trees-Coinductive
open import Tests

-- ==============================================
--   GENERAL BINARY TREE COMPUTATIONS
-- ==============================================

data True : Set where
  true : True

data False : Set where
  
data Bit : Set where
  left : Bit
  right : Bit

-- Natural number generator
num-gen : {i : Size} →  ℕ → STree (λ (_ : True) → Bit) ℕ i
num-gen' : {i : Size} → ℕ → STree' (λ _ → Bit) ℕ i

num-gen n = node true (λ { left → record { force = λ { {j} → leaf n } } ; right →
  num-gen' (suc n) })

force (num-gen' n) = num-gen n

data pred-even : ℕ → Set where
  pe-zero : pred-even zero
  pe-ss : (n : ℕ) → pred-even n → pred-even (suc (suc n))

-- Equations for binary decision trees
module bin-equations (O : Set) (αl : O → Bool)
                 (αn : True → O → Test (Bit × O)) where

  bI : True → Set
  bI k = Bit

  import Pred-Lift-ab
  open Pred-Lift-ab bI O αl αn

  -- some basic variable expressions
  g-x : VTree bI
  g-x = leaf 0
  g-oxx : VTree bI
  g-oxx = node true (λ {left → record {force = leaf 0} ; right → record { force = leaf 0 }})
  g-oxy : VTree bI
  g-oxy = node true (λ {left → record {force = leaf 0} ; right → record { force = leaf 1 }})
  g-oyz : VTree bI
  g-oyz = node true (λ {left → record {force = leaf 1} ; right → record { force = leaf 2 }})
  g-oyx : VTree bI
  g-oyx = node true (λ {left → record {force = leaf 1} ; right → record { force = leaf 0 }})
  g-ooxyz : VTree bI
  g-ooxyz = node true (λ {left → record { force = g-oxy} ; right → record { force = leaf 2 }})
  g-oxoyz : VTree bI
  g-oxoyz = node true (λ {left → record { force = leaf 0} ; right → record { force = g-oyz }})

  -- The equation for idempotency
  idempotency1 = (g-x ◄ g-oxx)
  idempotency2 = (g-oxx ◄ g-x)

  -- The equation for symmetry
  symmetry = (g-oxy ◄ g-oyx)

  -- The equations for associativity
  associativity1 = (g-ooxyz ◄ g-oxoyz) 
  associativity2 = (g-oxoyz ◄ g-ooxyz)

