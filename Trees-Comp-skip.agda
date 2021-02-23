module Trees-Comp-skip where

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
open import Signatures
open add-skip BSig BAr

-- ==============================================
--   GENERAL BIT-SKIP TREE COMPUTATIONS
-- ==============================================
  
pattern left = true
pattern right = false

BST-nodes = Sig⊥
BST-arit = ar⊥
BST-or : BST-nodes
BST-or = inj₁ b-or

num-gen : {i : Size} →  ℕ → STree BST-arit ℕ i
num-gen' : {i : Size} → ℕ → STree' BST-arit ℕ i

num-gen n = node BST-or (λ { left → record { force = λ { {j} → leaf n } } ; right → num-gen' (suc n) })

force (num-gen' n) = num-gen n

data pred-even : ℕ → Set where
  pe-zero : pred-even zero
  pe-ss : (n : ℕ) → pred-even n → pred-even (suc (suc n))

module bin-equations-skip (O : Set) (αl : O → Bool)
                 (αn : (k : BST-nodes) → O → Test ((BST-arit k) × O)) where

  import Pred-Lift-ab
  open Pred-Lift-ab BST-arit O αl αn

  g-x : VTree ar⊥
  g-x = leaf 0
  g-oxx : VTree ar⊥
  g-oxx = node BST-or (λ {left → record {force = leaf 0} ; right → record { force = leaf 0 }})
  g-oxy : VTree ar⊥
  g-oxy = node BST-or (λ {left → record {force = leaf 0} ; right → record { force = leaf 1 }})
  g-oyz : VTree ar⊥
  g-oyz = node BST-or (λ {left → record {force = leaf 1} ; right → record { force = leaf 2 }})
  g-oyx : VTree ar⊥
  g-oyx = node BST-or (λ {left → record {force = leaf 1} ; right → record { force = leaf 0 }})
  g-ooxyz : VTree ar⊥
  g-ooxyz = node BST-or (λ {left → record { force = g-oxy} ; right → record { force = leaf 2 }})
  g-oxoyz : VTree ar⊥
  g-oxoyz = node BST-or (λ {left → record { force = leaf 0} ; right → record { force = g-oyz }})

  idempotency1 = (g-x ◄ g-oxx)
  idempotency2 = (g-oxx ◄ g-x)
  symmetry = (g-oxy ◄ g-oyx)
  associativity1 = (g-ooxyz ◄ g-oxoyz) 
  associativity2 = (g-oxoyz ◄ g-ooxyz)

