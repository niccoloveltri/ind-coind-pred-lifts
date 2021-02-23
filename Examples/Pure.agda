module Examples.Pure where

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

open import Tests
open import Trees-Coinductive


-- ==============================================
--   PURE, immediate termination (very trivial)
-- ==============================================

data u-obs : Set where
  ter : u-obs

u-leaf : u-obs → Bool
u-leaf o = true

u-node : ⊥ → u-obs → Test (⊥ × u-obs)
u-node ()

uI = (λ (_ : ⊥) → ⊥)

import Pred-Lift-ab
open Pred-Lift-ab uI u-obs u-leaf u-node


-- -- Decomposable:


-- deco formulation
u-deco : deco
u-deco ter = atom (ter , ter)

u-deco-α-seq : (deco-α-seq u-deco)
u-deco-α-seq ter (leaf x₁) (leaf-α x x₂) = x₂

u-deco-α-unf : (deco-α-unf u-deco)
u-deco-α-unf ter (leaf .(leaf _)) (leaf-α x x₁) = leaf-α refl (leaf-α refl x₁)

-- PROPOSITION:  may+must nondeterminism is strong decomposable
u-is-strong : Strong-Decomposable
u-is-strong = deco-α-decomp u-deco u-deco-α-seq u-deco-α-unf


-- Coinductive
u-deco' : deco
u-deco' o = dualTest (u-deco o)

u-deco-β-seq : deco-β-seq u-deco'
u-deco-β-seq' : deco-β-seq' u-deco'
u-deco-β-seq ter (leaf x₁) (β-leaf x) = x
β-force (u-deco-β-seq' o r hypo) = u-deco-β-seq o r hypo

u-deco-β-unf : deco-β-unf u-deco'
u-deco-β-unf' : deco-β-unf' u-deco'
u-deco-β-unf ter (leaf x) hypo = β-leaf hypo
β-force (u-deco-β-unf' ter d hypo) = u-deco-β-unf ter d hypo

u-β-decomp : β-Strong-Decomposable
u-β-decomp = deco-β-decomp u-deco' u-deco-β-seq u-deco-β-unf
