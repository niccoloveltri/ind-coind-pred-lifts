module Examples.Skip where

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
--   Solitary undetectable SKIP
--   (for general recursion)
-- ==============================================

data s-obs : Set where
  ter : s-obs

s-leaf : s-obs → Bool
s-leaf o = true

s-node : ⊤ → s-obs → Test (⊤ × s-obs)
s-node tt ter = atom (tt , ter)

sI : ⊤ → Set
sI tt = ⊤

import Pred-Lift-ab
open Pred-Lift-ab sI s-obs s-leaf s-node


-- α-decomposition
s-deco : deco
s-deco ter = atom (ter , ter)

s-deco-α-seq : (deco-α-seq s-deco)
s-deco-α-seq ter (leaf x₁) (leaf-α x x₂) = x₂
s-deco-α-seq ter (node tt ts) (node-α x) = node-α (s-deco-α-seq ter (force (ts tt)) x)

s-deco-α-unf : (deco-α-unf s-deco)
s-deco-α-unf ter (leaf y) x = leaf-α refl x
s-deco-α-unf ter (node tt ts) (node-α x) = node-α (s-deco-α-unf ter (force (ts tt)) x)

-- α-decomposability
s-is-strong : Strong-Decomposable
s-is-strong = deco-α-decomp s-deco s-deco-α-seq s-deco-α-unf


-- β-decomposition
s-deco' : deco
s-deco' o = dualTest (s-deco o)

s-deco-β-seq : deco-β-seq s-deco'
s-deco-β-seq' : deco-β-seq' s-deco'
s-deco-β-seq ter (leaf x₁) (β-leaf x) = x
s-deco-β-seq ter (node tt ts) (β-node x) =
  β-node (s-deco-β-seq' ter (force (ts tt)) (β-force x))
β-force (s-deco-β-seq' o r hypo) = s-deco-β-seq o r hypo

s-deco-β-unf : deco-β-unf s-deco'
s-deco-β-unf' : deco-β-unf' s-deco'
s-deco-β-unf ter (leaf x) hypo = β-leaf hypo
s-deco-β-unf ter (node tt ts) (β-node x) = β-node
  (s-deco-β-unf' ter (force (ts tt)) (β-force x))
β-force (s-deco-β-unf' ter d hypo) = s-deco-β-unf ter d hypo

-- β-decomposability
s-β-decomp : β-Strong-Decomposable
s-β-decomp = deco-β-decomp s-deco' s-deco-β-seq s-deco-β-unf
