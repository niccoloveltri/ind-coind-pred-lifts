module Examples.Error (E : Set) where

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


-- ====================================================
--   ERROR (set of error messages without continuations
-- ====================================================

eI : E → Set
eI e = ⊥

e-obs : Set
e-obs = E → Bool

e-leaf : e-obs → Bool
e-leaf o = true

e-node : E → e-obs → Test (⊥ × e-obs)
e-node e f = if (f e) then true else false

import Pred-Lift-ab
open Pred-Lift-ab eI e-obs e-leaf e-node


e-help : {A : Set} → {P : A → Set} → (b : Bool) → (liftTest P (if b then true else false))
  → (true ≡ b)
e-help true hypo = refl


-- α-decomposition
e-deco : deco
e-deco f = atom (f , f)

e-deco-α-seq : (deco-α-seq e-deco)
e-deco-α-seq f (leaf x₁) (leaf-α x x₂) = x₂
e-deco-α-seq f (node e ts) (node-α x) = node-α
  (subst (λ z → liftTest _ (if z then true else false))
     (e-help (f e) x) tt)

e-deco-α-unf : (deco-α-unf e-deco)
e-deco-α-unf f (leaf (leaf _)) (leaf-α x x₁) = leaf-α refl (leaf-α refl x₁)
e-deco-α-unf f (leaf (node e ts)) (node-α x) = leaf-α refl (node-α
  (subst (λ z →  liftTest
      (uncurry
       (λ x₁ o' → α o' (force (ts x₁))))
      (if z then true else false)) (e-help (f e) x) tt))
e-deco-α-unf f (node e ts) (node-α x) = node-α
  (subst (λ z → liftTest (uncurry (λ x₁ o' → α o' (mapTree
           (α f) (force (ts x₁))))) (if z then true else false)) (e-help (f e) x) tt)

-- PROPOSITION:  error is strong decomposable
e-is-strong : Strong-Decomposable
e-is-strong = deco-α-decomp e-deco e-deco-α-seq e-deco-α-unf

e-help2 : {A : Set} → {P : A → Set} → (b : Bool)
  → (liftTest P (dualTest (if b then true else false))) → (false ≡ b)
e-help2 false hypo = refl

-- β-decomposition
e-deco' : deco
e-deco' o = dualTest (e-deco o)

e-deco-β-seq : deco-β-seq e-deco'
e-deco-β-seq' : deco-β-seq' e-deco'
e-deco-β-seq f (leaf x₁) (β-leaf x) = x
e-deco-β-seq f (node e ts) (β-node x) = β-node
  (subst (λ z → liftTest (uncurry (λ x₁ o' → β' ∞ o' (μTree (force (ts x₁)))))
        (dualTest (if z then true else false)))
     (e-help2 (f e) x) tt)
β-force (e-deco-β-seq' o r hypo) = e-deco-β-seq o r hypo

e-deco-β-unf : deco-β-unf e-deco'
e-deco-β-unf' : deco-β-unf' e-deco'
e-deco-β-unf f (leaf x) hypo = β-leaf hypo
e-deco-β-unf f (node e ts) (β-node x) = β-node
  (subst (λ z → liftTest
      (uncurry
       (λ x₁ o' →
          β' ∞ o'
          (mapTree
           (β  ∞ f)
           (force (ts x₁)))))
      (dualTest (if z then true else false))) (e-help2 (f e) x) tt )
β-force (e-deco-β-unf' ter d hypo) = e-deco-β-unf ter d hypo

-- Error is strong decomposable for β
e-β-decomp : β-Strong-Decomposable
e-β-decomp = deco-β-decomp e-deco' e-deco-β-seq e-deco-β-unf
