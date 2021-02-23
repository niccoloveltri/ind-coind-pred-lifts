module Examples.Bittog-skip where

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
open import Trees-Comp-skip
open import Signatures
open add-skip BSig BAr


-- ==============================================
--   BIT-TOGGLE, minimalist global store
-- ==============================================

t-obs = Bool × Bool
_↦_ : Bool → Bool → t-obs
a ↦ b = a , b

t-leaf : t-obs → Bool
t-leaf (left , left) = true
t-leaf (left , right) = false
t-leaf (right , right) = true
t-leaf (right , left) = false

t-node : (k : BST-nodes) → t-obs → Test ((BST-arit k) × t-obs)
t-node (inj₁ b-or) (left , b) = atom (left , (right , b))
t-node (inj₁ b-or) (right , b) = atom (right , (left , b))
t-node (inj₂ tt) o = atom (tt , o)

import Pred-Lift-ab
open Pred-Lift-ab BST-arit t-obs t-leaf t-node


-- Example:

t-01 : t-obs
t-01 = left , right

toggle-01-even0 : liftTree pred-even t-01 (num-gen zero)
toggle-01-even0 = node-α (leaf-α refl pe-zero)

t-11 : t-obs
t-11 = right , right

toggle-11-even1 : liftTree pred-even t-11 (num-gen (suc zero))
toggle-11-even1 = node-α (node-α (leaf-α refl (pe-ss zero pe-zero)))


-- Decomposable:

-- State transition composition
t-strong : (a b c : Bit) → (r : DTree ar⊥) → obsTower r (a ↦ b) (b ↦ c) → α (a ↦ c) (μTree r)
t-strong right right c (leaf x) (leaf-α x₁ x₂) = x₂
t-strong right left c (leaf x) (leaf-α () x₂)
t-strong left left c (leaf x) (leaf-α x₁ x₂) = x₂
t-strong left right c (leaf x) (leaf-α () x₂)
t-strong left b c (node (inj₁ b-or) ts) (node-α x) = node-α (t-strong right b c (force (ts left)) x)
t-strong right b c (node (inj₁ b-or) ts) (node-α x) = node-α (t-strong left b c (force (ts right)) x)
t-strong a b c (node (inj₂ tt) ts) (node-α x) = node-α (t-strong a b c (force (ts tt)) x)


-- Finding intermediate state
t-strong-inv : (a c : Bit) → (r : DTree ar⊥) → α (a ↦ c) (μTree r) → Σ Bit λ b →  obsTower r (a ↦ b) (b ↦ c)
t-strong-inv left c (leaf x) pruf = left , (leaf-α refl pruf)
t-strong-inv right c (leaf x) pruf = right , (leaf-α refl pruf)
t-strong-inv left c (node (inj₁ b-or) ts) (node-α x) with t-strong-inv right c (force (ts left)) x
... | fst , snd = fst , (node-α snd)
t-strong-inv right c (node (inj₁ b-or) ts) (node-α x) with t-strong-inv left c (force (ts right)) x
... | fst , snd = fst , (node-α snd)
t-strong-inv a c (node (inj₂ tt) ts) (node-α x) with t-strong-inv a c (force (ts tt)) x
... | fst , snd = fst , (node-α snd)

-- Proposition: Bit-toggle is strong decomposable
t-is-strong : Strong-Decomposable
t-is-strong r r' pruf (a , c) assum with t-strong-inv a c r assum
... | (b , tow) = t-strong a b c r' (pruf (a ↦ b) (b ↦ c) tow)

-- Implications
t-ab-imp-iac : (a b c : Bit) → (t : PTree ar⊥) → (α (a ↦ b) t) → (β ∞ (a ↦ c) t)
t-ab-imp-iac' : (a b c : Bit) → (t : PTree ar⊥) → (α (a ↦ b) t) → (β' ∞ (a ↦ c) t)
t-ab-imp-iac a b c (leaf P) (leaf-α L xP) = β-leaf xP
t-ab-imp-iac right b c (node (inj₁ b-or) ts) (node-α x) = β-node (t-ab-imp-iac' left b c (force (ts right)) x)
t-ab-imp-iac left b c (node (inj₁ b-or) ts) (node-α x) = β-node (t-ab-imp-iac' right b c (force (ts left)) x)
t-ab-imp-iac a b c (node (inj₂ tt) ts) (node-α x) = β-node (t-ab-imp-iac' a b c (force (ts tt)) x)
β-force (t-ab-imp-iac' a b c t hypo) = t-ab-imp-iac a b c t hypo


-- Sugar

-- Flip the bit operation
t-flip : {A : Set} (t : Tree BST-arit A) → Tree BST-arit A
t-flip t = node (inj₁ b-or) (λ {left → record { force = t } ; right → record { force = t}})
-- Lookup without flipping bit operation
t-lookup : {A : Set} (l r : Tree BST-arit A) → Tree BST-arit A
t-lookup l r = node (inj₁ b-or) (λ {left → record { force = t-flip l } ; right → record { force = t-flip r }})
-- Update to operation
t-update : {A : Set} (c : Bit) (t : Tree BST-arit A) → Tree BST-arit A
t-update left t = node (inj₁ b-or) (λ {left → record { force = t-flip t } ; right → record { force = t }})
t-update right t = node (inj₁ b-or) (λ {left → record { force = t } ; right → record { force = t-flip t }})

-- Equations
-- open bin-equations t-obs t-leaf t-node

-- Two flips is no flip
t-double-flip1 : (t-flip (t-flip (leaf 0)) ◄ leaf 0)
t-double-flip1 P (left , left) (node-α (node-α (leaf-α x x₁))) = leaf-α refl x₁
t-double-flip1 P (right , right) (node-α (node-α (leaf-α x x₁))) = leaf-α refl x₁
-- No flip is two flips
t-double-flip2 : (leaf 0 ◄ (t-flip (t-flip (leaf 0))))
t-double-flip2 P (left , left) (leaf-α x x₁) = node-α (node-α (leaf-α refl x₁))
t-double-flip2 P (right , right) (leaf-α x x₁) = node-α (node-α (leaf-α refl x₁))
-- Lookup after update 0 -> just update 0
t-up0lo : (t-update left (t-lookup (leaf 0) (leaf 1))) ◄ (t-update left (leaf 0))
t-up0lo P (left , left) (node-α (node-α (node-α (node-α (leaf-α x x₁))))) = node-α (node-α (leaf-α refl x₁))
t-up0lo P (right , left) (node-α (node-α (node-α (leaf-α x x₁)))) = node-α (leaf-α refl x₁)
-- Just update 0 -> Lookup after update 0
t-up0lo-inv : (t-update left (leaf 0)) ◄ (t-update left (t-lookup (leaf 0) (leaf 1)))
t-up0lo-inv P (left , left) (node-α (node-α (leaf-α x x₁))) = node-α (node-α (node-α (node-α (leaf-α refl x₁))))
t-up0lo-inv P (right , left) (node-α (leaf-α x x₁)) = node-α (node-α (node-α (leaf-α refl x₁)))

-- -- Double update (unnecessarily long)
-- t-doubup : (a b : Bit) → (t-update a (t-update b (leaf 0))) ◄ (t-update b (leaf 0))
-- t-doubup left left P (left , .left) (node-α (node-α (node-α (node-α (leaf-α refl x₁))))) = node-α (node-α (leaf-α refl x₁))
-- t-doubup left left P (right , .left) (node-α (node-α (node-α (leaf-α refl x₁)))) = node-α (leaf-α refl x₁)
-- t-doubup left right P (c , d) x = {!!}
-- t-doubup right b P (c , d) x = {!!}
