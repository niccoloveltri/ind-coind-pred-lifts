module Examples.Bit-toggle where

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
open import Trees-Comp


-- ===========================================================
--   BIT-TOGGLE, the minimalist version of binary global store
-- ===========================================================


t-obs = Bit × Bit
_↦_ : Bit → Bit → t-obs
a ↦ b = a , b

t-leaf : t-obs → Bool
t-leaf (left , left) = true
t-leaf (left , right) = false
t-leaf (right , left) = false
t-leaf (right , right) = true


t-node : True → t-obs → Test (Bit × t-obs)
t-node * (left , b) = atom (left , (right , b))
t-node * (right , b) = atom (right , (left , b))

bI = (λ (_ : True) → Bit)

import Pred-Lift-ab
open Pred-Lift-ab bI t-obs t-leaf t-node


-- Example:

t-01 : t-obs
t-01 = left , right

toggle-01-even0 : liftTree pred-even t-01 (num-gen zero)
toggle-01-even0 = node-α (leaf-α refl pe-zero)

t-11 : t-obs
t-11 = right , right

toggle-11-even1 : liftTree pred-even t-11 (num-gen (suc zero))
toggle-11-even1 = node-α (node-α (leaf-α refl (pe-ss zero pe-zero)))


-- Decomposability

-- State transition composition
t-strong : (a b c : Bit) → (r : DTree bI) → obsTower r (a ↦ b) (b ↦ c) → α (a ↦ c) (μTree r)
t-strong left left c (leaf x) (leaf-α x₁ x₂) = x₂
t-strong left right c (leaf x) (leaf-α () x₂)
t-strong right left c (leaf x) (leaf-α () x₂)
t-strong right right c (leaf x) (leaf-α x₁ x₂) = x₂
t-strong left b c (node _ ts) (node-α x) = node-α (t-strong right b c (force (ts left)) x)
t-strong right b c (node _ ts) (node-α x) = node-α (t-strong left b c (force (ts right)) x)

-- Finding intermediate state
t-strong-inv : (a c : Bit) → (r : DTree bI) → α (a ↦ c) (μTree r) → Σ Bit λ b →  obsTower r (a ↦ b) (b ↦ c)
t-strong-inv left c (leaf x) pruf = left , (leaf-α refl pruf)
t-strong-inv right c (leaf x) pruf = right , (leaf-α refl pruf)
t-strong-inv left c (node _ ts) (node-α x) with t-strong-inv right c (force (ts left)) x
... | fst , snd = fst , (node-α snd)
t-strong-inv right c (node _ ts) (node-α x) with t-strong-inv left c (force (ts right)) x
... | fst , snd = fst , (node-α snd)

-- α-decomposition
t-deco : deco
t-deco (a , b) = (atom ((a ↦ left) , (left ↦ b))) ∨ (atom ((a ↦ right) , (right ↦ b)))

t-deco-α-seq : deco-α-seq t-deco
t-deco-α-seq (a , b) d (inj₁ x) = t-strong a left b d x
t-deco-α-seq (a , b) d (inj₂ y) = t-strong a right b d y

t-deco-α-unf : deco-α-unf t-deco
t-deco-α-unf (a , b) d x with t-strong-inv a b d x
... | left , y = inj₁ y
... | right , y = inj₂ y

-- Proposition: Bit-toggle is strong decomposable
t-is-strong : Strong-Decomposable
t-is-strong = deco-α-decomp t-deco t-deco-α-seq t-deco-α-unf


-- β-decomposition
t-deco' : deco
t-deco' o = dualTest (t-deco o)

t-deco-β-seq : deco-β-seq t-deco'
t-deco-β-seq' : deco-β-seq' t-deco'
t-deco-β-seq (left , snd) (leaf x) (β-leaf x₁ , x₂) = x₁
t-deco-β-seq (right , snd) (leaf x) (x₁ , β-leaf x₂) = x₂
t-deco-β-seq (left , snd) (node k ts) (β-node x , β-node x₁) = β-node (
  t-deco-β-seq' (right , snd) (force (ts left)) ((β-force x) , (β-force x₁)))
t-deco-β-seq (right , snd) (node k ts) (β-node x , β-node x₁) = β-node (
  t-deco-β-seq' (left , snd) (force (ts right)) ((β-force x) , (β-force x₁)))
β-force (t-deco-β-seq' o d hypo) = t-deco-β-seq o d hypo

t-deco-β-unf : deco-β-unf t-deco'
t-deco-β-unf' : deco-β-unf' t-deco'
t-deco-β-unf (left , snd) (leaf x) hypo = (β-leaf hypo) , (β-exep refl)
t-deco-β-unf (right , snd) (leaf x) hypo = (β-exep refl) , (β-leaf hypo)
t-deco-β-unf (left , snd) (node k ts) (β-node x) =
  (β-node (proj₁ (t-deco-β-unf' (right , snd) (force (ts left)) (β-force x)))) ,
  (β-node (proj₂ (t-deco-β-unf' (right , snd) (force (ts left)) (β-force x))))
t-deco-β-unf (right , snd) (node k ts) (β-node x) =
  (β-node (proj₁ (t-deco-β-unf' (left , snd) (force (ts right)) (β-force x)))) ,
  (β-node (proj₂ (t-deco-β-unf' (left , snd) (force (ts right)) (β-force x))))
β-force (proj₁ (t-deco-β-unf' o d hypo)) = proj₁ (t-deco-β-unf o d hypo)
β-force (proj₂ (t-deco-β-unf' o d hypo)) = proj₂ (t-deco-β-unf o d hypo)

t-β-decomp : β-Strong-Decomposable
t-β-decomp = deco-β-decomp t-deco' t-deco-β-seq t-deco-β-unf


-- Global store operations

-- Flip the bit operation
t-flip : {A : Set} (t : Tree (λ (_ : True) → Bit) A) → Tree (λ (_ : True) → Bit) A
t-flip t = node true (λ {left → record { force = t } ; right → record { force = t}})
-- Lookup without flipping bit operation
t-lookup : {A : Set} (l r : Tree (λ (_ : True) → Bit) A) → Tree (λ (_ : True) → Bit) A
t-lookup l r = node true (λ {left → record { force = t-flip l } ; right → record { force = t-flip r }})
-- Update to operation
t-update : {A : Set} (c : Bit) (t : Tree (λ (_ : True) → Bit) A) → Tree (λ (_ : True) → Bit) A
t-update left t = node true (λ {left → record { force = t-flip t } ; right → record { force = t }})
t-update right t = node true (λ {left → record { force = t } ; right → record { force = t-flip t }})


-- Equations

-- Two flips is no flip
t-double-flip1 : (t-flip (t-flip (leaf 0)) ◄ leaf 0)
t-double-flip1 P (left , left) (node-α (node-α (leaf-α x x₁))) = leaf-α refl x₁
t-double-flip1 P (right , right) (node-α (node-α (leaf-α refl x₁))) = leaf-α refl x₁
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
