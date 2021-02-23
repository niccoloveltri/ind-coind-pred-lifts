module Examples.Global-Store where

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
--   Global store, single natural number
-- ==============================================

data gK : Set where
  lookup : gK
  update : ℕ → gK

gI : gK → Set
gI lookup = ℕ
gI (update n) = ⊤

g-obs : Set
g-obs = ℕ × ℕ

g-leaf : g-obs → Bool
g-leaf (zero , zero) = true
g-leaf (zero , suc m) = false
g-leaf (suc n , zero) = false
g-leaf (suc n , suc m) = g-leaf (n , m)


g-node : (v : gK) → g-obs → Test ((gI v) × g-obs)
g-node lookup (n , m) = atom (n , (n , m))
g-node (update x) (n , m) = atom (tt , (x , m))


import Pred-Lift-ab
open Pred-Lift-ab gI g-obs g-leaf g-node


-- Decomposable:
g-eq : (n m : ℕ) → (g-leaf (n , m) ≡ true) → (n ≡ m)
g-eq zero zero assum = refl
g-eq (suc n) (suc m) assum = cong suc (g-eq n m assum)
g-id : (n : ℕ) → g-leaf (n , n) ≡ true
g-id zero = refl
g-id (suc n) = g-id n

-- deco statement
g-deco : deco
g-deco (n , m) = ⋁ (λ k → atom ((n , k) , (k , m)))

g-deco-α-seq : deco-α-seq g-deco
g-deco-α-seq (n , m) (leaf x) (k , leaf-α x₁ x₂) =
  subst (λ z → α (z , m) x) (sym (g-eq n k x₁)) x₂
g-deco-α-seq (n , m) (node lookup ts) (k , node-α x) = node-α
  (g-deco-α-seq (n , m) (force (ts n)) (k , x))
g-deco-α-seq (n , m) (node (update x) ts) (k , node-α x₁) = node-α
  (g-deco-α-seq (x , m) (force (ts tt)) (k , x₁))

g-deco-α-unf : deco-α-unf g-deco
g-deco-α-unf (n , m) (leaf x) hyp = n , (leaf-α (g-id n) hyp)
g-deco-α-unf (n , m) (node lookup ts) (node-α x)
  with g-deco-α-unf (n , m) (force (ts n)) x
... | (k , hypo) = k , (node-α hypo)
g-deco-α-unf (n , m) (node (update x) ts) (node-α Q)
  with g-deco-α-unf (x , m) (force (ts tt)) Q
... | (k , hypo) = k , (node-α hypo)

-- Proposition: Bit-toggle is strong decomposable
g-is-strong : Strong-Decomposable
g-is-strong = deco-α-decomp g-deco g-deco-α-seq g-deco-α-unf



-- Coinductive
g-deco' : deco
g-deco' o = dualTest (g-deco o)

g-deco-β-seq : deco-β-seq g-deco'
g-deco-β-seq' : deco-β-seq' g-deco'
g-deco-β-seq (n , m) (leaf x) assum  with assum n
... | β-leaf x₁ = x₁
... | β-exep x₁ with subst (λ z → z ≡ false) (g-id n) x₁
... | ()
g-deco-β-seq (n , m) (node lookup ts) assum = β-node (g-deco-β-seq' ((n , m))
  (force (ts n)) (λ k → lem ts (assum k)))
  where
    lem : ∀ {n k m} → (ts : ℕ →  STree' gI (PTree gI) ∞)
      →  β-obsTower (node lookup ts) (n , k) (k , m)
      →  β-obsTower (force (ts n)) (n , k) (k , m)
    lem ts (β-node x) = β-force x
g-deco-β-seq (n , m) (node (update x) ts) assum = β-node (g-deco-β-seq' (x , m)
  (force (ts tt)) (λ k → lem ts (assum k)))
  where
    lem : ∀ {n k m} → (ts : ⊤ → STree' gI (PTree gI) ∞)
      →  β-obsTower (node (update x) ts) (n , k) (k , m)
      → β-obsTower (force (ts tt)) (x , k) (k , m)
    lem ts (β-node x) = β-force x
β-force (g-deco-β-seq' o d assum) = g-deco-β-seq o d assum


g-help5 : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
g-help5 false = inj₂ refl
g-help5 true = inj₁ refl

g-deco-β-unf : deco-β-unf g-deco'
g-deco-β-unf' : deco-β-unf' g-deco'
g-deco-β-unf (n , m) (leaf x) assum k with g-help5 (g-leaf (n , k))
... | inj₁ x₁ = β-leaf (subst (λ z → β ∞ (z , m) x) (g-eq n k x₁) assum)
... | inj₂ y = β-exep y
g-deco-β-unf (n , m) (node lookup ts) (β-node x) k =
  β-node (g-deco-β-unf' (n , m) (force (ts n)) (β-force x) k)
g-deco-β-unf (n , m) (node (update x) ts) (β-node x₁) k =
  β-node (g-deco-β-unf' (x , m) (force (ts tt)) (β-force x₁) k)
β-force (g-deco-β-unf' o d assum k) = g-deco-β-unf o d assum k

g-β-decomp : β-Strong-Decomposable
g-β-decomp = deco-β-decomp g-deco' g-deco-β-seq g-deco-β-unf

