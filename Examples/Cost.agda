module Examples.Cost where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size

open import Tests
open import Trees-Coinductive


-- ==============================================
--   COST
-- ==============================================

cI : ⊤ → Set
cI tt = ⊤

c-obs : Set
c-obs = ℕ

c-leaf : c-obs → Bool
c-leaf o = true

c-node : ⊤ → c-obs → Test (⊤ × c-obs)
c-node tt zero = false
c-node tt (suc n) = atom (tt , n)

import Pred-Lift-ab
open Pred-Lift-ab cI c-obs c-leaf c-node


-- Decomposable:
infix 4 _<=_

_<=_ : ℕ → ℕ → Bool
zero <= m = true
(suc n) <= zero = false
(suc n) <= (suc m) = n <= m


c-mono : (n k : ℕ) → ((n <= k) ≡ true) → (x : PTree cI) → (α n x) → (α k x)
c-mono n k hypo (leaf x) (leaf-α x₁ x₂) = leaf-α refl x₂
c-mono (suc n) (suc k) hypo (node k₁ ts) (node-α x) =
  node-α (c-mono n k hypo (force (ts tt)) x)

c-help : {A : Set} → (tes : Test A) → (b : Bool) → (f : A → Set) →
  liftTest f (if b then tes else false) → (b ≡ true) × (liftTest f tes)
c-help tes true f k = refl , k

-- α-decomposition
c-deco : deco
c-deco n = ⋁ (λ m → ⋁ (λ k → (if (m + k) <= n then atom (m , k) else false)))

c-deco-α-seq : (deco-α-seq c-deco)
c-deco-α-seq n (leaf x) (m , k , snd)
  with c-help (atom (m , k)) (m + k <= n)
       (λ x₁ → obsTower (leaf x) (proj₁ x₁) (proj₂ x₁)) snd
... | fst , leaf-α x₁ x₂ = c-mono k n (lem1 m k n fst) x x₂ where
  lem1 : (m k n : ℕ) → (m + k <= n) ≡ true → (k <= n) ≡ true
  lem1 zero k n hypo = hypo
  lem1 (suc m) k (suc n) hypo = lem1 m k (suc n) (lem2 (m + k) n hypo) where
    lem2 : (a b : ℕ) → ((a <= b) ≡ true) → ((a <= suc b) ≡ true)
    lem2 zero b hip = refl
    lem2 (suc a) (suc b) hip = lem2 a b hip
c-deco-α-seq n (node tt ts) (m , k , snd)
  with c-help (atom (m , k)) (m + k <= n)
       (λ x₁ → obsTower (node tt ts) (proj₁ x₁) (proj₂ x₁)) snd
c-deco-α-seq n (node tt ts) (zero , k , snd) | fst , node-α ()
c-deco-α-seq zero (node tt ts) (suc m , k , snd) | () , node-α x
c-deco-α-seq (suc n) (node tt ts) (suc m , k , snd) | fst , node-α x = node-α
  (c-deco-α-seq n (force (ts tt)) (m , k , subst
  (λ z → liftTest (λ x₁ → obsTower (force (ts tt)) (proj₁ x₁) (proj₂ x₁))
         (if z then atom (m , k) else false)) (sym fst) x))

c-help2 : (n : ℕ) → true ≡ (n <= n)
c-help2 zero = refl
c-help2 (suc n) = c-help2 n

c-deco-α-unf : (deco-α-unf c-deco)
c-deco-α-unf n (leaf x) hypo = zero , (n , subst
  (λ z → liftTest (λ x₁ → obsTower (leaf x) (proj₁ x₁) (proj₂ x₁))
                  (if z then atom (zero , n) else false))
  (c-help2 n) (leaf-α refl hypo))
c-deco-α-unf (suc n) (node tt ts) (node-α x) with c-deco-α-unf n (force (ts tt)) x
...| (m , k , pruf) with c-help (atom (m , k)) (m + k <= n)
  (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) (force (ts tt)))) pruf
... | eq , ye = (suc m) , (k , (subst (λ z → liftTest
  (λ x₁ → α (proj₁ x₁) (node tt (λ x₂ → mapTree' (α (proj₂ x₁)) (ts x₂))))
  (if z then atom (suc m , k) else false)) (sym eq) (node-α ye)))


c-is-strong : Strong-Decomposable
c-is-strong = deco-α-decomp c-deco c-deco-α-seq c-deco-α-unf

-- β-decomposition
c-deco' : deco
c-deco' o = dualTest (c-deco o)

c-deco-β-seq-help : ∀ n d
  → (∀ m k → ((m + k <= n) ≡ true) → β-obsTower d m k)
  → β ∞ n (μTree d)
c-deco-β-seq-help' : ∀ n d
  → (∀ m k → ((m + k <= n) ≡ true) → β-obsTower d m k)
  → β' ∞ n (μTree d)
c-deco-β-seq-help n (leaf x) p with p zero n
...| case with case (sym (c-help2 n))
... | β-leaf x₁ = x₁
c-deco-β-seq-help zero (node tt ts) p = β-node tt
c-deco-β-seq-help (suc n) (node tt ts) p = β-node (c-deco-β-seq-help' n (force (ts tt)) lem)
  where
    lem : ∀ m k → ((m + k) <= n) ≡ true
      → β ∞ m (mapTree (β ∞ k) (force (ts tt)))
    lem m k prp with p (suc m) k prp
    ... | β-node x = β-force x
β-force (c-deco-β-seq-help' n d p) = c-deco-β-seq-help n d p

c-deco-β-seq : deco-β-seq c-deco'
c-deco-β-seq n d x = c-deco-β-seq-help n d lem
  where
    lem : ∀ m k → (((m + k) <= n) ≡ true)
      → β ∞ m (mapTree (β ∞ k) d)
    lem m k prp  with x m k
    ... | info = subst (λ z → liftTest (λ n₂ → β ∞ (proj₁ n₂) (mapTree (β ∞ (proj₂ n₂)) d))
                       (dualTest (if z then atom (m , k) else false))) prp info

c-βmono : (t : PTree cI) → (n m : ℕ) → (n <= m) ≡ true → β ∞ m t → β ∞ n t
c-βmono' : (t : PTree cI) → (n m : ℕ) → (n <= m) ≡ true → β ∞ m t → β' ∞ n t
c-βmono (leaf x) n m inq (β-leaf x₁) = β-leaf x₁
c-βmono (node tt ts) zero m inq (β-node x) = β-node tt
c-βmono (node tt ts) (suc n) (suc m) inq (β-node x) = β-node
  (c-βmono' (force (ts tt)) n m inq (β-force x))
β-force (c-βmono' t n m inq assum) = c-βmono t n m inq assum

c-help4 : (m k : ℕ) → (m + suc k) ≡ suc (m + k)
c-help4 zero k = refl
c-help4 (suc m) k = subst (λ z → suc z ≡ suc (suc (m + k))) (sym (+-comm m (suc k)))
  (cong (λ z → suc (suc z)) (+-comm k m))
c-help5 : (m k : ℕ) → (suc m + k) ≡ (m + suc k)
c-help5 zero k = refl
c-help5 (suc m) k = sym (cong (λ z → suc z) (c-help4 m k))

c-deco-β-unf-help : ∀ m k d
  → β ∞ (m + k) (μTree d) → β-obsTower d m k
c-deco-β-unf-help' : ∀ m k d
  → β ∞ (m + k) (μTree d) → β-obsTower' d m k
c-deco-β-unf-help zero k (leaf x) prp = β-leaf prp
c-deco-β-unf-help zero k (node k₁ ts) prp = β-node tt
c-deco-β-unf-help (suc m) k (leaf x) prp = β-leaf (c-βmono x k (suc (m + k)) (lem m k) prp)
  where
    lem : ∀ m k → (k <= suc (m + k)) ≡ true
    lem zero zero = refl
    lem zero (suc k) = lem zero k
    lem (suc m) zero = refl
    lem (suc m) (suc k) = subst (λ z → (k <= suc z) ≡ true) (c-help5 m k) (lem (suc m) k)
c-deco-β-unf-help (suc m) k (node tt ts) (β-node x) =
                       β-node (c-deco-β-unf-help' m k (force (ts tt)) (β-force x))
β-force (c-deco-β-unf-help' m k d prp) = c-deco-β-unf-help m k d prp

c-deco-β-unf : deco-β-unf c-deco'
c-deco-β-unf n d prp k m
  with λ z → c-deco-β-unf-help k m d (c-βmono (μTree d) (k + m) n z prp)
... | help  with ((k + m) <= n)
... | false = tt
... | true = help refl

c-β-decomp : β-Strong-Decomposable
c-β-decomp = deco-β-decomp c-deco' c-deco-β-seq c-deco-β-unf
