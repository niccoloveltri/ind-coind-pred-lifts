open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool hiding (_∧_; _∨_)

module Pred-Lift-ab {K : Set} (I : K → Set)
                 (O : Set) (πl : O → Bool)
                 (πn : (k : K) → O → Test (I k × O)) where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size

open import Trees-Coinductive
import Pred-Lift-a
open Pred-Lift-a I O πl πn   public
import Pred-Lift-b
open Pred-Lift-b I O πl πn   public

-- ==============================================
--   BOTH INDUCTIVE AND COINDUCTIVE PREDICATIVE LIFTING
-- ==============================================


-- Distinction result

dist-αβ : {A : Set} → (P Q : A → Set) → ((a : A) → (P a) → (Q a) → ⊥)
  → (t : Tree I A) → (o : O)
  → (β-liftTree Q o t)
  → (liftTree P o t)
  → ⊥
dist-αβ-tes : {A : Set} → (P Q : A → Set) → ((a : A) → (P a) → (Q a) → ⊥)
  → (k : K) → (ts : I k → Tree I A) → (tes : Test (I k × O))
  → liftTest (uncurry (λ x₂ o' → β' ∞ o' (mapTree Q (ts x₂)))) (dualTest tes)
  → liftTest (uncurry (λ x₂ o' → α o' (mapTree P (ts x₂)))) tes
  → ⊥
dist-αβ P Q P-Q (leaf x) o (β-leaf Qx) (leaf-α L Px) = P-Q x Px Qx
dist-αβ P Q P-Q (leaf x) o (β-exep nL) (leaf-α L Px) with subst (λ y → (y ≡ false)) L nL
...| () 
dist-αβ P Q P-Q (node k ts) o (β-node x) (node-α x₁) =
  dist-αβ-tes P Q P-Q k (λ i → force (ts i)) (πn k o) x x₁
dist-αβ-tes P Q P-Q k ts (atom x) coin ind =
  dist-αβ P Q P-Q (ts (proj₁ x)) (proj₂ x) (β-force coin) ind
dist-αβ-tes P Q P-Q k ts (tes ∧ tes₁) (inj₁ x) (fst , snd) =
  dist-αβ-tes P Q P-Q k ts tes x fst
dist-αβ-tes P Q P-Q k ts (tes ∧ tes₁) (inj₂ y) (fst , snd) =
  dist-αβ-tes P Q P-Q k ts tes₁ y snd
dist-αβ-tes P Q P-Q k ts (tes ∨ tes₁) (fst , snd) (inj₁ x) =
  dist-αβ-tes P Q P-Q k ts tes fst x
dist-αβ-tes P Q P-Q k ts (tes ∨ tes₁) (fst , snd) (inj₂ y) =
  dist-αβ-tes P Q P-Q k ts tes₁ snd y
dist-αβ-tes P Q P-Q k ts (⋁ x) coin (n , ind) = dist-αβ-tes P Q P-Q k ts (x n) (coin n) ind
dist-αβ-tes P Q P-Q k ts (⋀ x) (n , coin) ind = dist-αβ-tes P Q P-Q k ts (x n) coin (ind n)

