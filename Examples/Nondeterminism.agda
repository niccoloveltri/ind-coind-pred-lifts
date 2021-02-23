module Examples.Nondeterminism where

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


-- ==============================================
--   NONDETERMINISM, convex
-- ==============================================

data n-obs : Set where
  may : n-obs
  must : n-obs

n-leaf : n-obs → Bool
n-leaf o = true

n-node : True → n-obs → Test (Bit × n-obs)
n-node * may = (atom (left , may)) ∨ (atom (right , may))
n-node * must = (atom (left , must)) ∧ (atom (right , must))

bI = (λ (_ : True) → Bit)

import Logic
open Logic bI n-obs n-leaf n-node


-- Decomposability: Helpful lemmas

-- may may => may
strong-may : (r : DTree bI) → obsTower r may may → α may (μTree r)
strong-may (leaf x) (leaf-α x₁ x₂) = x₂
strong-may (node _ ts) (node-α (inj₁ x)) = node-α (inj₁ (strong-may (force (ts left)) x))
strong-may (node _ ts) (node-α (inj₂ y)) = node-α (inj₂ (strong-may (force (ts right)) y))

-- may => may may
strong-may-inv : (r : DTree bI) → α may (μTree r) → obsTower r may may
strong-may-inv (leaf x) = λ x₁ → leaf-α refl x₁
strong-may-inv (node _ ts) (node-α (inj₁ x)) = node-α (inj₁ (strong-may-inv (force (ts left)) x))
strong-may-inv (node _ ts) (node-α (inj₂ y)) = node-α (inj₂ (strong-may-inv ((force (ts right))) y))

-- must must => must
strong-must : (r : DTree bI) → obsTower r must must → α must (μTree r)
strong-must (leaf x) (leaf-α x₁ x₂) = x₂
strong-must (node _ ts) (node-α (fst , snd)) = node-α ((strong-must (force (ts left)) fst) , (strong-must (force (ts right)) snd))

-- must => must must
strong-must-inv : (r : DTree bI) → α must (μTree r) → obsTower r must must
strong-must-inv (leaf x) pruf = leaf-α refl pruf
strong-must-inv (node _ ts) (node-α (fst , snd)) = node-α ((strong-must-inv (force (ts left)) fst) , (strong-must-inv (force (ts right)) snd))

-- α-decomposition
n-deco : deco
n-deco may = atom (may , may)
n-deco must = atom (must , must)

n-deco-α-seq : (deco-α-seq n-deco)
n-deco-α-seq may d x = strong-may d x
n-deco-α-seq must d x = strong-must d x

n-deco-α-unf : (deco-α-unf n-deco)
n-deco-α-unf may d x = strong-may-inv d x
n-deco-α-unf must d x = strong-must-inv d x

-- PROPOSITION:  may+must nondeterminism is strong decomposable
n-is-strong : Strong-Decomposable
n-is-strong = deco-α-decomp n-deco n-deco-α-seq n-deco-α-unf


-- β-decomposition
n-deco' : deco
n-deco' o = dualTest (n-deco o)

n-deco-β-seq : deco-β-seq n-deco'
n-deco-β-seq' : deco-β-seq' n-deco'
n-deco-β-seq may (leaf t) (β-leaf x) = x
n-deco-β-seq may (node k ts) (β-node (fst , snd)) = β-node (
  n-deco-β-seq' may (force (ts left)) (β-force fst) ,
  n-deco-β-seq' may (force (ts right)) (β-force snd))
n-deco-β-seq must (leaf t) (β-leaf x) = x
n-deco-β-seq must (node k ts) (β-node (inj₁ x)) = β-node (
  inj₁ (n-deco-β-seq' must (force (ts left)) (β-force x)))
n-deco-β-seq must (node k ts) (β-node (inj₂ y)) = β-node (
  inj₂ (n-deco-β-seq' must (force (ts right)) (β-force y)))
β-force (n-deco-β-seq' o r hypo) = n-deco-β-seq o r hypo

n-deco-β-unf : deco-β-unf n-deco'
n-deco-β-unf' : deco-β-unf' n-deco'
n-deco-β-unf may (leaf x) hypo = β-leaf hypo
n-deco-β-unf may (node k ts) (β-node (fst , snd)) = β-node (
  n-deco-β-unf' may (force (ts left)) (β-force fst)  ,
  n-deco-β-unf' may ((force (ts right))) (β-force snd))
n-deco-β-unf must (leaf x) hypo = β-leaf hypo
n-deco-β-unf must (node k ts) (β-node (inj₁ x)) = β-node (
  inj₁ (n-deco-β-unf' must (force (ts left)) (β-force x)))
n-deco-β-unf must (node k ts) (β-node (inj₂ y)) = β-node (
  inj₂ (n-deco-β-unf' must (force (ts right)) (β-force y)))
β-force (n-deco-β-unf' may d hypo) = n-deco-β-unf may d hypo
β-force (n-deco-β-unf' must d hypo) = n-deco-β-unf must d hypo

-- Nondeterminism is strong decomposable for β
n-β-decomp : β-Strong-Decomposable
n-β-decomp = deco-β-decomp n-deco' n-deco-β-seq n-deco-β-unf



-- Equations for nondeterminism
open bin-equations n-obs n-leaf n-node

n-is-idem1 : idempotency1
n-is-idem1 P may x = node-α (inj₁  x)
n-is-idem1 P must x = node-α (x , x)

n-is-idem2 : idempotency2
n-is-idem2 P may (node-α (inj₁ x)) = x
n-is-idem2 P may (node-α (inj₂ y)) = y
n-is-idem2 P must (node-α (x , y)) = x

n-is-sym : symmetry
n-is-sym P may (node-α (inj₁ x)) = node-α (inj₂ x)
n-is-sym P may (node-α (inj₂ y)) = node-α (inj₁ y)
n-is-sym P must (node-α (x , y)) = node-α (y , x)

n-is-assoc1 : associativity1
n-is-assoc1 P may (node-α (inj₁ (node-α (inj₁ x)))) = node-α (inj₁ x)
n-is-assoc1 P may (node-α (inj₁ (node-α (inj₂ y)))) = node-α (inj₂ (node-α (inj₁ y)))
n-is-assoc1 P may (node-α (inj₂ z)) = node-α (inj₂ (node-α (inj₂ z)))
n-is-assoc1 P must (node-α (node-α (x , y) , z)) = node-α (x , node-α (y , z))


-- EXAMPLE COMPUTATIONS

-- Always diverging element Omega
n-Omega : (τ : Aty) → (A-cpt τ)
n-Omega' : (τ : Aty) → (A-cpt' τ)
n-Omega τ = node true (λ x → n-Omega' τ)
force (n-Omega' τ) = n-Omega τ

Omega-diverges : (τ : Aty) → (o : n-obs) → (ϕ : A-form val τ) →
  (n-Omega τ ⊧ bas-Comβ o ϕ)
Omega-diverges' : (τ : Aty) → (o : n-obs) → (ϕ : A-form val τ) →
  β-liftTree' (λ V → V ⊧ ϕ) o (n-Omega τ)
Omega-diverges τ may ϕ = β-node (Omega-diverges' τ may ϕ , Omega-diverges' τ may ϕ)
Omega-diverges τ must ϕ = β-node (inj₁ (Omega-diverges' τ must ϕ))
β-force (Omega-diverges' τ o ϕ) = Omega-diverges τ o ϕ

-- Returning zero, or terminating
bitBool : Bit → Bool
bitBool left = true
bitBool right = false

leaf-0' : A-cpt' N
force (leaf-0') = leaf zero

n-ZorO : A-cpt N
n-ZorO = node true (λ x → if (bitBool x) then leaf-0'
                                         else n-Omega' N )

ZorO-may-1 : n-ZorO ⊧ bas-Comα may (bas-Nat zero)
ZorO-may-1 = node-α (inj₁ (leaf-α refl refl))

ZorO-may-diverge : n-ZorO ⊧ bas-Comβ must (clo-Form false)
ZorO-may-diverge = β-node (inj₂ (Omega-diverges' N must (clo-Form false)))

ZorO-par-must-1 : n-ZorO ⊧ bas-Comβ may (bas-Nat zero)
ZorO-par-must-1 = β-node ((record { β-force = β-leaf refl }) ,
  Omega-diverges' N may (bas-Nat zero))


-- Ong example

-- the value λx.Ω
thu-Omega : (τ : Aty) → A-term val (U τ)
thu-Omega = n-Omega

-- the computation λx.Ω (forced)
thu-Omega' : (τ : Aty) → A-cpt' (U τ)
force (thu-Omega' τ) = leaf (thu-Omega τ)

-- the value λx.λy.Ω
thu-thu-Omega : (τ : Aty) → A-term val (U (U τ))
thu-thu-Omega τ = leaf (thu-Omega τ)

-- the computation λx.λy.Ω (forced)
thu-thu-Omega' : (τ : Aty) → A-cpt' (U (U τ))
force (thu-thu-Omega' τ) = leaf (thu-thu-Omega τ)

-- the left term in example: λx.Ω or λx.λy.Ω : 1 → 1 → τ
Ong-left : (τ : Aty) →  A-term cpt (U (U τ))
Ong-left τ = node true (λ x → if (bitBool x) then (thu-Omega' (U τ)) else (thu-thu-Omega' τ))

-- the right term in example: λx.(Ω or λy.Ω)
Ong-right : (τ : Aty) → A-term cpt (U (U τ))
Ong-right τ = leaf ( node true (λ x → if (bitBool x) then (n-Omega' (U τ)) else (thu-Omega' τ)))

-- we show that they are different, and hence not bisimilar
Ong-diff : (τ : Aty) → A-form cpt (U (U τ))
Ong-diff τ = bas-Comα may (bas-Thu (neg-Form (bas-Comα may (clo-Form true))))

Ong-left⊧diff : (τ : Aty) → ((Ong-left τ) ⊧ (Ong-diff τ))
Ong-left⊧diff τ = node-α (inj₁ (leaf-α refl (Omega-diverges (U τ) may (clo-Form false))))

Ong-right⊧neg : (τ : Aty) → ((Ong-right τ) ⊧ (neg-Form (Ong-diff τ)))
Ong-right⊧neg τ = β-leaf (node-α (inj₂ (leaf-α refl tt)))

-- example showing the two terms are unrelated. Note that bisimilarity implies logical order
Ong-example : (τ : Aty) → (Log-Order cpt (U (U τ)) (Ong-left τ) (Ong-right τ)) → ⊥
Ong-example τ log = dist-Log (Ong-diff τ) (Ong-right τ)
  ((log (Ong-diff τ) (Ong-left⊧diff τ))) (Ong-right⊧neg τ)



-- The infinite number generator, num-gen : A-val (N ⇒ N)

may-even : (n : ℕ) → (pred-even n) → liftTree pred-even may (num-gen n)
may-even n hypo = node-α (inj₁ (leaf-α refl hypo))

may-even1 : (n : ℕ) → (pred-even (suc n)) → liftTree pred-even may (num-gen n)
may-even1 n hypo = node-α (inj₂ (node-α (inj₁ (leaf-α refl hypo))))

lem1 : (n : ℕ) → (pred-even n) ⊎ (pred-even (suc n))
lem1 zero = inj₁ pe-zero
lem1 (suc zero) = inj₂ (pe-ss zero pe-zero)
lem1 (suc (suc n))  with lem1 n
... | inj₁ x = inj₁ (pe-ss n x)
... | inj₂ y = inj₂ (pe-ss (suc n) y)

even-lem : (V : (A-val N)) → (pred-even V) → (V ⊧ even-Form)
even-lem zero hypo = zero , refl
even-lem (suc (suc V)) (pe-ss .V hypo) with even-lem V hypo
... | fst , snd = (suc fst) , (cong (λ x → suc (suc x)) snd)

may-evenA : (n : ℕ) → liftTree pred-even may (num-gen n)
may-evenA n  with lem1 n
... | inj₁ x = may-even n x
... | inj₂ y = may-even1 n y

may-even-formula : num-gen ⊧ clo-Form (⋀ (λ n → atom (bas-Fun n (bas-Comα may even-Form))))
may-even-formula n = monotone pred-even (λ V → Σ ℕ (λ n₁ → V ≡ N-twice n₁))
  even-lem (num-gen n)
  may (may-evenA n)

may-diverge : num-gen ⊧
  clo-Form (⋀ (λ n → atom (bas-Fun n (bas-Comβ must (clo-Form false)))))
may-diverge' : (n : ℕ) → β-liftTree' (λ x → ⊥) must (num-gen n)
may-diverge n = β-node (inj₂ (may-diverge' (suc n)))
β-force (may-diverge' n) = may-diverge n

