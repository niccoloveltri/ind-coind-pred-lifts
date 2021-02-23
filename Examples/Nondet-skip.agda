module Examples.Nondet-skip where

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
--   NONDETERMINISM, convex
-- ==============================================



data n-obs : Set where
  may : n-obs
  must : n-obs

n-leaf : n-obs → Bool
n-leaf o = true

n-bode : (k : BSig) → n-obs → Test ((BAr k) × n-obs)
n-bode b-or may = (atom (true , may)) ∨ (atom (false , may))
n-bode b-or must = (atom (true , must)) ∧ (atom (false , must))

n-delay : n-obs → Test n-obs
n-delay o = atom o

n-node : (k : BST-nodes) → n-obs → Test ((BST-arit k) × n-obs)
n-node (inj₁ x) c = n-bode x c
n-node (inj₂ tt) c = functorTest (λ x → tt , x) (n-delay c)


import Logic
open Logic BST-arit n-obs n-leaf n-node public

-- Example:

may-even : liftTree pred-even may (num-gen zero)
may-even = node-α (inj₁ (leaf-α refl pe-zero))

may-even1 : liftTree pred-even may (num-gen (suc zero))
may-even1 = node-α (inj₂ (node-α (inj₁ (leaf-α refl (pe-ss zero pe-zero)))))

may-diverge : (n : ℕ) → β-liftTree (λ x → ⊥) must (num-gen n)
may-diverge' : (n : ℕ) → β-liftTree' (λ x → ⊥) must (num-gen n)
may-diverge n = β-node (inj₂ (may-diverge' (suc n)))
β-force (may-diverge' n) = may-diverge n 

-- Decomposable:

-- may may => may
strong-may : (r : DTree ar⊥) → obsTower r may may → α may (μTree r)
strong-may (leaf x) (leaf-α x₁ x₂) = x₂
strong-may (node (inj₁ b-or) ts) (node-α (inj₁ x)) = node-α (inj₁ (strong-may (force (ts left)) x))
strong-may (node (inj₁ b-or) ts) (node-α (inj₂ y)) = node-α (inj₂ (strong-may (force (ts right)) y))
strong-may (node (inj₂ tt) ts) (node-α x) = node-α (strong-may (force (ts tt)) x)

strongβ-may : (r : DTree ar⊥) → (β-obsTower r may may) → β ∞ may (μTree r)
strongβ-may' : (r : DTree ar⊥) → (β-obsTower r may may) → β' ∞ may (μTree r)
strongβ-may (leaf x) (β-leaf x₁) = x₁
strongβ-may (node (inj₁ b-or) ts) (β-node (fst , snd)) =
  β-node ((strongβ-may' (force (ts true)) (β-force fst)) ,
  strongβ-may' (force (ts false)) (β-force snd))
strongβ-may (node (inj₂ tt) ts) (β-node x) =
  β-node (strongβ-may' (force (ts tt)) (β-force x))
β-force (strongβ-may' r hypo) = strongβ-may r hypo

-- may => may may
strong-may-inv : (r : DTree ar⊥) → α may (μTree r) → obsTower r may may
strong-may-inv (leaf x) = λ x₁ → leaf-α refl x₁
strong-may-inv (node (inj₁ b-or) ts) (node-α (inj₁ x)) = node-α (inj₁ (strong-may-inv (force (ts left)) x))
strong-may-inv (node (inj₁ b-or) ts) (node-α (inj₂ y)) = node-α (inj₂ (strong-may-inv ((force (ts right))) y))
strong-may-inv (node (inj₂ tt) ts) (node-α x) = node-α (strong-may-inv (force (ts tt)) x)

strongβ-may-inv : (r : DTree ar⊥) → β ∞ may (μTree r) → β-obsTower r may may
strongβ-may-inv' : (r : DTree ar⊥) → β ∞ may (μTree r) → β-obsTower' r may may
strongβ-may-inv (leaf x) hypo = β-leaf hypo
strongβ-may-inv (node (inj₁ b-or) ts) (β-node (fst , snd))
  = β-node ((strongβ-may-inv' (force (ts left)) (β-force fst)) ,
  (strongβ-may-inv' (force (ts right)) (β-force snd)))
strongβ-may-inv (node (inj₂ tt) ts) (β-node x) =
  β-node (strongβ-may-inv' (force (ts tt)) (β-force x))
β-force (strongβ-may-inv' r hypo) = strongβ-may-inv r hypo

-- must must => must
strong-must : (r : DTree ar⊥) → obsTower r must must → α must (μTree r)
strong-must (leaf x) (leaf-α x₁ x₂) = x₂
strong-must (node (inj₁ b-or) ts) (node-α (fst , snd)) = node-α ((strong-must (force (ts left)) fst) , (strong-must (force (ts right)) snd))
strong-must (node (inj₂ tt) ts) (node-α x) = node-α (strong-must (force (ts tt)) x)

-- must => must must
strong-must-inv : (r : DTree ar⊥) → α must (μTree r) → obsTower r must must
strong-must-inv (leaf x) pruf = leaf-α refl pruf
strong-must-inv (node (inj₁ b-or) ts) (node-α (fst , snd)) = node-α ((strong-must-inv (force (ts left)) fst) , (strong-must-inv (force (ts right)) snd))
strong-must-inv (node (inj₂ tt) ts) (node-α x) = node-α (strong-must-inv (force (ts tt)) x)

-- PROPOSITION:  may+must nondeterminism is strong decomposable
n-is-strong : Strong-Decomposable
n-is-strong r r' pruf may assum = strong-may r' (pruf may may (strong-may-inv r assum))
n-is-strong r r' pruf must assum = strong-must r' (pruf must must (strong-must-inv r assum))

-- Implications, α-must => α-may => β-must, α-must => β-may => β-must

must-imp-may : (t : PTree ar⊥) → (α must t) → (α may t)
must-imp-may (leaf P) (leaf-α L xP) = leaf-α refl xP
must-imp-may (node (inj₁ b-or) ts) (node-α (fst , snd)) = node-α (inj₁ (must-imp-may (force (ts true)) fst))
must-imp-may (node (inj₂ tt) ts) (node-α x) = node-α (must-imp-may (force (ts tt)) x)

imay-imp-imust : (t : PTree ar⊥) → (β ∞ may t) → (β ∞ must t)
imay-imp-imust' : (t : PTree ar⊥) → (β ∞ may t) → (β' ∞ must t)
imay-imp-imust (leaf P) (β-leaf xP) = β-leaf xP
imay-imp-imust (node (inj₁ b-or) ts) (β-node (fst , snd)) = β-node (inj₁ (imay-imp-imust' (force (ts true)) (β-force fst)))
imay-imp-imust (node (inj₂ tt) ts) (β-node x) = β-node (imay-imp-imust' (force (ts tt)) (β-force x))
β-force (imay-imp-imust' t hypo) = imay-imp-imust t hypo

may-imp-imust : (t : PTree ar⊥) → (α may t) → (β ∞ must t)
may-imp-imust' : (t : PTree ar⊥) → (α may t) → (β' ∞ must t)
may-imp-imust (leaf P) (leaf-α L xP) = β-leaf xP
may-imp-imust (node (inj₁ b-or) ts) (node-α (inj₁ x)) = β-node (inj₁ (may-imp-imust' (force (ts true)) x))
may-imp-imust (node (inj₁ b-or) ts) (node-α (inj₂ y)) = β-node (inj₂ (may-imp-imust' (force (ts false)) y))
may-imp-imust (node (inj₂ tt) ts) (node-α x) = β-node (may-imp-imust' (force (ts tt)) x)
β-force (may-imp-imust' t hypo) = may-imp-imust t hypo

must-imp-imay : (t : PTree ar⊥) → (α must t) → (β ∞ may t)
must-imp-imay' : (t : PTree ar⊥) → (α must t) → (β' ∞ may t)
must-imp-imay (leaf P) (leaf-α L xP) = β-leaf xP
must-imp-imay (node (inj₁ b-or) ts) (node-α (fst , snd)) = β-node (must-imp-imay' (force (ts true)) fst , must-imp-imay' (force (ts false)) snd)
must-imp-imay (node (inj₂ tt) ts) (node-α x) = β-node (must-imp-imay' (force (ts tt)) x)
β-force (must-imp-imay' t hypo) = must-imp-imay t hypo

must-imp-imust : (t : PTree ar⊥) → (α must t) → (β ∞ must t)
must-imp-imust t hypo = imay-imp-imust t (must-imp-imay t hypo)
-- must-imp-imust t hypo = may-imp-imust t (must-imp-may t hypo)


-- Equations (weird stuff when layering though...)
open bin-equations-skip n-obs n-leaf n-node

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
-- associativity 2 is very similar, plus derivable from symmetry and associativity 1

pribbles = V-subs (Strong-to-Normal n-is-strong) n-is-sym (λ n → leaf (pred-even n))


nat-even : ℕ → Bool
nat-odd : ℕ → Bool
nat-even zero = true
nat-even (suc n) = nat-odd n
nat-odd zero = false
nat-odd (suc n) = nat-even n

tree-drunk : {i : Size} → ℕ → STree BST-arit ℕ i
tree-drunk' : {i : Size} → ℕ → STree' BST-arit ℕ i
tree-drunk zero = leaf zero
tree-drunk (suc n) = node (inj₁ b-or) (λ x → if x
  then tree-drunk' n else tree-drunk' (suc (suc n)) )
force (tree-drunk' n) = tree-drunk n

tree-drunk-typed : A-val (N ⇒ N)
tree-drunk-typed = tree-drunk


may-fall-form : A-form val (N ⇒ N)
may-fall-form = clo-Form (⋀ (λ k →
  atom (bas-Fun k (bas-Comα may (clo-Form true)))))

drunk-may-fall : tree-drunk-typed ⊧ may-fall-form
drunk-may-fall zero = leaf-α refl tt
drunk-may-fall (suc n) = node-α (inj₁ (drunk-may-fall n))


drunk-may-wander : ∀ (n : ℕ) → β-liftTree (λ n → ⊥) must
  (tree-drunk (suc n))
drunk-may-wander' : ∀ (n : ℕ) → β-liftTree' (λ n → ⊥) must
  (tree-drunk (suc n))
drunk-may-wander n = β-node (inj₂ (drunk-may-wander' ((suc n))))
β-force (drunk-may-wander' n) = drunk-may-wander n

fall-evenly : A-form val (N ⇒ N)
fall-evenly = clo-Form (⋀ (λ x → atom (bas-Fun (N-twice x)
  (bas-Comβ may even-Form))))
drunk-falls-evenly : ∀ (n : ℕ) → (N-even n) → β-liftTree (N-even) may (tree-drunk n)
drunk-falls-evenly' : ∀ (n : ℕ) → (N-even n) → β-liftTree' (N-even) may (tree-drunk n)
drunk-falls-evenly zero neven = β-leaf neven
drunk-falls-evenly (suc zero) ()
drunk-falls-evenly (suc (suc (fst))) neven = β-node (
  (record { β-force = β-node (
    (drunk-falls-evenly' fst neven) ,
    (drunk-falls-evenly' (suc (suc fst)) neven)) }) ,
  (record { β-force = β-node (
    (drunk-falls-evenly' (suc (suc fst)) neven) ,
    (drunk-falls-evenly' (suc (suc (suc (suc fst)))) neven)) }))
β-force (drunk-falls-evenly' n neven) = drunk-falls-evenly n neven

drunk-falls-evenly-form : tree-drunk-typed ⊧ fall-evenly
drunk-falls-evenly-form n = β-monotone N-even (λ V → V ⊧ even-Form)
  even-equiv-l (tree-drunk (N-twice n)) may (drunk-falls-evenly (N-twice n) (N-twice-even n))

--   Pred-Lift.β-node
--     ((record { β-force = Pred-Lift.β-node (
--       (drunk-falls-evenly' fst ?) ,
--       (drunk-falls-evenly' (suc (suc fst)) ?)) }) ,
--     record { β-force = Pred-Lift.β-node (
--       (drunk-falls-evenly' (suc (suc fst)) ?) ,
--       (drunk-falls-evenly' (suc (suc (suc (suc fst)))) (pe-ss ? ?))) }
--     )
-- β-force (drunk-falls-evenly' n neven) = drunk-falls-evenly n neven
     
-- -- drunk-falls-evenly-form : tree-drunk-typed ⊧ fall-evenly
-- -- drunk-falls-evenly-form' : (n : ℕ)
-- --   → β-liftTree (λ V → Σ ℕ (λ n₁ → V ≡ nat-twice n₁)) may
-- --       (tree-drunk-typed (nat-twice n))
-- -- drunk-falls-evenly-form n = {!!}
