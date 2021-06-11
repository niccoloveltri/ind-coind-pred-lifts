open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool hiding (_∧_; _∨_)

module Pred-Lift-b {K : Set} (I : K → Set)
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

-- ==============================================
--   O-INDEXED PREDICATE LIFTINGS (coinductive)
-- ==============================================

-- O-indexed coinductive algebras on coinductive trees
mutual
  data β (i : Size) : O →  PTree I → Set where
    β-leaf : ∀ {P o} → P → β i o (leaf P)
    β-exep : ∀ {P o} → (πl o ≡ false) → β i o (leaf P)
    β-node : ∀ {k ts o}
      → liftTest (uncurry (λ x o' → β' i o' (force (ts x)))) (πn k o)
      → β i o (node k ts)

  record β' (i : Size) (o : O) (t : PTree I) : Set where
    coinductive
    field
      β-force : {j : Size< i} → β j o t

open β' public

-- O-induced coinductive predicate lifting by β
β-liftTree : ∀ {ℓ} {A : Set ℓ} → (A → Set) → O → Tree I A → Set
β-liftTree' : ∀ {ℓ} {A : Set ℓ} → (A → Set) → O → Tree I A → Set
β-liftTree P o t = β ∞ o (mapTree P t)
β-liftTree' P o t = β' ∞ o (mapTree P t)

-- Basic ordering induced by β
_β⊏_ : PTree I → PTree I → Set
t β⊏ t' = (o : O) → β ∞ o t → β ∞ o t'
_β'⊏_ : PTree I → PTree I → Set
t β'⊏ t' = (o : O) → β ∞ o t → β' ∞ o t'

-- β is monotone as predicate lifting
β-mono-help' : {A : Set} {k : K} (os : Test (I k × O)) (f g : A → Set)
  (ord : (a : A) → f a → g a) (ts : I k → Tree I A)
          (x : liftTest (uncurry (λ x₁ o' → β' ∞ o' (mapTree f (ts x₁)))) (os))
          → liftTest (uncurry (λ x₁ o' → β' ∞ o' (mapTree g (ts x₁)))) (os)
β-monotone : {A : Set} → (f g : A → Set) → ((a : A) → (f a) → (g a)) → (t : Tree I A) →
  ((mapTree f t) β⊏ (mapTree g t))
β-monotone' : {A : Set} → (f g : A → Set) → ((a : A) → (f a) → (g a)) → (t : Tree I A) →
  ((mapTree f t) β'⊏ (mapTree g t))
β-monotone f g f-g (leaf P) o (β-leaf xfP) = β-leaf (f-g P xfP)
β-monotone f g f-g (leaf P) o (β-exep -L) = β-exep -L
β-monotone f g f-g (node k ts) o (β-node x) =
  β-node (β-mono-help' (πn k o) f g f-g (λ i → force (ts i)) x)
β-force (β-monotone' f g f-g t o left) = β-monotone f g f-g t o left
β-mono-help' (atom x) f g ord ts left =
  β-monotone' f g ord (ts (proj₁ x)) (proj₂ x) (β-force left)
β-mono-help' (os ∧ os₁) f g ord ts (fst , snd) =
  (β-mono-help' os f g ord ts fst) , (β-mono-help' os₁ f g ord ts snd)
β-mono-help' (os ∨ os₁) f g ord ts (inj₁ x) = inj₁ (β-mono-help' os f g ord ts x)
β-mono-help' (os ∨ os₁) f g ord ts (inj₂ y) = inj₂ (β-mono-help' os₁ f g ord ts y)
β-mono-help' true f g ord ts left = tt
β-mono-help' (⋁ x) f g ord ts (n , C) = n , (β-mono-help' (x n) f g ord ts C)
β-mono-help' (⋀ x) f g ord ts left = λ n → β-mono-help' (x n) f g ord ts (left n)


-- ===================================================================
-- Studying higher order programs with β: preservation over sequencing

-- Double observations given by β
β-obsTower : DTree I → O → O → Set
β-obsTower r o o' = β ∞ o (mapTree (β ∞ o') r)
β-obsTower' : DTree I → O → O → Set
β-obsTower' r o o' = β' ∞ o (mapTree (β ∞ o') r)

-- Basic β ordering on double trees
_β⊂_ : DTree I → DTree I → Set
r β⊂ r' = (o : O) (os : Test O)
  → β ∞ o (mapTree (λ t → liftTest (λ o' → β ∞ o' t) os) r)
  → β ∞ o (mapTree (λ t → liftTest (λ o' → β ∞ o' t) os) r')
_β'⊂_ : DTree I → DTree I → Set
r β'⊂ r' = (o : O) (os : Test O)
  → β ∞ o (mapTree (λ t → liftTest (λ o' → β ∞ o' t) os) r)
  → β' ∞ o (mapTree (λ t → liftTest (λ o' → β ∞ o' t) os) r')

-- Notion of decomposability for β: preservation over sequencing
β-Decomposable : Set₁
β-Decomposable =
  (r r' : DTree I) → (r β⊂ r') → ((μTree r) β⊏ (μTree r'))

β-gen-to-tower : (r : DTree I) → (r' : DTree I) → (r β⊂ r') → (o o' : O) →
  β-obsTower r o o' → β-obsTower r' o o'
β-gen-to-tower r r' hypo o o' assum = hypo o (atom o') assum

-- Strong decomposability for β
β-Strong-Decomposable : Set₁
β-Strong-Decomposable =
  (r r' : DTree I)
  → ((o o' : O) → β-obsTower r o o' → β-obsTower r' o o')
  → μTree r β⊏ μTree r'

β-Strong-to-Normal : β-Strong-Decomposable → β-Decomposable
β-Strong-to-Normal hypo
  r r' x o x₁ = hypo r r' (β-gen-to-tower r r' x) o x₁


-- Explicit β-decomposition
deco' : Set
deco' = O → Test (O × O)

deco-β : deco' → O → DTree I → Set
deco-β πd o d = liftTest (λ x → β-obsTower d (proj₁ x) (proj₂ x)) (πd o)
deco-β' : deco' → O → DTree I → Set
deco-β' πd o d = liftTest (λ x → β-obsTower' d (proj₁ x) (proj₂ x)) (πd o)

-- Two properties showing that πd is a β-decomposition
deco-β-seq : deco' → Set₁
deco-β-seq' : deco' → Set₁
deco-β-seq πd = (o : O) → (d : DTree I) → (deco-β πd o d) → (β ∞ o (μTree d))
deco-β-seq' πd = (o : O) → (d : DTree I) → (deco-β πd o d) → (β' ∞ o (μTree d))

deco-β-unf : deco' → Set₁
deco-β-unf' : deco' → Set₁
deco-β-unf πd = (o : O) → (d : DTree I)  → (β ∞ o (μTree d)) → (deco-β πd o d)
deco-β-unf' πd = (o : O) → (d : DTree I)  → (β ∞ o (μTree d)) → (deco-β' πd o d)

-- β-decompositions imply strong decomposability
deco-β-decomp : (πd : deco') → (deco-β-seq πd) → (deco-β-unf πd)
  → β-Strong-Decomposable
deco-β-decomp πd rig lef d₁ d₂ d₁-d₂ o d₁-o = rig o d₂
  (liftfunTest (O × O) (λ x → β ∞ (proj₁ x) (mapTree (β ∞ (proj₂ x)) d₁))
     (λ x → β ∞ (proj₁ x) (mapTree (β ∞ (proj₂ x)) d₂)) (πd o)
     (λ p → d₁-d₂ (proj₁ p) (proj₂ p)) (lef o d₁ d₁-o))
