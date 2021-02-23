open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool hiding (_∧_; _∨_)

module Pred-Lift-a {K : Set} (I : K → Set)
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
--   O-INDEXED PREDICATE LIFTINGS (inductive)
-- ==============================================

-- Inductive O-indexed algebras on coinductive trees
data α : O → PTree I → Set where
  leaf-α : ∀ {P o} → (πl o ≡ true) → P → α o (leaf P) 
  node-α : ∀ {k ts o}
    → liftTest (uncurry (λ x o' → α o' (force (ts x)))) (πn k o)
    → α o (node k ts)

-- Inductive O-indexed predicate lifting to coinductive trees
liftTree : ∀ {ℓ} {A : Set ℓ} → (A → Set) → O → Tree I A → Set
liftTree P o t = α o (mapTree P t)

-- Basic ordering on predicate trees using α
_⊏_ : PTree I → PTree I → Set
t ⊏ t' = (o : O) → α o t → α o t'


-- α is monotone
mono-leaf : (A B : Set) → (f : A → B) → (leaf A ⊏ leaf B)
mono-leaf A B f o (leaf-α x a) = leaf-α x (f a)
mono-node : (k : K) (f g : I k → Set) → ((i : I k) → (f i) → (g i))
  → (node k (λ i → record {force = leaf (f i)} ) ⊏
     node k (λ i → record {force = leaf (g i)}))
mono-node k f g pruf o (node-α x) =
  node-α (liftfunTest _ (uncurry (λ x₁ o' → α o' (leaf (f x₁))))
         (uncurry (λ x₁ o' → α o' (leaf (g x₁)))) (πn k o)
         (λ a x₁ → (mono-leaf (f (proj₁ a)) (g (proj₁ a)) (pruf (proj₁ a)) (proj₂ a)) x₁) x)
mono-node2 : (k : K) (f g : I k → PTree I) → ((i : I k) → (f i) ⊏ (g i))
  → (node k (λ i → record {force = (f i)} ) ⊏ node k (λ i → record {force = (g i)}))
mono-node2 k f g pruf o (node-α x) = node-α (liftfunTest _ (uncurry (λ x₁ o' → α o' (f x₁)))
                                         (uncurry (λ x₁ o' → α o' (g x₁))) (πn k o)
                                         (λ a x₁ → pruf (proj₁ a) (proj₂ a) x₁) x)

mono-help : {A : Set} {k : K} (os : Test (I k × O)) (f g : A → Set)
  (ord : (a : A) → f a → g a) (ts : I k → Tree I A)
          (x : liftTest (uncurry (λ x₁ o' → α o' (mapTree f (ts x₁)))) (os))
          → liftTest (uncurry (λ x₁ o' → α o' (mapTree g (ts x₁)))) (os)
monotone : {A : Set} → (f g : A → Set) → ((a : A) → (f a) → (g a)) → (t : Tree I A) →
  ((mapTree f t) ⊏ (mapTree g t))

mono-help (atom (i , o)) f g ord ts x = monotone f g ord (ts i) o x
mono-help (os ∧ os₁) f g ord ts (fst , snd) =
  (mono-help os f g ord ts fst) , (mono-help os₁ f g ord ts snd)
mono-help (os ∨ os₁) f g ord ts (inj₁ x) = inj₁ (mono-help os f g ord ts x)
mono-help (os ∨ os₁) f g ord ts (inj₂ y) = inj₂ (mono-help os₁ f g ord ts y)
mono-help true f g ord ts tt = tt
mono-help (⋁ x₁) f g ord ts (n , x) = n , mono-help (x₁ n) f g ord ts x
mono-help (⋀ x₁) f g ord ts hypo = λ n → mono-help (x₁ n) f g ord ts (hypo n)

monotone f g assum (leaf x) o (leaf-α x₁ x₂) = leaf-α x₁ (assum x x₂)
monotone f g assum (node k ts) o (node-α x) =
  node-α (mono-help (πn k o) f g assum (λ i → force (ts i)) x)


-- Monotonicity of α extended to tests of oberservations Test O
base-test-lift : (t₁ t₂ : PTree I)  → (t₁ ⊏ t₂) → (os : Test O) →
  (liftTest (λ o' → α o' t₁) os) → (liftTest (λ o' → α o' t₂) os)
base-test-lift t₁ t₂ x (atom o) t₁Mos = x o t₁Mos
base-test-lift t₁ t₂ x (os ∧ os₁) (fst , snd) =
  (base-test-lift t₁ t₂ x os fst) , base-test-lift t₁ t₂ x os₁ snd
base-test-lift t₁ t₂ x (os ∨ os₁) (inj₁ y) = inj₁ (base-test-lift t₁ t₂ x os y)
base-test-lift t₁ t₂ x (os ∨ os₁) (inj₂ y) = inj₂ (base-test-lift t₁ t₂ x os₁ y)
base-test-lift t₁ t₂ x true tt = tt
base-test-lift t₁ t₂ x (⋁ x₁) (fst , snd) = fst , (base-test-lift t₁ t₂ x (x₁ fst) snd)
base-test-lift t₁ t₂ x (⋀ x₁) hypo = λ n → base-test-lift t₁ t₂ x (x₁ n) (hypo n)


-- =================================================
-- Sequencing and the study of higher-order programs

-- Double observations for double trees, for describing higher order programs
obsTower : DTree I → O → O → Set
obsTower r o o' = α o (mapTree (α o') r)

-- Basic ordering on double trees
_⊂_ : DTree I → DTree I → Set
r ⊂ r' = (o : O) (os : Test O)
  → α o (mapTree (λ t → liftTest (λ o' → α o' t) os) r)
  → α o (mapTree (λ t → liftTest (λ o' → α o' t) os) r')

-- Preservation of basic orderings over the monadic multiplication map
Decomposable : Set₁
Decomposable =
  (r r' : DTree I) → (r ⊂ r') → ((μTree r) ⊏ (μTree r'))

-- A subrelation of ⊂ is determined by towers
gen-to-tower : (r : DTree I) → (r' : DTree I) → (r ⊂ r') → (o o' : O) →
  obsTower r o o' → obsTower r' o o'
gen-to-tower r r' hypo o o' assum = hypo o (atom o') assum

-- Stronger preservation over μ, requiring only double observations
-- Note: in the paper, strong decomposability for α and β are combined into one
Strong-Decomposable : Set₁
Strong-Decomposable =
  (r r' : DTree I)
  → ((o o' : O) → obsTower r o o' → obsTower r' o o')
  → μTree r ⊏ μTree r'

-- Strong implies normal decomposable
Strong-to-Normal : Strong-Decomposable → Decomposable
Strong-to-Normal hypo
  r r' x o x₁ = hypo r r' (gen-to-tower r r' x) o x₁


-- ====================================================================
-- General relation on variable expressions given by coinductive trees
-- These allow us to describe algebraic equations for algebraic effects
_◄_ : VTree I → VTree I → Set₁
e ◄ e' = (P : ℕ → Set) (o : O) → liftTree P o e → liftTree P o e'
_■_ : VTree I → VTree I → Set₁
e ■ e' = (e ◄ e') × (e' ◄ e)

-- Substitution in variable expressions generates related double trees
V-tower : (e : VTree I) → (e' : VTree I) → (e ◄ e') → (f : ℕ → PTree I) →
  ((mapTree f e) ⊂ (mapTree f e'))
V-tower e e' hypo f o os assum = subst (λ x → α o x)
        (sym (functTree f (λ t → liftTest (λ o' → α o' t) os) e'))
        (hypo (λ t → liftTest (λ o' → α o' (f t)) os) o (subst (α o)
        (functTree f (λ t → liftTest (λ o' → α o' t) os) e) assum))

-- Substitutivity (needs functoriality of mapsTree, which needs function extensionality)

V-subs : Decomposable → {e : VTree I} → {e' : VTree I} → (e ◄ e') → (f : ℕ → PTree I) →
  ((KleisTree f e) ⊏ (KleisTree f e'))
V-subs decom hypo f = decom (mapTree f _) (mapTree f _) (V-tower _ _ hypo f)

-- Complete subsitutivity
V-subst :  Decomposable → (e : VTree I) → (e' : VTree I) → (e ◄ e') → (g : ℕ → VTree I) →
  ((KleisTree g e) ◄ (KleisTree g e'))
V-subst decom e e' hypo g P o assum = subst (α o) (sym (μ-natural P (mapTree g e')))
        (subst (λ r → α o (μTree r)) (sym (functTree g (mapTree P) e'))
        (V-subs decom hypo (λ n → mapTree P (g n)) o
        (subst (λ r → α o (μTree r)) (functTree g (mapTree P) e)
        (subst (α o) (μ-natural P (mapTree g e)) assum))))

-- Subsituting related values in related expressions gives related double trees
V-tower-cong : (e : VTree I) → (e' : VTree I) → (e ◄ e') → (f g : ℕ → PTree I) →
  ((n : ℕ) → (f n) ⊏ (g n)) → ((mapTree f e) ⊂ (mapTree g e'))
V-tower-cong e e' hypo f g rel o os assum = subst (λ x → α o x)
        (sym (functTree g (λ t → liftTest (λ o' → α o' t) os) e'))
        (hypo (λ t → liftTest (λ o' → α o' (g t)) os) o
        (monotone ( λ t → liftTest (λ o' → α o' (f t)) os)
        (λ t → liftTest (λ o' → α o' (g t)) os)
          (λ a x → liftfunTest _ ((λ o' → α o' (f a)))
          ((λ o' → α o' (g a))) os (λ a₁ → rel a a₁) x) e o
        (subst (λ x → α o x)
           (functTree f (λ t → liftTest (λ o' → α o' t) os) e) assum)))

-- Congruence: Variable relation is preserved under subsitution
V-cong-help : Decomposable → {e : VTree I} → {e' : VTree I} → (e ◄ e') →
  (f g : ℕ → PTree I) → ((n : ℕ) → (f n) ⊏ (g n)) → ((KleisTree f e) ⊏ (KleisTree g e'))
V-cong-help decom hypo f g assum = decom (mapTree f _) (mapTree g _)
  (V-tower-cong _ _ hypo f g assum)

V-cong :  Decomposable → (e : VTree I) → (e' : VTree I) → (e ◄ e') → (F G : ℕ → VTree I) →
  ((n : ℕ) → (F n) ◄ (G n)) → ((KleisTree F e) ◄ (KleisTree G e'))
V-cong decom e e' hypo F G ord P o assum = subst (α o) (sym (μ-natural P (mapTree G e')))
        (subst (λ r → α o (μTree r)) (sym (functTree G (mapTree P) e'))
        (V-cong-help decom hypo (λ n → mapTree P (F n)) (λ n → mapTree P (G n))
        (λ n → (ord n P)) o
        (subst (λ r → α o (μTree r)) (functTree F (mapTree P) e)
        (subst (α o) (μ-natural P (mapTree F e)) assum))))


-- =================================================
-- Explicit decomposition of sequential satisfaction
-- For showing decomposability

deco : Set
deco = O → Test (O × O)

deco-α : deco → O → DTree I → Set
deco-α πd o d = liftTest (λ x → obsTower d (proj₁ x) (proj₂ x)) (πd o)

-- Two properties for deco to be an α-decomposition
deco-α-seq : deco → Set₁
deco-α-seq πd = (o : O) → (d : DTree I) → (deco-α πd o d) → (α o (μTree d))

deco-α-unf : deco → Set₁
deco-α-unf πd = (o : O) → (d : DTree I)  → (α o (μTree d)) → (deco-α πd o d)

-- α-decompositions show decomposability
deco-α-decomp : (πd : deco) → (deco-α-seq πd) → (deco-α-unf πd)
  → Strong-Decomposable
deco-α-decomp πd rig lef d₁ d₂ d₁-d₂ o d₁-o = rig o d₂
  (liftfunTest (O × O) (λ x → α (proj₁ x) (mapTree (α (proj₂ x)) d₁))
     (λ x → α (proj₁ x) (mapTree (α (proj₂ x)) d₂)) (πd o)
     (λ p → d₁-d₂ (proj₁ p) (proj₂ p)) (lef o d₁ d₁-o))
