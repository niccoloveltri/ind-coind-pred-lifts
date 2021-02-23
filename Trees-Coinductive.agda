module Trees-Coinductive where

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


-- Function extensionality
postulate 
  extensionality : {X : Set} → {Y : X -> Set} → 
                  ∀{f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

-- ==============================================
--   COINDUCTIVE TREES
-- ==============================================

data Token {ℓ} : Set ℓ where
  more : Token

FinTree :  ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ} (I : K → Set ℓ₁) (A : Set ℓ₂) (n : ℕ) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
FinTree I A zero = Token
FinTree I A (suc n) = A ⊎ (Σ _ λ op → (I op) → FinTree I A n)


mutual
  data STree {ℓ ℓ₁ ℓ₂} {K : Set ℓ} (I : K → Set ℓ₂) (A : Set ℓ₁) (i : Size) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    leaf : (x : A) → STree I A i
    node : (k : K) (ts : I k → STree' I A i) → STree I A i

  record STree' {ℓ ℓ₁ ℓ₂} {K : Set ℓ} (I : K → Set ℓ₂) (A : Set ℓ₁) (i : Size) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      force : {j : Size< i} → STree I A j
  
open STree' public

data ITree {ℓ ℓ₁ ℓ₂} {K : Set ℓ} (I : K → Set ℓ₂) (A : Set ℓ₁) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
  in-more : ITree I A
  in-leaf : (x : A) → ITree I A
  in-node : (op : K) (ts : I op → ITree I A) → ITree I A


Tree : ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ} (I : K → Set ℓ₁) (A : Set ℓ₂) → Set _
Tree I A = STree I A ∞

PTree : {K : Set} (I : K → Set) → Set₁
PTree I = Tree I Set

DTree : {K : Set} (I : K → Set) → Set₁
DTree I = Tree I (PTree I)

VTree : {K : Set} (I : K → Set) → Set
VTree I = Tree I ℕ

AppTree : ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ} {I : K → Set ℓ₁} {A : Set ℓ₂} (t : Tree I A) (n : ℕ) → (FinTree I A n)
AppTree t zero = more
AppTree (leaf x) (suc n) = inj₁ x
AppTree (node op ts) (suc n) = inj₂ (op , (λ i → AppTree (force (ts i)) n))


-- Bisimilarity

mutual
  data Bisim {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} (i : Size) : Tree I A → Tree I A → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    leaf-eq : {x y : A} → (x ≡ y) → (Bisim i (leaf x) (leaf y))
    node-eq : ∀ {k ts ts'} → ((j : I k) → (Bisim' i (force (ts j)) (force (ts' j)))) → Bisim i (node k ts) (node k ts')

  record Bisim' {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} (i : Size) (t t' : Tree I A)  :  Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      force-eq : {j : Size< i} → Bisim j t t'

open Bisim' public

_∼_ :  ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} → Tree I A → Tree I A → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
t ∼ t' = Bisim ∞ t t'

postulate
  coin-prince :  ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} {t t' : Tree I A } →  t ∼ t' → (t ≡ t')


-- Coinductive trees as a functor

mapTree : ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {i : Size}
  → (A → B) → STree I A i → STree I B i
mapTree' : ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {i : Size}
  → (A → B) → STree' I A i → STree' I B i

mapTree f (leaf x) = leaf (f x)
mapTree f (node k ts) = node k (mapTree' f ∘ ts)

force (mapTree' f t) = mapTree f (force t)


-- mapTree preserves function composition (seems to need function extensionality)
funcomTree :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄} {K : Set ℓ₄} {I : K → Set ℓ₃} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} {i : Size}
           (f : A → B) (g : B → C) (t : Tree I A) → Bisim i (mapTree g (mapTree f t)) (mapTree (λ x → g (f x)) t)
funcomTree' :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄} {K : Set ℓ₄} {I : K → Set ℓ₃} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} {i : Size}
            (f : A → B) (g : B → C) (t : Tree I A) → Bisim' i (mapTree g (mapTree f t)) (mapTree (λ x → g (f x)) t)
funcomTree f g (leaf x) = leaf-eq refl
funcomTree f g (node k ts) = node-eq (λ j → funcomTree' f g (force (ts j)))
force-eq (funcomTree' f g t) = funcomTree f g t

functTree :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄} {K : Set ℓ₄} {I : K → Set ℓ₃} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂}
          (f : A → B) (g : B → C) (t : Tree I A) → (mapTree g (mapTree f t)) ≡ (mapTree (λ x → g (f x)) t)
functTree f g t = coin-prince (funcomTree f g t)


-- Monad structure
ηTree : ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {A : Set ℓ} (I : K → Set ℓ₁) → A → Tree I A
ηTree I a = leaf a

μTree : ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} {i : Size}
  → STree I (Tree I A) i → STree I A i
μTree' : ∀ {ℓ ℓ₁ ℓ₂} {K : Set ℓ₂} {I : K → Set ℓ₁} {A : Set ℓ} {i : Size}
  → STree' I (Tree I A) i → STree' I A i

μTree (leaf t) = t
μTree (node k ts) = node k (μTree' ∘ ts)

force (μTree' t) = μTree (force t)

-- η is a natural transformation
η-is-nat :  ∀ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {K : Set ℓ₂} (I : K → Set ℓ₁) (f : A → B) (a : A) → (ηTree I (f a) ≡ mapTree f (ηTree I a))
η-is-nat f I a = refl

-- μ is a natural transformation
μ-is-nat :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {i : Size} (f : A → B) (t : Tree I (Tree I A))
         → Bisim i (mapTree f (μTree t)) (μTree (mapTree (mapTree f) t))
μ-is-nat' :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {i : Size} (f : A → B) (t : Tree I (Tree I A))
         → Bisim' i (mapTree f (μTree t)) (μTree (mapTree (mapTree f) t))
μ-is-nat f (leaf (leaf x)) = leaf-eq refl
μ-is-nat f (leaf (node k ts)) = node-eq (λ j → μ-is-nat' f (leaf (force (ts j))))
μ-is-nat f (node k ts) = node-eq (λ j → μ-is-nat' f (force (ts j)))
force-eq (μ-is-nat' f t) = μ-is-nat f t 

μ-natural :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} (f : A → B) (t : Tree I (Tree I A)) →
          (mapTree f (μTree t)) ≡ (μTree (mapTree (mapTree f) t))
μ-natural f t = coin-prince (μ-is-nat f t)


η-μ-law1 :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {i : Size} (t : (Tree I A))
         →  t ≡ (μTree (ηTree I t))
η-μ-law1 t = refl

η-μ-law2-bis :  ∀ {ℓ ℓ₂ ℓ₃} {K : Set ℓ₃} {A : Set ℓ} {i : Size} {I : K → Set ℓ₂} (t : (Tree I A))
         →  Bisim i t (μTree (mapTree (ηTree I) t))
η-μ-law2-bis' :  ∀ {ℓ ℓ₂ ℓ₃} {K : Set ℓ₃} {A : Set ℓ} {i : Size} {I : K → Set ℓ₂} (t : (Tree I A))
         →  Bisim' i t (μTree (mapTree (ηTree I) t))
η-μ-law2-bis (leaf x) = leaf-eq refl
η-μ-law2-bis (node k ts) = node-eq (λ op → η-μ-law2-bis' (force (ts op)))
force-eq (η-μ-law2-bis' t) = η-μ-law2-bis t

η-μ-law2 :  ∀ {ℓ ℓ₂ ℓ₃} {K : Set ℓ₃} {A : Set ℓ} {i : Size} {I : K → Set ℓ₂} (t : (Tree I A))
         → t ≡ (μTree (mapTree (ηTree I) t))
η-μ-law2 t = coin-prince (η-μ-law2-bis t)


KleisTree :  ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ₃} {I : K → Set ℓ₂} {A : Set ℓ} {B : Set ℓ₁}
          (f : A → Tree I B) (t : Tree I A) → Tree I B
KleisTree f t = μTree (mapTree f t)

-- The finality of the coalgebra of trees
unfoldTree : ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ} {I : K → Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃}
  → (C → A ⊎ Σ K λ k → I k → C)
  → C → Tree I A
unfoldTree' : ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {K : Set ℓ} {I : K → Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃}
  → (C → A ⊎ Σ K λ k → I k → C)
  → C → STree' I A ∞
unfoldTree f c with f c
... | inj₁ a = leaf a
... | inj₂ (k , cs) = node k λ i → unfoldTree' f (cs i)
force (unfoldTree' f c) = unfoldTree f c


