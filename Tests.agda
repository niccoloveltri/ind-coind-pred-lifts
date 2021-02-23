module Tests where

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
open import Axiom.Extensionality.Propositional

postulate funext : ∀ {a b} → Axiom.Extensionality.Propositional.Extensionality a b

data Test (A : Set) : Set where
  atom : A → Test A
  _∧_ _∨_ : Test A → Test A → Test A
  true false : Test A
  ⋁ : (ℕ → Test A) → Test A
  ⋀ : (ℕ → Test A) → Test A
--  ∁ : Set → Test A

-- Proof relevant Sierpinski space
§ = Test ⊥

boolTest : {A : Set} → Bool → Test A
boolTest false = false
boolTest true = true

boolSet : Bool → Set
boolSet false = ⊥
boolSet true = ⊤

liftTest : {A : Set} → (A → Set) → Test A → Set
liftTest f (atom a) = f a
liftTest f (T₁ ∧ T₂) = liftTest f T₁ × liftTest f T₂
liftTest f (T₁ ∨ T₂) = liftTest f T₁ ⊎ liftTest f T₂
liftTest f true = ⊤
liftTest f false = ⊥
liftTest f (⋁ T) = ∃ λ n → liftTest f (T n)
liftTest f (⋀ T) = (n : _) → liftTest f (T n)
-- liftTest f (∁ P) = P

-- Functor test
functorTest : {A B : Set} → (f : A → B) → (Test A) → (Test B)
functorTest f (atom x) = atom (f x)
functorTest f (x ∧ x₁) = (functorTest f x) ∧ (functorTest f x₁)
functorTest f (x ∨ x₁) = (functorTest f x) ∨ (functorTest f x₁)
functorTest f true = true
functorTest f false = false
functorTest f (⋁ x) = ⋁ (λ n → functorTest f (x n))
functorTest f (⋀ x) = ⋀ (λ n → functorTest f (x n))
-- functorTest f (∁ x) = ∁ x

-- Monad structure

KleisTest : {A B : Set} → (A → Test B) → (Test A) → (Test B)
KleisTest f (atom x) = f x
KleisTest f (tes ∧ tes₁) = KleisTest f tes ∧ KleisTest f tes₁
KleisTest f (tes ∨ tes₁) = (KleisTest f tes) ∨ (KleisTest f tes₁)
KleisTest f true = true
KleisTest f false = false
KleisTest f (⋁ x) = ⋁ (λ x₁ → KleisTest f (x x₁))
KleisTest f (⋀ x) = ⋀ (λ x₁ → KleisTest f (x x₁))

strengTest : {A B : Set} → Test A × B → Test (A × B)
strengTest (atom x , b) = atom (x , b)
strengTest ((tes ∧ tes₁) , b) =
  (strengTest (tes , b)) ∧ (strengTest (tes₁ , b))
strengTest ((tes ∨ tes₁) , b) =
  (strengTest (tes , b)) ∨ (strengTest (tes₁ , b))
strengTest (true , b) = true
strengTest (false , b) = false
strengTest (⋁ x , b) = ⋁ (λ x₁ → strengTest (x x₁ , b))
strengTest (⋀ x , b) = ⋀ (λ x₁ → strengTest (x x₁ , b))


-- Lifttor

liftfunTest : (A : Set) → (P : A → Set) → (Q : A → Set) → (os : Test A) → ((a : A) → ((P a) → (Q a))) → (liftTest P os) → liftTest Q os
liftfunTest A P Q (atom x) pruf assum = pruf x assum
liftfunTest A P Q (os ∧ os₁) pruf (fst , snd) = (liftfunTest _ P Q os pruf fst) , (liftfunTest _ P Q os₁ pruf snd)
liftfunTest A P Q (os ∨ os₁) pruf (inj₁ x) = inj₁ (liftfunTest _ P Q os pruf x)
liftfunTest A P Q (os ∨ os₁) pruf (inj₂ y) = inj₂ (liftfunTest _ P Q os₁ pruf y)
liftfunTest A P Q true pruf tt = tt
liftfunTest A P Q (⋁ x) pruf (n , assum) = n , (liftfunTest _ P Q (x n) pruf assum)
liftfunTest A P Q (⋀ x) pruf hypo = λ n → liftfunTest _ P Q (x n) pruf (hypo n)
-- liftfunTest P Q (∁ x) pruf assum = assum

liftnatTest : {A B : Set} → (f : A → B) → (P : B → Set) → (tes : Test A) → (liftTest (λ x → (P (f x))) tes) ≡ (liftTest P (functorTest f tes))
liftnatTest f P (atom x) = refl
liftnatTest f P (tes ∧ tes₁) = cong₂ _×_ (liftnatTest f P tes) (liftnatTest f P tes₁)
liftnatTest f P (tes ∨ tes₁) = cong₂ _⊎_ (liftnatTest f P tes) (liftnatTest f P tes₁)
liftnatTest f P true = refl
liftnatTest f P false = refl
liftnatTest f P (⋁ x) = cong ∃ (funext (λ x₁ → liftnatTest f P (x x₁)))
liftnatTest f P (⋀ x) = cong (λ z → (n : _) → z n) (funext (λ x₁ → liftnatTest f P (x x₁)))

-- distinctions by dualization

dualTest : {A : Set} → (tes : Test A) → Test A
dualTest (atom x) = atom x
dualTest (tes ∧ tes₁) = (dualTest tes) ∨ (dualTest tes₁)
dualTest (tes ∨ tes₁) = (dualTest tes) ∧ (dualTest tes₁)
dualTest true = false
dualTest false = true
dualTest (⋁ x) = ⋀ (λ i → dualTest (x i))
dualTest (⋀ x) = ⋁ (λ i → dualTest (x i))


dualnatTest : {A B : Set} → {f : A → B} → (tes : Test A) → (functorTest f (dualTest tes)) ≡ (dualTest (functorTest f tes))
dualnatTest (atom x) = refl
dualnatTest (tes ∧ tes₁) = cong₂ _∨_ (dualnatTest tes) (dualnatTest tes₁)
dualnatTest (tes ∨ tes₁) =  cong₂ _∧_ (dualnatTest tes) (dualnatTest tes₁)
dualnatTest true = refl
dualnatTest false = refl
dualnatTest (⋁ x) = cong ⋀ (funext (λ i → dualnatTest (x i)))
dualnatTest (⋀ x) = cong ⋁ (funext (λ i → dualnatTest (x i)))

distTest : {A : Set} → (P Q : A → Set) → ((a : A) → (P a) → (Q a) → ⊥)
   → (tes : Test A) → (liftTest P tes) → (liftTest Q (dualTest tes)) → ⊥
distTest P Q dist (atom x) L R = dist x L R
distTest P Q dist (test ∧ test₁) (fst , snd) (inj₁ x) = distTest P Q dist test fst x
distTest P Q dist (test ∧ test₁) (fst , snd) (inj₂ y) = distTest P Q dist test₁ snd y
distTest P Q dist (test ∨ test₁) (inj₁ x) (fst , snd) = distTest P Q dist test x fst
distTest P Q dist (test ∨ test₁) (inj₂ y) (fst , snd) = distTest P Q dist test₁ y snd
distTest P Q dist (⋁ x) (n , pruf) R = distTest P Q dist (x n) pruf (R n)
distTest P Q dist (⋀ x) L (n , pruf) = distTest P Q dist (x n) (L n) pruf

-- syntactic ordering
data synTest {A B : Set} (f : A → B → Set) : (Test A) → (Test B) → Set where
  syn-atom : (a : A) → (b : B) → (f a b) → (synTest f (atom a) (atom b))
  syn-∧ : (ta₁ ta₂ : Test A) → (tb₁ tb₂ : Test B) → (synTest f ta₁ tb₁)
    → (synTest f ta₂ tb₂) → (synTest f (ta₁ ∧ ta₂) (tb₁ ∧ tb₂))
  syn-∨ : (ta₁ ta₂ : Test A) → (tb₁ tb₂ : Test B) → (synTest f ta₁ tb₁)
    → (synTest f ta₂ tb₂) → (synTest f (ta₁ ∨ ta₂) (tb₁ ∨ tb₂))
  syn-false : (tb : Test B) → (synTest f false tb)
  syn-true : (ta : Test A) → (synTest f ta true)
  syn-⋁ : (tf : ℕ → Test A) → (tg : ℕ → Test B) →
    ((n : ℕ) → synTest f (tf n) (tg n)) → (synTest f (⋁ tf) (⋁ tg))
  syn-⋀ : (tf : ℕ → Test A) → (tg : ℕ → Test B) →
    ((n : ℕ) → synTest f (tf n) (tg n)) → (synTest f (⋀ tf) (⋀ tg))

pordTest : {A : Set} → (A → Set) → (Test A) → (Test A) → Set
pordTest P tes₁ tes₂ = liftTest P tes₁ → liftTest P tes₂ 


orderTest : (A B : Set) → (A → B → Set) → (Test A) → (Test B) → Set₁
orderTest A B ord tesa tesb = ∀ (P : A → Set) → ∀ (Q : B → Set)
  → (∀ (a : A) → ∀ (b : B) → (ord a b) → (P a) → (Q b))
  → liftTest P tesa → liftTest Q tesb

orderTest-s : (A : Set) → (A → A → Set) → (Test A) → (Test A) → Set₁
orderTest-s A ord tes₁ tes₂ = ∀ (P : A → Set)
  → (∀ (a b : A) → (ord a b) → (P a) → (P b))
  → liftTest P tes₁ → liftTest P tes₂


-- dual-orderTest : {A B : Set} → (ord : A → B → Set) → (tesa : Test A) → (tesb : Test B)
--   → (orderTest A B ord tesa tesb) → (orderTest B A (λ b a → ord a b) (dualTest tesb) (dualTest tesa))
-- dual-orderTest ord (atom x) tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!tesa-tesb!}
-- dual-orderTest ord (tesa ∧ tesa₁) tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
-- dual-orderTest ord (tesa ∨ tesa₁) tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
-- dual-orderTest ord true tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
-- dual-orderTest ord false tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
-- dual-orderTest ord (⋁ x) tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
-- dual-orderTest ord (⋀ x) tesb tesa-tesb P Q P-dro-Q P-i-tesb = {!!}
