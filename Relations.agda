open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool hiding (_∧_; _∨_)

module Relations  {K : Set} (I : K → Set)
                 (O : Set) (αl : O → Bool)
                 (αn : (k : K) → O → Test (I k × O)) where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size


open import Logic I O αl αn
open import Trees-Coinductive


-- Properties of relations

-- reflexivity
rel-idin : ∀ {i} {A : Set} (R : A → A → Set i) → Set i
rel-idin R = (a : _) → R a a

-- composing relations
rel-comp : ∀ {i} {A B C : Set} (R : A → B → Set i) (S : B → C → Set i) → A → C → Set i
rel-comp R S a c = Σ _ λ b → ((R a b) × (S b c))

-- inclusion of relations
rel-ord : ∀ {i} {A B : Set} (R S : A → B → Set i) → Set i
rel-ord R S = (a : _) → (b : _) → (R a b) → (S a b)

-- transitivity
rel-tran : ∀ {i} {A : Set} (R : A → A → Set i) → Set i
rel-tran R = rel-ord (rel-comp R R) R

-- union
rel-∪ :  ∀ {i} {A B : Set} (R S : A → B → Set i) → A → B → Set i
rel-∪ R S a b = (R a b) ⊎ (S a b)

-- n-fold composition
rel-n : ∀ {i} {A : Set} (R : A → A → Set i) → ℕ → A → A → Set i
rel-n R zero = R
rel-n R (suc n) = rel-comp (rel-n R n) R

-- the transitive/reflexive closure
rel-⋆ : ∀ {i} {A : Set} (R : A → A → Set i) → A → A → Set i
rel-⋆ R a b = ∃ λ n → rel-n R n a b

-- left and right inclusion of relation union
rel-∪-ord1 :  ∀ {i} {A B : Set} (R S : A → B → Set i) → rel-ord R (rel-∪ R S)
rel-∪-ord1 R S a b aRb = inj₁ aRb

rel-∪-ord2 :  ∀ {i} {A B : Set} (R S : A → B → Set i) → rel-ord S (rel-∪ R S)
rel-∪-ord2 R S a b aSb = inj₂ aSb

-- symmetry of union
rel-∪-sym :  ∀ {i} {A B : Set} (R S : A → B → Set i) → rel-ord (rel-∪ R S) (rel-∪ S R)
rel-∪-sym R S a b (inj₁ aRb) = inj₂ aRb
rel-∪-sym R S a b (inj₂ aSb) = inj₁ aSb

-- associativity of union
rel-∪-ass :  ∀ {i} {A B : Set} (R S T : A → B → Set i) → rel-ord R S → rel-ord S T
  → rel-ord R T
rel-∪-ass R S T R<S S<T a b aRb = S<T a b (R<S a b aRb)

-- transitive/reflexive closure contains the original relation
rel-⋆-ord : ∀ {i} {A : Set} (R : A → A → Set i) → rel-ord R (rel-⋆ R)
rel-⋆-ord R a b aRb = (zero , aRb)


-- ==============================================
--   Relation lifting
-- ==============================================

-- When a predicate is correct according to an endongenous relation
corp : ∀ {i} (A : Set) (R : A → A → Set i) (f : A → Set) → Set i
corp A R f = (a b : A) → f a → R a b → f b

-- Correctness preservation over relation inclusion
corp-ord : ∀ {i} (A : Set) (R S : A → A → Set i) → (f : A → Set)
  → corp A S f → (rel-ord R S) → corp A R f
corp-ord A R S f Sf R<S a b fa aRb = Sf a b fa (R<S a b aRb) 

-- Relation lifting to coinductive trees, induced by α and β respectively
Γα : ∀ {i} (A : Set) (R : A → A → Set i) (t r : Tree I A) → Set (lsuc lzero ⊔ i)
Γα A R t r = (f : A → Set) → corp A R f → (o : O) → liftTree f o t → liftTree f o r

Γβ : ∀ {i} (A : Set) (R : A → A → Set i) (t r : Tree I A) → Set (lsuc lzero ⊔ i)
Γβ A R t r = (f : A → Set) → corp A R f → (o : O) → β-liftTree f o t → β-liftTree f o r

Γβ' : ∀ {i} (A : Set) (R : A → A → Set i) (t r : Tree I A) → Set (lsuc lzero ⊔ i)
Γβ' A R t r = (f : A → Set) → corp A R f → (o : O)
  → β-liftTree f o t → β-liftTree' f o r

-- Combined relation lifting
Γ : ∀ {i} {A : Set} (R : A → A → Set i) (t r : Tree I A) → Set (lsuc lzero ⊔ i)
Γ R t r = (Γα _ R t r) × Γβ _ R t r

-- ==================================
-- properties of the relation lifting

-- monotonicity
Γ-mono : ∀ {i} {A : Set} (R S : A → A → Set i) → rel-ord R S → rel-ord (Γ R) (Γ S)
Γ-mono R S R<S t r (tΓαr , tΓβr) =
  (λ f Sf o t-of → tΓαr f (corp-ord _ R S f Sf R<S) o t-of) ,
  (λ f Sf o t-of → tΓβr f (corp-ord _ R S f Sf R<S) o t-of)

-- reflexivity
Γ-id : ∀ {i} {A : Set} (R : A → A → Set i) → rel-idin R → rel-idin (Γ R)
Γ-id R refR t = (λ f x o x₁ → x₁) , (λ f x o x₁ → x₁)

-- functoriality
Γ-functor : ∀ {i} {A B : Set} (f : A → B) (R : B → B → Set i) (t t' : Tree I A)
  → Γ (λ a a' → R (f a) (f a')) t t' → Γ R (mapTree f t) (mapTree f t')
proj₁ (Γ-functor f R t t' (as-α , as-β)) g Rg o ft-og =
  subst (α o) (sym (functTree f g t'))
    (as-α (g ∘ f) (λ a b gfa faRfb → Rg (f a) (f b) gfa faRfb) o
  (subst (α o) (functTree f g t) ft-og))
proj₂ (Γ-functor f R t t' (as-α , as-β)) g Rg o ft-og =
  subst (β ∞ o) (sym (functTree f g t'))
    (as-β (g ∘ f) (λ a b gfa faRfb → Rg (f a) (f b) gfa faRfb) o
  (subst (β ∞ o) (functTree f g t) ft-og))


-- Relation liftings are preserved over monadic multiplication, given decomposability
Γα-doub : {A : Set} → Decomposable → (R : A → A → Set₁) → (D E : Tree I (Tree I A))
  → Γα _ (Γα _ R) D E → Γα _ R (μTree D) (μTree E) 
Γα-doub decom R D E DααRE f Rf o μDof =
  subst (α o) (sym (μ-natural f E))
  (decom (mapTree (mapTree f) D) (mapTree (mapTree f) E)
    (λ o₁ os fD-o₁os →
    subst (α o₁) (sym (functTree (mapTree f) (λ t → liftTest (λ o' → α o' t) os) E))
      (DααRE (λ x → liftTest (λ o' → α o' (mapTree f x)) os)
        (λ a b x x₁ →
          liftfunTest O (λ o' → α o' (mapTree f a)) (λ o' → α o' (mapTree f b)) os
            (x₁ f Rf) x)
        o₁
    (subst (α o₁) (functTree (mapTree f) (λ t → liftTest (λ o' → α o' t) os) D) fD-o₁os)))
    o
  (subst (α o) (μ-natural f D) μDof))

Γβ-doub : {A : Set} → β-Decomposable → (R : A → A → Set₁) → (D E : Tree I (Tree I A))
  → Γβ _ (Γβ _ R) D E → Γβ _ R (μTree D) (μTree E) 
Γβ-doub decom R D E DββRE f Rf o μDof =
  subst (β ∞ o) (sym (μ-natural f E))
  (decom (mapTree (mapTree f) D) (mapTree (mapTree f) E)
    (λ o₁ os fD-o₁os →
    subst (β ∞ o₁) (sym (functTree (mapTree f) (λ t → liftTest (λ o' → β ∞ o' t) os) E))
      (DββRE (λ x → liftTest (λ o' → β ∞ o' (mapTree f x)) os)
        (λ a b x x₁ →
          liftfunTest O (λ o' → β ∞ o' (mapTree f a)) (λ o' → β ∞ o' (mapTree f b)) os
            (x₁ f Rf) x)
        o₁
    (subst (β ∞ o₁)
      (functTree (mapTree f) (λ t → liftTest (λ o' → β ∞ o' t) os) D) fD-o₁os))) o
  (subst (β ∞ o) (μ-natural f D) μDof))


Γ-doub : {A : Set} → Decomposable → β-Decomposable →
  (R : A → A → Set₁) → (D E : Tree I (Tree I A))
  → Γ (Γ R) D E → Γ R (μTree D) (μTree E) 
proj₁ (Γ-doub decom β-dec R D E DΓΓRE) = Γα-doub decom R D E
  (proj₁ (Γ-mono (Γ R) (Γα _ R) (λ a b x → proj₁ x) D E DΓΓRE))
proj₂ (Γ-doub decom β-dec R D E DΓΓRE) = Γβ-doub β-dec R D E
  (proj₂ (Γ-mono (Γ R) (Γβ _ R) (λ a b x → proj₂ x) D E DΓΓRE))


-- =======================
-- well-typed relations
-- =======================

-- relations on program denotation indexed by Agda types
typed-rel : Set₁
typed-rel = (a : Bool) → (τ : Aty) → (P Q : A-term a τ) → Set


-- extension of relation properties to well-typed relations

-- inclusion
typed-rel-ord : (R S : typed-rel) → Set
typed-rel-ord R S = (a : Bool) → (τ : Aty) → rel-ord (R a τ) (S a τ)

-- union
typed-rel-∪ : (R S : typed-rel) → typed-rel
typed-rel-∪ R S a τ = rel-∪ (R a τ) (S a τ)

-- transitive/reflexive closure
typed-rel-⋆ : (R : typed-rel) → typed-rel
typed-rel-⋆ R a τ = rel-⋆ (R a τ)

-- union inclusions
typed-rel-∪-ord1 :  (R S : typed-rel) → typed-rel-ord R (typed-rel-∪ R S)
typed-rel-∪-ord1 R S a τ = rel-∪-ord1 (R a τ) (S a τ)

typed-rel-∪-ord2 :  (R S : typed-rel) → typed-rel-ord S (typed-rel-∪ R S)
typed-rel-∪-ord2 R S a τ = (rel-∪-ord2 (R a τ) (S a τ))

-- transitive/reflexive closure inclusion
typed-rel-⋆-ord : (R : typed-rel) → typed-rel-ord R (typed-rel-⋆ R)
typed-rel-⋆-ord R a τ = rel-⋆-ord (R a τ)


-- Helpful auxiliary constructions 
llif : (i : Level) → Set i → Set (lsuc i)
llif i A = Set i → A
llif-p : ∀ {i} (A : Set i) → A → llif i A
llif-p A a x = a
llif-b : ∀ {i} (A : Set i) → llif i A → A
llif-b A x = x A

TOK : Set
TOK = Bool


-- Properties for formulating applicative simulation condition
simulprop : (R : typed-rel) → (a : Bool) → (τ : Aty) → (P Q : A-term a τ)
  → (R a τ P Q) → Set₁
simulprop R cpt τ P Q PRQ = Γ (R val τ) P Q
simulprop R val N P Q PRQ = llif lzero (P ≡ Q)
simulprop R val (σ ⇒ τ) P Q PRQ = (V : A-val σ) → llif lzero (R cpt τ (P V) (Q V))
simulprop R val (σ ⊗ τ) P Q PRQ =
  llif lzero (R val σ (proj₁ P) (proj₁ Q)) × llif lzero (R val τ (proj₂ P) (proj₂ Q))
simulprop R val (U τ) P Q PRQ = llif lzero (R cpt τ P Q)

-- Predicate testing whether a typed relation is an applicative simulation
simulation : (R : typed-rel) → Set₁
simulation R =  (a : Bool) → (τ : Aty) → (P Q : A-term a τ)
  → (PRQ : R a τ P Q) → simulprop R a τ P Q PRQ

-- The union of applicative simulations is an applicative simulation
simulation-∪ : (R S : typed-rel) → (simulation R) → (simulation S)
  → simulation (typed-rel-∪ R S)
simulation-∪ R S simR simS cpt τ P Q (inj₁ PRQ) = Γ-mono (R val τ)
  (rel-∪ (R val τ) (S val τ)) (rel-∪-ord1 (R val τ) (S val τ)) P Q
  (simR cpt τ P Q PRQ)
simulation-∪ R S simR simS val N P Q (inj₁ PRQ) = simR val N P Q PRQ
simulation-∪ R S simR simS val (τ ⇒ τ₁) P Q (inj₁ PRQ) V TOK =
  inj₁ (simR val (τ ⇒ τ₁) P Q PRQ V TOK)
simulation-∪ R S simR simS val (τ ⊗ τ₁) P Q (inj₁ PRQ) =
  (λ z → inj₁ (proj₁ (simR val (τ ⊗ τ₁) P Q PRQ) z)) ,
  (λ z → inj₁ (proj₂ (simR val (τ ⊗ τ₁) P Q PRQ) z))
simulation-∪ R S simR simS val (U τ) P Q (inj₁ PRQ) z =
  inj₁ (simR val (U τ) P Q PRQ z)
simulation-∪ R S simR simS cpt τ P Q (inj₂ PSQ) =  Γ-mono (S val τ)
  (rel-∪ (R val τ) (S val τ)) (rel-∪-ord2 (R val τ) (S val τ)) P Q
  (simS cpt τ P Q PSQ)
simulation-∪ R S simR simS val N P Q (inj₂ PSQ) = simS val N P Q PSQ
simulation-∪ R S simR simS val (τ ⇒ τ₁) P Q (inj₂ PSQ) V z =
  inj₂ (simS val (τ ⇒ τ₁) P Q PSQ V z)
simulation-∪ R S simR simS val (τ ⊗ τ₁) P Q (inj₂ PSQ) =
  (λ z → inj₂ (proj₁ (simS val (τ ⊗ τ₁) P Q PSQ) z)) ,
  (λ z → inj₂ (proj₂ (simS val (τ ⊗ τ₁) P Q PSQ) z))
simulation-∪ R S simR simS val (U τ) P Q (inj₂ PSQ) z =
  inj₂ (simS val (U τ) P Q PSQ z)

-- The transitive/reflexive closure of an applicative simulation is
-- an applicative simulation
simulation-⋆ : (R : typed-rel) → (simulation R) → (simulation (typed-rel-⋆ R))
simulation-⋆ R simR cpt τ P Q (zero , PRnQ) = Γ-mono (R val τ) (typed-rel-⋆ R val τ)
  (rel-⋆-ord (R val τ)) P Q (simR cpt τ P Q PRnQ)
simulation-⋆ R simR val N P Q (zero , PRnQ) = simR val N P Q PRnQ
simulation-⋆ R simR val (τ ⇒ τ₁) P Q (zero , PRnQ) V z =
  zero , simR val (τ ⇒ τ₁) P Q PRnQ V z
simulation-⋆ R simR val (τ ⊗ τ₁) P Q (zero , PRnQ) =
  (λ z → (zero , proj₁ (simR val (τ ⊗ τ₁) P Q PRnQ) z)) ,
  (λ z → (zero , proj₂ (simR val (τ ⊗ τ₁) P Q PRnQ) z))
simulation-⋆ R simR val (U τ) P Q (zero , PRnQ) z =
  zero , simR val (U τ) P Q PRnQ z
simulation-⋆ R simR a τ P Q (suc n , M , PRnM , MRQ )
  with simulation-⋆ R simR a τ P M (n , PRnM)
simulation-⋆ R simR cpt τ P Q (suc n , M , PRnM , MRQ) | hypo =
  (λ f R⋆f o Pof → proj₁ (simR cpt τ M Q MRQ) f
    (λ a b fa aRb → R⋆f a b fa (zero , aRb)) o (proj₁ hypo f R⋆f o Pof)) ,
  λ f R⋆f o Pof → proj₂ (simR cpt τ M Q MRQ) f
    (λ a b fa aRb → R⋆f a b fa (zero , aRb)) o (proj₂ hypo f R⋆f o Pof)
simulation-⋆ R simR val N P Q (suc n , M , PRnM , MRQ) | hypo = llif-p (P ≡ Q)
  (subst (λ z → z ≡ Q) (sym (llif-b (P ≡ M) hypo))
  (llif-b (M ≡ Q) (simR val N M Q MRQ)))
simulation-⋆ R simR val (τ ⇒ τ₁) P Q (suc n , M , PRnM , MRQ) | hypo = λ V z →
  suc (proj₁ (hypo V z)) , (M V) , (proj₂ (hypo V z) , simR val (τ ⇒ τ₁) M Q MRQ V z)
simulation-⋆ R simR val (τ ⊗ τ₁) P Q (suc n , M , PRnM , MRQ) | hypo =
  (λ z → suc (proj₁ (proj₁ hypo z)) , (proj₁ M) , (proj₂ (proj₁ hypo z) ,
        proj₁ (simR val (τ ⊗ τ₁) M Q MRQ) z)) ,
  λ z → suc (proj₁ (proj₂ hypo z)) , (proj₂ M) , (proj₂ (proj₂ hypo z) ,
        proj₂ (simR val (τ ⊗ τ₁) M Q MRQ) z)
simulation-⋆ R simR val (U τ) P Q (suc n , M , PRnM , MRQ) | hypo =
  λ z → suc (proj₁ (hypo z)) , M , (proj₂ (hypo z) , simR val (U τ) M Q MRQ z)


-- Applicative similarity
simil : (a : Bool) → (τ : Aty) → (P Q : A-term a τ) → Set₁
simil a τ P Q = ∃ λ R → simulation R × R a τ P Q

-- Transitivity of applicative similarity
simil-tra : {a : Bool} → {τ : Aty} → (P M Q : A-term a τ)
  → simil a τ P M → simil a τ M Q → simil a τ P Q
simil-tra P M Q (R , simR , PRM) (S , simS , MSQ) = (typed-rel-⋆ (typed-rel-∪ R S)) ,
  ((simulation-⋆ (typed-rel-∪ R S) (simulation-∪ R S simR simS)) ,
  (suc zero , M , (inj₁ PRM , inj₂ MSQ)))


-- Applicative similarity implies logical ordering
rel-form : (R : typed-rel) → (simulation R) → (a : Bool) → (τ : Aty)
  → (ϕ : A-form a τ) → (P Q : A-term a τ)
  → (R a τ P Q) → (P ⊧ ϕ) → (Q ⊧ ϕ)
rel-form R simR .val N (bas-Nat x) P Q PRQ Pmϕ = subst (λ z → Q ≡ z) Pmϕ
  (sym (simR val N P Q PRQ TOK))
rel-form R simR .val N (bas-Tan x) P Q PRQ Pmϕ = subst (λ z → z ≡ x → ⊥)
  (simR val N P Q PRQ TOK) Pmϕ
rel-form R simR .val .(_ ⇒ _) (bas-Fun V ϕ) P Q PRQ Pmϕ =
  rel-form R simR cpt _ ϕ (P V) (Q V) (simR val _ P Q PRQ V TOK) Pmϕ
rel-form R simR .val .(_ ⊗ _) (bas-Lef ϕ) P Q PRQ Pmϕ = rel-form R simR val _
  ϕ (proj₁ P) (proj₁ Q) (proj₁ (simR val _ P Q PRQ) TOK) Pmϕ
rel-form R simR .val .(_ ⊗ _) (bas-Rig ϕ) P Q PRQ Pmϕ =  rel-form R simR val _
  ϕ (proj₂ P) (proj₂ Q) (proj₂ (simR val _ P Q PRQ) TOK) Pmϕ
rel-form R simR .val .(U _) (bas-Thu ϕ) P Q PRQ Pmϕ = 
  rel-form R simR cpt _ ϕ P Q (simR val (U _) P Q PRQ TOK) Pmϕ 
rel-form R simR .cpt τ (bas-Comα o ϕ) P Q PRQ Pmϕ = proj₁ (simR cpt τ P Q PRQ)
  (λ V → V ⊧ ϕ) (λ V W V-ϕ VRW → rel-form R simR val τ ϕ V W VRW V-ϕ) o Pmϕ
rel-form R simR .cpt τ (bas-Comβ o ϕ) P Q PRQ Pmϕ = proj₂ (simR cpt τ P Q PRQ)
  (λ V → V ⊧ ϕ) (λ V W V-ϕ VRW → rel-form R simR val τ ϕ V W VRW V-ϕ) o Pmϕ
rel-form R simR a τ (clo-Form (atom ϕ)) P Q PRQ Pmϕ =
  rel-form R simR a τ ϕ P Q PRQ Pmϕ
rel-form R simR a τ (clo-Form (tes ∧ tes₁)) P Q PRQ (fst , snd) =
  (rel-form R simR a τ (clo-Form tes) P Q PRQ fst) ,
  (rel-form R simR a τ (clo-Form tes₁) P Q PRQ snd)
rel-form R simR a τ (clo-Form (tes ∨ tes₁)) P Q PRQ (inj₁ x) =
  inj₁ (rel-form R simR a τ (clo-Form tes) P Q PRQ x)
rel-form R simR a τ (clo-Form (tes ∨ tes₁)) P Q PRQ (inj₂ y) =
  inj₂ (rel-form R simR a τ (clo-Form tes₁) P Q PRQ y)
rel-form R simR a τ (clo-Form val) P Q PRQ tt = tt
rel-form R simR a τ (clo-Form (⋁ x)) P Q PRQ (n , Pmϕ) =
  n , rel-form R simR a τ (clo-Form (x n)) P Q PRQ Pmϕ
rel-form R simR a τ (clo-Form (⋀ x)) P Q PRQ Pmϕ n =
  rel-form R simR a τ (clo-Form (x n)) P Q PRQ (Pmϕ n)

rel-sim-imp-log : {a : Bool} {τ : Aty} (P Q : A-term a τ)
  → simil a τ P Q → Log-Order a τ P Q
rel-sim-imp-log P Q (R , simR , PRQ) ϕ = rel-form R simR _ _ ϕ P Q PRQ

rel-dist : {a : Bool} {τ : Aty} (P Q : A-term a τ)
  → (ϕ : A-form a τ) → (R : typed-rel) → (simulation R)
  → (P ⊧ ϕ) → (Q ⊧ (neg-Form ϕ)) → (R a τ P Q) → ⊥
rel-dist P Q ϕ R simR Pmϕ Qnϕ PRQ =
  dist-Log ϕ Q (rel-sim-imp-log P Q (R , simR , PRQ) ϕ Pmϕ) Qnϕ

