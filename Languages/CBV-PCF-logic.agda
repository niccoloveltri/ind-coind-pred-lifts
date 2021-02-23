open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool

module Languages.CBV-PCF-logic (Sig : Set) (ar : Sig → Set)
                               (O : Set) (αl : O → Bool)
                               (αn : (k : Sig) → O → Test (ar k × O))
                               (αd : O → (Test O)) where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Function hiding (_⟶_)

open import Signatures
open add-skip Sig ar
open import Trees-Coinductive
import Languages.CBV-PCF
open Languages.CBV-PCF Sig ar

α⊥l : O → Bool
α⊥l = αl
α⊥n : (k : Sig⊥) → O → Test (ar⊥ k × O)
α⊥n (inj₁ k) o = αn k o
α⊥n (inj₂ tt) o = functorTest (λ x → tt , x) (αd o)


import Pred-Lift-ab
open Pred-Lift-ab ar⊥ O α⊥l α⊥n

-- formulas (bas) (v/c) (type) (formula)
data Form : Bool → Ty → Set where
  bas-Nat : ℕ → (Form val N)
  bas-Fun : {τ σ : Ty} → (TVal τ) → (Form cpt σ)
    → (Form val (τ ⟶ σ))
  bas-Com : {τ : Ty} → O → (Form val τ) → (Form cpt τ)
  clo-Form : {a : Bool} → {τ : Ty} → Test (Form a τ) → Form a τ 


infix 6 _⊧_
_⊧_ : {b : Bool} → {τ : Ty} → (P : TTerm b τ) → (ϕ : Form b τ) → Set
V ⊧ (bas-Fun W ϕ) = (app V W) ⊧ ϕ
M ⊧ (bas-Com o ψ) = liftTree (λ V → V ⊧ ψ) o (Tdenot M)
P ⊧ clo-Form (atom x) = P ⊧ x
P ⊧ clo-Form (E ∧ E₁) = P ⊧ clo-Form E × P ⊧ clo-Form E₁
P ⊧ clo-Form (E ∨ E₁) = P ⊧ clo-Form E ⊎ P ⊧ clo-Form E₁
P ⊧ clo-Form true = ⊤
P ⊧ clo-Form false = False
P ⊧ clo-Form (⋁ x) = Σ ℕ (λ n → P ⊧ clo-Form (x n))
P ⊧ clo-Form (⋀ x) = (n : ℕ) → (P ⊧ clo-Form (x n))
Z ⊧ bas-Nat zero = True
(S V) ⊧ bas-Nat zero = False
Z ⊧ bas-Nat (suc x) = False
(S V) ⊧ bas-Nat (suc x) = V ⊧ bas-Nat x




Log-Order : {a : Bool} → {τ : Ty} → (P Q : TTerm a τ) → Set
Log-Order P Q = (ϕ : Form _ _) → (P ⊧ ϕ) → (Q ⊧ ϕ)



import Relators
open Relators ar⊥ O α⊥l α⊥n

wek : Set → Set₁
wek a = ∀(b : Set) → a

wtr : Set₁
wtr = (a : Bool) → (τ : Ty) → (P Q : TTerm a τ) → Set

app-sim-loc  :  (R : wtr) → (a : Bool) → (τ : Ty) → (P Q : TTerm a τ) → Set₁
app-sim-loc R cpt τ P Q = O-Relator (R val τ) (Tdenot P) (Tdenot Q)
app-sim-loc R val N P Q = wek (P ≡ Q)
app-sim-loc R val (τ ⟶ σ) P Q = ∀(U : TTerm val τ) → wek (R cpt σ (app P U) (app Q U))

app-sim : (R : wtr) → Set₁
app-sim R = ∀(a : Bool) → ∀(τ : Ty) → ∀(P Q : TTerm a τ)
  → (R a τ P Q) → app-sim-loc R a τ P Q

app-simil : (a : Bool) → (τ : Ty) → (P Q : TTerm a τ) → Set₁
app-simil a τ P Q = Σ wtr (λ R → (app-sim R) × R a τ P Q)

distinction : {a : Bool} → {τ : Ty} → (R : wtr) → (app-sim R) →
  (ϕ : Form a τ) → (P Q : TTerm a τ)
  → (R a τ P Q) → (P ⊧ ϕ) → (Q ⊧ ϕ)
distinction R sim (clo-Form (atom ϕ)) P Q =
  distinction R sim ϕ P Q
distinction R sim (clo-Form (E ∧ E₁)) P Q PRQ (fst , snd) =
  (distinction R sim (clo-Form E) P Q PRQ fst) ,
  (distinction R sim (clo-Form E₁) P Q PRQ snd)
distinction R sim (clo-Form (E ∨ E₁)) P Q PRQ (inj₁ x) =
  inj₁ (distinction R sim (clo-Form E) P Q PRQ x)
distinction R sim (clo-Form (E ∨ E₁)) P Q PRQ (inj₂ y) =
  inj₂ (distinction R sim (clo-Form E₁) P Q PRQ y)
distinction R sim (clo-Form true) P Q PRQ Pmϕ = tt
distinction R sim (clo-Form false) P Q PRQ Pmϕ = Pmϕ
distinction R sim (clo-Form (⋁ x)) P Q PRQ (n , K) = n ,
  distinction R sim (clo-Form (x n)) P Q PRQ K
distinction R sim (clo-Form (⋀ x)) P Q PRQ hypo =
  λ n → distinction R sim (clo-Form (x n)) P Q PRQ (hypo n)
distinction R sim (bas-Nat n) P Q PRQ Pmϕ =
  subst (λ x → x ⊧ (bas-Nat n)) (sim _ _ P Q PRQ ℕ) Pmϕ
distinction R sim (bas-Fun V ϕ) P Q PRQ Pmϕ = distinction R sim ϕ (app P V) (app Q V) (sim _ _ P Q PRQ V ℕ) Pmϕ
distinction R sim (bas-Com o ϕ) P Q PRQ Pmoϕ =
  sim _ _ _ _ PRQ (λ V → V ⊧ ϕ) (λ V → V ⊧ ϕ)
  (λ V W Vmϕ VRW → distinction R sim ϕ V W VRW Vmϕ) o Pmoϕ

inclusion :  ∀(a : Bool) → ∀(τ : Ty) → ∀(P Q : TTerm a τ)
  → (app-simil a τ P Q) → (Log-Order P Q)
inclusion a τ P Q (R , sim , PRQ) = λ ϕ x →
  distinction R sim ϕ P Q PRQ x


