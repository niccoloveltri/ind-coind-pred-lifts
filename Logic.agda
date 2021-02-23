open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool

module Logic {Sig : Set} (ar : Sig → Set)
             (O : Set) (αl : O → Bool)
             (αn : (k : Sig) → O → Test (ar k × O)) where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Function
open import Size

open import Signatures
open import Trees-Coinductive


-- Importing program types
import Program-Types
open Program-Types ar public

-- Importing inductive and coinductive properties
import Pred-Lift-ab
open Pred-Lift-ab ar O αl αn public


-- Program formulas
data A-form : Bool → Aty → Set where
  bas-Nat : ℕ → (A-form val N)
  bas-Tan : ℕ → (A-form val N)
  bas-Fun : {τ σ : Aty} → (A-val τ) → (A-form cpt σ)
    → (A-form val (τ ⇒ σ))
  bas-Lef : {τ σ : Aty} → (A-form val τ) → (A-form val (τ ⊗ σ))
  bas-Rig : {τ σ : Aty} → (A-form val σ) → (A-form val (τ ⊗ σ))
  bas-Thu : {τ : Aty} → (A-form cpt τ) → (A-form val (U τ))
  bas-Comα : {τ : Aty} → O → (A-form val τ) → (A-form cpt τ)
  bas-Comβ : {τ : Aty} → O → (A-form val τ) → (A-form cpt τ)
  clo-Form : {a : Bool} → {τ : Aty} → Test (A-form a τ) → A-form a τ 


infix 6 _⊧_
_⊧_ : {b : Bool} → {τ : Aty} → (P : A-term b τ) → (ϕ : A-form b τ) → Set
n ⊧ bas-Nat ϕ = n ≡ ϕ
n ⊧ bas-Tan ϕ = n ≢ ϕ
V ⊧ (bas-Fun W ϕ) = (V W) ⊧ ϕ
(V , W) ⊧ bas-Lef ϕ = (V ⊧ ϕ)
(V , W) ⊧ bas-Rig ψ = (W ⊧ ψ)
V ⊧ bas-Thu ϕ = V ⊧ ϕ
M ⊧ (bas-Comα o ψ) = liftTree (λ V → V ⊧ ψ) o (M)
M ⊧ (bas-Comβ o ψ) = β-liftTree (λ V → V ⊧ ψ) o (M)
P ⊧ clo-Form (atom x) = P ⊧ x
P ⊧ clo-Form (E ∧ E₁) = P ⊧ clo-Form E × P ⊧ clo-Form E₁
P ⊧ clo-Form (E ∨ E₁) = P ⊧ clo-Form E ⊎ P ⊧ clo-Form E₁
P ⊧ clo-Form true = ⊤
P ⊧ clo-Form false = ⊥
P ⊧ clo-Form (⋁ x) = Σ ℕ (λ n → P ⊧ clo-Form (x n))
P ⊧ clo-Form (⋀ x) = (n : ℕ) → (P ⊧ clo-Form (x n))


-- Extensional (hopefully congruent) equivalence

Log-Order : (a : Bool) → (τ : Aty) → (P Q : A-term a τ) → Set
Log-Order a τ P Q = (ϕ : A-form a τ) → (P ⊧ ϕ) → (Q ⊧ ϕ)

-- Helpful sugar

clo-Form-eq  : {a : Bool} → {τ : Aty} → (tes : Test (A-form a τ))
  → (P : A-term a τ) → (liftTest (λ ϕ → (P ⊧ ϕ)) tes) ≡ (P ⊧ clo-Form tes)
clo-Form-eq (atom x) P = refl
clo-Form-eq (tes Test.∧ tes₁) P = subst
  (λ a → (liftTest (_⊧_ P) tes × liftTest (_⊧_ P) tes₁) ≡ (a × P ⊧ clo-Form tes₁))
  (clo-Form-eq tes P)
    (subst (λ b → (liftTest (_⊧_ P) tes × liftTest (_⊧_ P) tes₁) ≡ (liftTest (_⊧_ P) tes × b))
    (clo-Form-eq tes₁ P) refl)
clo-Form-eq (tes Test.∨ tes₁) P =  subst
  (λ a → (liftTest (_⊧_ P) tes ⊎ liftTest (_⊧_ P) tes₁) ≡ (a ⊎ P ⊧ clo-Form tes₁))
  (clo-Form-eq tes P)
    (subst (λ b → (liftTest (_⊧_ P) tes ⊎ liftTest (_⊧_ P) tes₁) ≡ (liftTest (_⊧_ P) tes ⊎ b))
    (clo-Form-eq tes₁ P) refl)
clo-Form-eq val P = refl
clo-Form-eq cpt P = refl
clo-Form-eq (⋁ x) P = cong ∃ (funext (λ n → clo-Form-eq (x n) P))
clo-Form-eq (⋀ x) P = cong (λ z → (n : _) → z n) (funext (λ n → clo-Form-eq (x n) P)) 

clo-Form-eq2 : {a : Bool} → {τ : Aty} → {A : Set} → (tes : Test A) → (f : A → (A-form a τ))
  → (P : A-term a τ) →
  (liftTest (λ a → (P ⊧ f a)) tes) ≡ (P ⊧ clo-Form (functorTest (λ a → f a) tes))
clo-Form-eq2 (atom x) f P = refl
clo-Form-eq2 (tes Test.∧ tes₁) f P = cong₂ _×_ (clo-Form-eq2 tes f P) (clo-Form-eq2 tes₁ f P)
clo-Form-eq2 (tes Test.∨ tes₁) f P =  cong₂ _⊎_ (clo-Form-eq2 tes f P) (clo-Form-eq2 tes₁ f P)
clo-Form-eq2 val f P = refl
clo-Form-eq2 cpt f P = refl
clo-Form-eq2 (⋁ x) f P = cong ∃ (funext (λ n → clo-Form-eq2 (x n) f P))
clo-Form-eq2 (⋀ x) f P =  cong (λ z → (n : _) → (z n)) (funext (λ n → clo-Form-eq2 (x n) f P))

-- examples

N-twice : ℕ → ℕ
N-twice zero = zero
N-twice (suc n) = suc (suc (N-twice n))

even-Form : A-form val N
even-Form = clo-Form (⋁ λ x → atom (bas-Nat (N-twice x)))
odd-Form : A-form val N
odd-Form = clo-Form (⋁ (λ x → atom (bas-Nat (suc (N-twice x)))))

N-even : ℕ → Set
N-even zero = ⊤
N-even (suc zero) = ⊥
N-even (suc (suc n)) = N-even n

N-twice-even : (n : ℕ) → (N-even (N-twice n))
N-twice-even zero = tt
N-twice-even (suc n) = N-twice-even n

-- IXI in standard library?
N-sueq : (n m : ℕ) → ((suc n) ≡ (suc m)) → (n ≡ m)
N-sueq n .n refl = refl

even-equiv-r : (V : (A-val N)) → (V ⊧ even-Form) → (N-even V)
even-equiv-r zero hypo = tt
even-equiv-r (suc zero) (zero , ())
even-equiv-r (suc zero) (suc fst , ())
even-equiv-r (suc (suc V)) (suc fst , snd) = even-equiv-r V (fst , N-sueq _ _ (N-sueq _ _ snd))

even-equiv-l : (V : (A-val N)) → (N-even V) → (V ⊧ even-Form)
even-equiv-l zero hypo = zero , refl
even-equiv-l (suc (suc V)) hypo with even-equiv-l V hypo
... | fst , snd = (suc fst) , (cong (λ x → suc (suc x)) snd)

-- Positive negation exists

neg-Form : {b : Bool} → {τ : Aty} → (ϕ : A-form b τ) → (A-form b τ)
neg-Form-help : {b : Bool} → {τ : Aty} → (tes : Test (A-form b τ)) → Test (A-form b τ)
neg-Form (bas-Nat x) = bas-Tan x
neg-Form (bas-Tan x) = bas-Nat x
neg-Form (bas-Fun x ϕ) = bas-Fun x (neg-Form ϕ)
neg-Form (bas-Lef ϕ) = bas-Lef (neg-Form ϕ)
neg-Form (bas-Rig ϕ) = bas-Rig (neg-Form ϕ)
neg-Form (bas-Thu ϕ) = bas-Thu (neg-Form ϕ)
neg-Form (bas-Comα x ϕ) = bas-Comβ x (neg-Form ϕ)
neg-Form (bas-Comβ x ϕ) = bas-Comα x (neg-Form ϕ)
neg-Form (clo-Form tes) = clo-Form (neg-Form-help tes)
neg-Form-help (atom x) = atom (neg-Form x)
neg-Form-help (tes ∧ tes₁) = (neg-Form-help tes) Test.∨ (neg-Form-help tes₁)
neg-Form-help (tes ∨ tes₁) = (neg-Form-help tes) Test.∧ (neg-Form-help tes₁)
neg-Form-help true = false
neg-Form-help false = true
neg-Form-help (⋁ x) = ⋀ (λ i → neg-Form-help (x i))
neg-Form-help (⋀ x) = ⋁ (λ i → neg-Form-help (x i))


-- double negation is strictly identity
doub-eq-Log : {b : Bool} → {τ : Aty} → (ϕ : A-form b τ) → (neg-Form (neg-Form ϕ) ≡ ϕ)
doub-eq-Log-help : {b : Bool} → {τ : Aty} → (tes : Test (A-form b τ)) → (neg-Form-help (neg-Form-help tes) ≡ tes)
doub-eq-Log (bas-Nat n) = refl
doub-eq-Log (bas-Tan n) = refl
doub-eq-Log (bas-Fun V ϕ) = cong (λ ψ → (bas-Fun V ψ)) (doub-eq-Log ϕ)
doub-eq-Log (bas-Lef ϕ) = cong (λ ψ → bas-Lef ψ) (doub-eq-Log ϕ)
doub-eq-Log (bas-Rig ϕ) = cong (λ ψ → bas-Rig ψ) (doub-eq-Log ϕ)
doub-eq-Log (bas-Thu ϕ) = cong (λ ψ → bas-Thu ψ) (doub-eq-Log ϕ)
doub-eq-Log (bas-Comα o ϕ) = cong (λ ψ → (bas-Comα o ψ)) (doub-eq-Log ϕ)
doub-eq-Log (bas-Comβ o ϕ) = cong (λ ψ → (bas-Comβ o ψ)) (doub-eq-Log ϕ)
doub-eq-Log (clo-Form tes) = cong (λ ψ → (clo-Form ψ)) (doub-eq-Log-help tes)
doub-eq-Log-help (atom x) = cong (λ ψ → (atom ψ)) (doub-eq-Log x)
doub-eq-Log-help (tes Test.∧ tes₁) = cong₂ Test._∧_ (doub-eq-Log-help tes) (doub-eq-Log-help tes₁)
doub-eq-Log-help (tes Test.∨ tes₁) = cong₂ Test._∨_ (doub-eq-Log-help tes) (doub-eq-Log-help tes₁)
doub-eq-Log-help true = refl
doub-eq-Log-help false = refl
doub-eq-Log-help (⋁ x) = cong ⋁ (funext (λ n → doub-eq-Log-help (x n)))
doub-eq-Log-help (⋀ x) = cong ⋀ (funext (λ n → doub-eq-Log-help (x n)))


-- negation is distinction

dist-Log : {b : Bool} → {τ : Aty} → (ϕ : A-form b τ) → (P : A-term b τ)
  → (P ⊧ ϕ) → (P ⊧ (neg-Form ϕ)) → ⊥
dist-Log (bas-Nat n) k kmn knegn = knegn kmn
dist-Log (bas-Tan n) k kmn knegn = kmn knegn
dist-Log (bas-Fun x ϕ) P Pmϕ Pnegϕ = dist-Log ϕ (P x) Pmϕ Pnegϕ
dist-Log (bas-Lef ϕ) (P , Q) Pmϕ Pnegϕ = dist-Log ϕ P Pmϕ Pnegϕ
dist-Log (bas-Rig ϕ) (P , Q) Pmϕ Pnegϕ = dist-Log ϕ Q Pmϕ Pnegϕ
dist-Log (bas-Thu ϕ) P Pmϕ Pnegϕ = dist-Log ϕ P Pmϕ Pnegϕ
dist-Log (bas-Comα o ϕ) P Pmϕ Pnegϕ = dist-αβ (λ Q → Q ⊧ ϕ) (λ Q → Q ⊧ neg-Form ϕ)
  (dist-Log ϕ) (P) o Pnegϕ Pmϕ
dist-Log (bas-Comβ o ϕ) P Pmϕ Pnegϕ = dist-αβ (λ Q → Q ⊧ neg-Form ϕ) (λ Q → Q ⊧ ϕ)
  (λ V nϕ mϕ → dist-Log ϕ V mϕ nϕ) (P) o Pmϕ Pnegϕ
dist-Log (clo-Form (atom x)) P Pmϕ Pnegϕ = dist-Log x P Pmϕ Pnegϕ
dist-Log (clo-Form (x Test.∧ x₁)) P (fst , snd) (inj₁ y) = dist-Log (clo-Form x) P fst y
dist-Log (clo-Form (x Test.∧ x₁)) P (fst , snd) (inj₂ y) = dist-Log (clo-Form x₁) P snd y
dist-Log (clo-Form (x Test.∨ x₁)) P (inj₁ y) (fst , snd) = dist-Log (clo-Form x) P y fst
dist-Log (clo-Form (x Test.∨ x₁)) P (inj₂ y) (fst , snd) = dist-Log (clo-Form x₁) P y snd
dist-Log (clo-Form (⋁ x)) P (n , C) Pnegϕ = dist-Log (clo-Form (x n)) P C (Pnegϕ n)
dist-Log (clo-Form (⋀ x)) P Pmϕ (n , C) = dist-Log (clo-Form (x n)) P (Pmϕ n) C



Log-CL-Order : (a : Bool) → (τ : Aty) → (P Q : A-term a τ) → Set
Log-CL-Order a τ P Q = (ϕ : A-form a τ) → ((P ⊧ neg-Form ϕ) ⊎ (Q ⊧ ϕ))

CL-correct :  {a : Bool} → {τ : Aty} → (P Q : A-term a τ) → (Log-CL-Order a τ P Q) → (Log-Order a τ P Q)
CL-correct P Q hypo ϕ x with (hypo ϕ)
... | inj₁ x₁ = ⊥-elim (dist-Log ϕ P x x₁)
... | inj₂ y = y
