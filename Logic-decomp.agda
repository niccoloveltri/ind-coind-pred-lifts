open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool

module Logic-decomp {Sig : Set} (ar : Sig → Set)
             (O : Set) (πl : O → Bool)
             (πn : (k : Sig) → O → Test (ar k × O)) where

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

-- =======================================================
-- Sequencing results for the logic, using decomposability
-- =======================================================

import Logic
open Logic ar O πl πn public


-- Sequencing programs: the immediate termination of returned programs 
ty-seq : {τ : Aty} → A-cpt (U τ) → A-cpt τ
ty-seq M = μTree M

-- Decomposability preserved the logical order over the sequencing operation
ty-seq-preserve : {τ : Aty} → Decomposable → β-Decomposable
  → (P R : A-cpt (U τ)) → Log-Order cpt (U τ) P R → Log-Order cpt τ (ty-seq P) (ty-seq R)
ty-seq-preserve α-dec β-dec P R P<R (bas-Comα o ϕ) μPmϕ =
 subst (α o) (sym (μ-natural (λ V → V ⊧ ϕ) R))
   (α-dec (mapTree (mapTree (λ V → V ⊧ ϕ)) P) (mapTree (mapTree (λ V → V ⊧ ϕ)) R)
     (λ o₁ os x → subst (α o₁) (sym
       (functTree (mapTree (λ V → V ⊧ ϕ)) (λ t → liftTest (λ o' → α o' t) os) R))
       (monotone (λ x₁ → x₁ ⊧ (bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comα o₁ ϕ) os))))
         (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V → V ⊧ ϕ) x₁)) os)
           (λ a x₁ → subst (λ z → z) (sym (liftnatTest (λ o₂ → bas-Comα o₂ ϕ) (_⊧_ a) os))
           (subst (λ z → z) (sym (clo-Form-eq (functorTest (λ o₂ → bas-Comα o₂ ϕ) os) a))
           x₁))
        R o₁ (P<R (bas-Comα o₁ (bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comα o₁ ϕ) os))))
        (monotone (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V → V ⊧ ϕ) x₁)) os)
         (λ x₁ → x₁ ⊧ bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comα o₁ ϕ) os)))
         (λ a x₁ → subst (λ z → z) (clo-Form-eq (functorTest (λ o₂ → bas-Comα o₂ ϕ) os) a)
         (subst (λ z → z) (liftnatTest (λ o₂ → bas-Comα o₂ ϕ) (_⊧_ a) os) x₁))
       P o₁
       (subst (α o₁)
          (functTree (mapTree (λ V → V ⊧ ϕ))
           (λ t → liftTest (λ o' → α o' t) os) P)
       x)))))
   o (subst (α o) (μ-natural (λ V → V ⊧ ϕ) P) μPmϕ))
ty-seq-preserve α-dec β-dec P R P<R (bas-Comβ o ϕ) μPmϕ =
 subst (β ∞ o) (sym (μ-natural (λ V → V ⊧ ϕ) R))
   (β-dec (mapTree (mapTree (λ V → V ⊧ ϕ)) P) (mapTree (mapTree (λ V → V ⊧ ϕ)) R)
     (λ o₁ os x → subst (β ∞ o₁) (sym
       (functTree (mapTree (λ V → V ⊧ ϕ)) (λ t → liftTest (λ o' → β ∞ o' t) os) R))
       (β-monotone (λ x₁ → x₁ ⊧ (bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comβ o₁ ϕ) os))))
         (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V → V ⊧ ϕ) x₁)) os)
           (λ a x₁ → subst (λ z → z) (sym (liftnatTest (λ o₂ → bas-Comβ o₂ ϕ) (_⊧_ a) os))
           (subst (λ z → z) (sym (clo-Form-eq (functorTest (λ o₂ → bas-Comβ o₂ ϕ) os) a))
           x₁))
        R o₁ (P<R (bas-Comβ o₁ (bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comβ o₁ ϕ) os))))
        (β-monotone (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V → V ⊧ ϕ) x₁)) os)
         (λ x₁ → x₁ ⊧ bas-Thu (clo-Form (functorTest (λ o₁ → bas-Comβ o₁ ϕ) os)))
         (λ a x₁ → subst (λ z → z) (clo-Form-eq (functorTest (λ o₂ → bas-Comβ o₂ ϕ) os) a)
         (subst (λ z → z) (liftnatTest (λ o₂ → bas-Comβ o₂ ϕ) (_⊧_ a) os) x₁))
       P o₁
       (subst (β ∞ o₁)
          (functTree (mapTree (λ V → V ⊧ ϕ))
           (λ t → liftTest (λ o' → β ∞ o' t) os) P)
       x)))))
   o (subst (β ∞ o) (μ-natural (λ V → V ⊧ ϕ) P) μPmϕ))
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (atom x)) μPmϕ =
  ty-seq-preserve α-dec β-dec P R P<R x μPmϕ
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (x ∧ x₁)) (fst , snd) =
  (ty-seq-preserve α-dec β-dec P R P<R (clo-Form x) fst) ,
  ( ty-seq-preserve α-dec β-dec P R P<R (clo-Form x₁) snd)
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (x ∨ x₁)) (inj₁ x₂) =
  inj₁ (ty-seq-preserve α-dec β-dec P R P<R (clo-Form x) x₂)
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (x ∨ x₁)) (inj₂ y) =
  inj₂ (ty-seq-preserve α-dec β-dec P R P<R (clo-Form x₁) y)
ty-seq-preserve α-dec β-dec P R P<R (clo-Form val) tt = tt
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (⋁ x)) (n , μPmϕ) =
  n ,  (ty-seq-preserve α-dec β-dec P R P<R (clo-Form (x n)) μPmϕ)
ty-seq-preserve α-dec β-dec P R P<R (clo-Form (⋀ x)) μPmϕ =
  λ n →  ty-seq-preserve α-dec β-dec P R P<R (clo-Form (x n)) (μPmϕ n)


-- Let-binding
ty-let : {τ σ : Aty} → A-cpt τ → A-val (τ ⇒ σ) → A-cpt σ
ty-let M V = KleisTree V M

-- Uncurrying and Currying functions
ty-uncurry : {τ₀ τ₁ ρ : Aty} → A-val (τ₀ ⇒ (τ₁ ⇒ ρ)) → A-val ((τ₀ ⊗ τ₁) ⇒ ρ)
ty-uncurry f (V , W) = ty-let (f V) (λ g → g W)

ty-curry : {τ₀ τ₁ ρ : Aty} → A-val ((τ₀ ⊗ τ₁) ⇒ ρ) → A-val (τ₀ ⇒ (τ₁ ⇒ ρ))
ty-curry f V = leaf (λ W → f (V , W))

-- Decomposability implies preservation of logical order over the Uncurrying operation
uncurry-preserve : {τ₀ τ₁ ρ : Aty} → Decomposable → β-Decomposable
  → (f g : A-val (τ₀ ⇒ (τ₁ ⇒ ρ)))
  → Log-Order val (τ₀ ⇒ (τ₁ ⇒ ρ)) f g
  → Log-Order val ((τ₀ ⊗ τ₁) ⇒ ρ) (ty-uncurry f) (ty-uncurry g)
uncurry-preserve decom β-decom f g assum (bas-Fun (V , W) (bas-Comα x ϕ)) hypo =
  subst (λ z → α x z) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree (λ g₁ → g₁ W) (g V))))
  (subst (λ z → α x (μTree z))
     (sym (functTree (λ g₁ → g₁ W) (mapTree (λ V₁ → V₁ ⊧ ϕ)) (g V)))
  (decom (mapTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W)) (f V))
     (mapTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W)) (g V))
     (λ o os hyp →
        subst (λ z → α o z) (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W))
                                            (λ t → liftTest (λ o' → α o' t) os) (g V)))
        (subst (λ z → α o (mapTree z (g V)))
           (sym (funext (λ x₁ → clo-Form-eq2 os (λ o' → bas-Comα o' ϕ) (x₁ W))))
           (assum (bas-Fun V (bas-Comα o
                  (bas-Fun W (clo-Form (functorTest (λ z → bas-Comα z ϕ) os)))))
        (subst (λ z → α o (mapTree z (f V)))
           (funext (λ x₁ → clo-Form-eq2 os (λ o' → bas-Comα o' ϕ) (x₁ W)))
        (subst (λ z → α o z)
           (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W))
            (λ t → liftTest (λ o' → α o' t) os) (f V))
           hyp)))))
     x
     (subst (λ z → α x (μTree z))
     (functTree (λ g₁ → g₁ W) (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
     (subst (λ z → α x z) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree (λ g₁ → g₁ W) (f V))) hypo))))
uncurry-preserve decom β-decom f g assum (bas-Fun (V , W) (bas-Comβ x ϕ)) hypo =
  subst (λ z → β ∞ x z) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree (λ g₁ → g₁ W) (g V))))
  (subst (λ z → β ∞ x (μTree z))
     (sym (functTree (λ g₁ → g₁ W) (mapTree (λ V₁ → V₁ ⊧ ϕ)) (g V)))
  (β-decom (mapTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W)) (f V))
     (mapTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W)) (g V))
     (λ o os hyp →
        subst (λ z → β ∞ o z) (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W))
                                            (λ t → liftTest (λ o' → β ∞ o' t) os) (g V)))
        (subst (λ z → β ∞ o (mapTree z (g V)))
           (sym (funext (λ x₁ → clo-Form-eq2 os (λ o' → bas-Comβ o' ϕ) (x₁ W))))
           (assum (bas-Fun V (bas-Comβ o
                  (bas-Fun W (clo-Form (functorTest (λ z → bas-Comβ z ϕ) os)))))
        (subst (λ z → β ∞ o (mapTree z (f V)))
           (funext (λ x₁ → clo-Form-eq2 os (λ o' → bas-Comβ o' ϕ) (x₁ W)))
        (subst (λ z → β ∞ o z)
           (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (x₁ W))
            (λ t → liftTest (λ o' → β ∞ o' t) os) (f V))
           hyp)))))
    x
    (subst (λ z → β ∞ x (μTree z))
    (functTree (λ g₁ → g₁ W) (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
    (subst (λ z → β ∞ x z) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree (λ g₁ → g₁ W) (f V))) hypo))))
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (atom x))) hypo =
  uncurry-preserve decom β-decom f g assum (bas-Fun V x) hypo
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (x ∨ x₁))) (inj₁ a) =
  inj₁ (uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form x)) a)
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (x ∨ x₁))) (inj₂ b) =
  inj₂ (uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form x₁)) b)
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (x ∧ x₁))) (a , b) =
  (uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form x)) a) ,
  uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form x₁)) b
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form val)) hypo = tt
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (⋁ x))) (n , hypo) =
  n , (uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (x n))) hypo)
uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (⋀ x))) hypo n =
  uncurry-preserve decom β-decom f g assum (bas-Fun V (clo-Form (x n))) (hypo n)
uncurry-preserve decom β-decom f g assum (clo-Form (atom x)) hypo =
  uncurry-preserve decom β-decom f g assum x hypo
uncurry-preserve decom β-decom f g assum (clo-Form (x ∧ y)) (a , b) =
  (uncurry-preserve decom β-decom f g assum (clo-Form x) a) ,
  (uncurry-preserve decom β-decom f g assum (clo-Form y) b)
uncurry-preserve decom β-decom f g assum (clo-Form (x ∨ y)) (inj₁ a) =
  inj₁ (uncurry-preserve decom β-decom f g assum (clo-Form x) a)
uncurry-preserve decom β-decom f g assum (clo-Form (x ∨ y)) (inj₂ b) =
  inj₂ (uncurry-preserve decom β-decom f g assum (clo-Form y) b)
uncurry-preserve decom β-decom f g assum (clo-Form val) tt = tt
uncurry-preserve decom β-decom f g assum (clo-Form (⋁ x)) (n , hypo) =
  n , uncurry-preserve decom β-decom f g assum (clo-Form (x n)) hypo
uncurry-preserve decom β-decom f g assum (clo-Form (⋀ x)) hypo n =
  uncurry-preserve decom β-decom f g assum (clo-Form (x n)) (hypo n)

-- Helpful lemmas
boolC : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
boolC cpt = inj₂ refl
boolC val = inj₁ refl

β-leaf-help : {τ : Aty} → (V : A-val τ) → (o : O) → (ϕ : A-form val τ)
  → (leaf V ⊧ bas-Comβ o ϕ) → (πl o ≡ true) → (V ⊧ ϕ)
β-leaf-help V o ϕ (β-leaf x) no = x
β-leaf-help V o ϕ (β-exep x) no with subst (λ z → (z ≡ false)) no x
... | ()

-- Function formulas distribute over test-formulas
bas-Fun-Clo-com : {σ τ : Aty} → (V : A-val (σ ⇒ τ))
  → (W : A-val σ) → (tes : Test (A-form cpt τ))
  → (V ⊧ clo-Form (functorTest (λ ϕ → bas-Fun W ϕ) tes))
  → (V ⊧ bas-Fun W (clo-Form tes))
bas-Fun-Clo-com V W (atom x) assum = assum
bas-Fun-Clo-com V W (tes Test.∧ tes₁) (fst , snd) = (bas-Fun-Clo-com V W tes fst) ,
  (bas-Fun-Clo-com V W tes₁ snd)
bas-Fun-Clo-com V W (tes Test.∨ tes₁) (inj₁ x) = inj₁ (bas-Fun-Clo-com V W tes x)
bas-Fun-Clo-com V W (tes Test.∨ tes₁) (inj₂ y) = inj₂ (bas-Fun-Clo-com V W tes₁ y)
bas-Fun-Clo-com V W val tt = tt
bas-Fun-Clo-com V W (⋁ x) (n , assum) = n , (bas-Fun-Clo-com V W (x n) assum)
bas-Fun-Clo-com V W (⋀ x) assum = λ n → bas-Fun-Clo-com V W (x n) (assum n)

bas-Fun-Clo-com2 : {σ τ : Aty} → (V : A-val (σ ⇒ τ))
  → (W : A-val σ) → (tes : Test (A-form cpt τ))
  → (V ⊧ bas-Fun W (clo-Form tes))
  → (V ⊧ clo-Form (functorTest (λ ϕ → bas-Fun W ϕ) tes))
bas-Fun-Clo-com2 V W (atom x) assum = assum
bas-Fun-Clo-com2 V W (tes Test.∧ tes₁) (fst , snd) = (bas-Fun-Clo-com2 V W tes fst) ,
  (bas-Fun-Clo-com2 V W tes₁ snd)
bas-Fun-Clo-com2 V W (tes Test.∨ tes₁) (inj₁ x) = inj₁ (bas-Fun-Clo-com2 V W tes x)
bas-Fun-Clo-com2 V W (tes Test.∨ tes₁) (inj₂ y) = inj₂ (bas-Fun-Clo-com2 V W tes₁ y)
bas-Fun-Clo-com2 V W val tt = tt
bas-Fun-Clo-com2 V W (⋁ x) (n , assum) = n , bas-Fun-Clo-com2 V W (x n) assum
bas-Fun-Clo-com2 V W (⋀ x) assum = λ n → bas-Fun-Clo-com2 V W (x n) (assum n)


-- α-decomposition for describing formulas for arbitrary types
decoα-Form : {τ : Aty} → (πd : deco) → (o : O) → (ϕ : A-form val τ) → (A-form cpt (U τ))
decoα-Form πd o ϕ = clo-Form
  (functorTest (λ p → bas-Comα (proj₁ p) (bas-Thu (bas-Comα (proj₂ p) ϕ))) (πd o))

-- β-decomposition for describing formulas for arbitrary types
decoβ-Form : {τ : Aty} → (πd : deco) → (o : O) → (ϕ : A-form val τ) → (A-form cpt (U τ))
decoβ-Form πd o ϕ = clo-Form
  (functorTest (λ p → bas-Comβ (proj₁ p) (bas-Thu (bas-Comβ (proj₂ p) ϕ))) (πd o))

-- α and β decompositions are sound for proving properties of sequenced programs
decoα-Form-seq : (πd : deco) (as : deco-α-seq πd) → (τ : Aty) → (o : O) → (ϕ : A-form val τ)
  → (M : A-cpt (U τ)) → (pr : (M ⊧ (decoα-Form πd o ϕ)))
  → (ty-seq M ⊧ bas-Comα o ϕ)
decoα-Form-seq πd as τ o ϕ M pr =
  subst (α o) (sym (μ-natural (λ V → V ⊧ ϕ) M))
    (as o (mapTree (λ d → mapTree (λ V → V ⊧ ϕ) d) M)
    (subst (λ z → liftTest z (πd o))
       (funext
        (λ x →
           cong (α (proj₁ x))
           (sym (functTree (λ d → mapTree (λ V → V ⊧ ϕ) d) (α (proj₂ x)) M))))
       (subst (λ z → z) (sym (clo-Form-eq2 (πd o) (λ x → bas-Comα (proj₁ x)
         (bas-Thu (bas-Comα (proj₂ x) ϕ))) M)) pr)))

decoβ-Form-seq : (πd : deco) (as : deco-β-seq πd) → (τ : Aty) → (o : O) → (ϕ : A-form val τ)
  → (M : A-cpt (U τ)) → (pr : (M ⊧ (decoβ-Form πd o ϕ)))
  → (ty-seq M ⊧ bas-Comβ o ϕ)
decoβ-Form-seq πd as τ o ϕ M pr =
  subst (β ∞ o) (sym (μ-natural (λ V → V ⊧ ϕ) M))
    (as o (mapTree (λ d → mapTree (λ V → V ⊧ ϕ) d) M)
    (subst (λ z → liftTest z (πd o))
       (funext
        (λ x →
           cong (β ∞ (proj₁ x))
           (sym (functTree (λ d → mapTree (λ V → V ⊧ ϕ) d) (β ∞ (proj₂ x)) M))))
       (subst (λ z → z) (sym (clo-Form-eq2 (πd o) (λ x → bas-Comβ (proj₁ x)
         (bas-Thu (bas-Comβ (proj₂ x) ϕ))) M)) pr)))

-- α and β decompositions are complete for proving properties of sequenced programs
decoα-Form-unf : (πd : deco) (as : deco-α-unf πd) → (τ : Aty) → (o : O) → (ϕ : A-form val τ)
  → (M : A-cpt (U τ)) → (pr : ty-seq M ⊧ bas-Comα o ϕ)
  → (M ⊧ (decoα-Form πd o ϕ))
decoα-Form-unf πd as τ o ϕ M pr = subst (λ z → z)
  (clo-Form-eq2 (πd o) (λ x → bas-Comα (proj₁ x) (bas-Thu (bas-Comα (proj₂ x) ϕ))) M)
     (subst (λ z → liftTest z (πd o))
        (funext
         (λ x →
            cong (α (proj₁ x))
            (functTree (λ d → mapTree (λ V → V ⊧ ϕ) d) (α (proj₂ x)) M)))
        (as o (mapTree (λ d → mapTree (λ V → V ⊧ ϕ) d) M)
          (subst (α o) (μ-natural (λ V → V ⊧ ϕ) M) pr)))

decoβ-Form-unf : (πd : deco) (as : deco-β-unf πd) → (τ : Aty) → (o : O) → (ϕ : A-form val τ)
  → (M : A-cpt (U τ)) → (pr : ty-seq M ⊧ bas-Comβ o ϕ)
  → (M ⊧ (decoβ-Form πd o ϕ))
decoβ-Form-unf πd as τ o ϕ M pr = subst (λ z → z)
  (clo-Form-eq2 (πd o) (λ x → bas-Comβ (proj₁ x) (bas-Thu (bas-Comβ (proj₂ x) ϕ))) M)
     (subst (λ z → liftTest z (πd o))
        (funext
         (λ x →
            cong (β ∞ (proj₁ x))
            (functTree (λ d → mapTree (λ V → V ⊧ ϕ) d) (β ∞ (proj₂ x)) M)))
        (as o (mapTree (λ d → mapTree (λ V → V ⊧ ϕ) d) M)
          (subst (β ∞ o) (μ-natural (λ V → V ⊧ ϕ) M) pr)))


-- The Curry operations preserves logical ordering, even in the absence of decomposability
curry-preserve : {τ₀ τ₁ ρ : Aty}
  → (f g : A-val ((τ₀ ⊗ τ₁) ⇒ ρ))
  → Log-Order val ((τ₀ ⊗ τ₁) ⇒ ρ) f g
  → Log-Order val (τ₀ ⇒ (τ₁ ⇒ ρ)) (ty-curry f) (ty-curry g)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (bas-Fun W ϕ))) (leaf-α x x₂) =
  leaf-α x (assum (bas-Fun (V , W) ϕ) x₂)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (atom x₃)))) (leaf-α x x₂) =
  curry-preserve f g assum (bas-Fun V (bas-Comα x₁ x₃)) (leaf-α x x₂)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (y ∧ z)))) (leaf-α x (a , b))
  with (curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form y))) (leaf-α x a) ,
    curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form z))) (leaf-α x b))
... | leaf-α v Q , leaf-α w R = leaf-α x (Q , R)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (y ∨ z)))) (leaf-α x (inj₁ a))
  with (curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form y))) (leaf-α x a))
... | leaf-α v Q = leaf-α x (inj₁ Q)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (y ∨ z)))) (leaf-α x (inj₂ b))
  with (curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form z))) (leaf-α x b))
... | leaf-α v Q = leaf-α x (inj₂ Q)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form val))) (leaf-α x x₂) =
  leaf-α x tt
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (⋁ F)))) (leaf-α x (n , a))
  with (curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (F n)))) (leaf-α x a))
... | leaf-α v Q = leaf-α x (n , Q)
curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (⋀ F)))) (leaf-α x x₂)
  = leaf-α x (λ n → lem (curry-preserve f g assum (bas-Fun V (bas-Comα x₁ (clo-Form (F n))))
                                        (leaf-α x (x₂ n)))) where
    lem : {n : ℕ} → α x₁ (leaf ((λ W → g (V , W)) ⊧ clo-Form (F n)))
      → (λ W → g (V , W)) ⊧ clo-Form (F n)
    lem (leaf-α x x₁) = x₁
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ ϕ)) (β-exep x) = β-exep x
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (bas-Fun W ϕ))) (β-leaf x) =
  β-leaf (assum (bas-Fun (V , W) ϕ) x)
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (atom x₃)))) (β-leaf x₂) =
  curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ x₃)) (β-leaf x₂)
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (y ∧ z)))) (β-leaf (a , b))
  with (curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form y))) (β-leaf a) ,
    curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form z))) (β-leaf b))
... | β-exep v , w = β-exep v
... | β-leaf Q , β-exep v = β-exep v
... | β-leaf Q , β-leaf R = β-leaf (Q , R)
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (y ∨ z)))) (β-leaf (inj₁ a))
  with (curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form y))) (β-leaf a))
... | β-leaf Q = β-leaf (inj₁ Q)
... | β-exep v = β-exep v
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (y ∨ z)))) (β-leaf (inj₂ b))
  with (curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form z))) (β-leaf b))
... | β-leaf Q = β-leaf (inj₂ Q)
... | β-exep v = β-exep v
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form val))) (β-leaf x₂) =
  β-leaf tt
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (⋁ F)))) (β-leaf (n , a))
  with (curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (F n)))) (β-leaf a))
... | β-leaf Q = β-leaf (n , Q)
... | β-exep v = β-exep v
curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (⋀ F)))) (β-leaf x₂)
  with λ n → curry-preserve f g assum (bas-Fun V (bas-Comβ x₁ (clo-Form (F n))))
                            (β-leaf (x₂ n))
... | pip with boolC (πl x₁)
... | inj₁ x = β-leaf (λ n → β-leaf-help (λ W → g (V , W)) x₁ (clo-Form (F n)) (pip n) x)
... | inj₂ y = β-exep y
curry-preserve f g assum (bas-Fun V (clo-Form (atom x₁))) x =
  curry-preserve f g assum (bas-Fun V x₁) x
curry-preserve f g assum (bas-Fun V (clo-Form (x₁ Test.∧ x₂))) (fst , snd) =
  curry-preserve f g assum (bas-Fun V (clo-Form x₁)) fst ,
  curry-preserve f g assum (bas-Fun V (clo-Form x₂)) snd
curry-preserve f g assum (bas-Fun V (clo-Form (x₁ Test.∨ x₂))) (inj₁ x) =
  inj₁ (curry-preserve f g assum (bas-Fun V (clo-Form x₁)) x)
curry-preserve f g assum (bas-Fun V (clo-Form (x₁ Test.∨ x₂))) (inj₂ y) =
  inj₂ (curry-preserve f g assum (bas-Fun V (clo-Form x₂)) y)
curry-preserve f g assum (bas-Fun V (clo-Form val)) tt = tt
curry-preserve f g assum (bas-Fun V (clo-Form (⋁ x₁))) (n , z) =
  n , curry-preserve f g assum (bas-Fun V (clo-Form (x₁ n))) z
curry-preserve f g assum (bas-Fun V (clo-Form (⋀ x₁))) x =
  λ n → curry-preserve f g assum (bas-Fun V (clo-Form (x₁ n))) (x n)
curry-preserve f g assum (clo-Form (atom x₁)) x = curry-preserve f g assum x₁ x
curry-preserve f g assum (clo-Form (x₁ Test.∧ x₂)) (fst , snd) =
  (curry-preserve f g assum (clo-Form x₁) fst) ,
  (curry-preserve f g assum (clo-Form x₂) snd)
curry-preserve f g assum (clo-Form (x₁ Test.∨ x₂)) (inj₁ x) =
  inj₁ (curry-preserve f g assum (clo-Form x₁) x)
curry-preserve f g assum (clo-Form (x₁ Test.∨ x₂)) (inj₂ y) =
  inj₂ (curry-preserve f g assum (clo-Form x₂) y)
curry-preserve f g assum (clo-Form val) tt = tt
curry-preserve f g assum (clo-Form (⋁ x₁)) (n , x) =
  n , curry-preserve f g assum (clo-Form (x₁ n)) x
curry-preserve f g assum (clo-Form (⋀ x₁)) x =
  λ n → curry-preserve f g assum (clo-Form (x₁ n)) (x n)



-- The following development considers proof techniques for preservation over
-- program compositions
cong-prop : {σ τ : Aty} → A-val (σ ⇒ τ) → Set
cong-prop f = ∀ (ϕ : A-form cpt _) → ∃ λ ψ → ∀ (V : A-val _) →
  ((V ⊧ ψ) → ((f V) ⊧ ϕ)) × (((f V) ⊧ ϕ) → (V ⊧ ψ))

congruent : {σ τ : Aty} → A-val (σ ⇒ τ) → Set
congruent {σ} f = ∀ (V W : A-term val σ)
  → Log-Order val σ V W → Log-Order cpt _ (f V) (f W)

cp-congruent : {σ τ : Aty} → (f : A-val (σ ⇒ τ)) → cong-prop f → congruent f
cp-congruent f co-f V W V<W ϕ fVmϕ = proj₁ (proj₂ (co-f ϕ) W)
  (V<W (proj₁ (co-f ϕ)) (proj₂ (proj₂ (co-f ϕ) V) fVmϕ))

compose : {σ τ ρ : Aty} → (f : A-val (σ ⇒ τ)) → (g : A-val (τ ⇒ ρ)) → A-val (σ ⇒ ρ)
compose f g V = KleisTree g (f V)

-- Preservation of logical order over post-composition of programs (f ∘ _)
compose-pres-r : {σ τ ρ : Aty} → Decomposable → β-Decomposable
  → (f : A-val (σ ⇒ τ)) → (g₀ g₁ : A-val (τ ⇒ ρ))
  → (Log-Order _ _ g₀ g₁) → Log-Order _ _ (compose f g₀) (compose f g₁)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (bas-Comα o ϕ)) g₀∘f⊧ϕ =
  subst (α o) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g₁ (f V))))
  (subst (λ z → α o (μTree z)) (sym (functTree g₁ (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V)))
    (α-dec (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x)) (f V))
           (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x)) (f V))
      (λ o₁ os x →
      subst (α o₁)
        (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x₁))
             (λ t → liftTest (λ o' → α o' t) os) (f V)))
        (monotone (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x₁))) os)
                  (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x₁))) os)
           (λ W x₁ → subst (λ z → z)
                       (sym (liftnatTest (λ o' → bas-Comα o' ϕ) (λ ψ → g₁ W ⊧ ψ) os))
              (liftfunTest _ (λ ψ → g₀ W ⊧ ψ) (λ ψ → g₁ W ⊧ ψ)
                 (functorTest (λ o' → bas-Comα o' ϕ) os) (λ a x₂ → g₀<g₁ (bas-Fun W a) x₂)
           (subst (λ z → z)
              (liftnatTest (λ o' → bas-Comα o' ϕ) (λ ψ → g₀ W ⊧ ψ) os)
        x₁)))
        (f V) o₁
        (subst (α o₁)
           (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x₁))
            (λ t → liftTest (λ o' → α o' t) os) (f V))
         x)))
    o
  (subst (λ z → α o (μTree z)) (functTree g₀ (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
  (subst (α o) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g₀ (f V))) g₀∘f⊧ϕ))))
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (bas-Comβ o ϕ)) g₀∘f⊧ϕ =
  subst (β ∞ o) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g₁ (f V))))
  (subst (λ z → β ∞ o (μTree z)) (sym (functTree g₁ (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V)))
    (β-dec (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x)) (f V))
           (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x)) (f V))
      (λ o₁ os x →
      subst (β ∞ o₁)
        (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x₁))
             (λ t → liftTest (λ o' → β ∞ o' t) os) (f V)))
        (β-monotone (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x₁))) os)
                  (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g₁ x₁))) os)
           (λ W x₁ → subst (λ z → z)
                       (sym (liftnatTest (λ o' → bas-Comβ o' ϕ) (λ ψ → g₁ W ⊧ ψ) os))
              (liftfunTest _ (λ ψ → g₀ W ⊧ ψ) (λ ψ → g₁ W ⊧ ψ)
                 (functorTest (λ o' → bas-Comβ o' ϕ) os) (λ a x₂ → g₀<g₁ (bas-Fun W a) x₂)
           (subst (λ z → z)
              (liftnatTest (λ o' → bas-Comβ o' ϕ) (λ ψ → g₀ W ⊧ ψ) os)
        x₁)))
        (f V) o₁
        (subst (β ∞ o₁)
           (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g₀ x₁))
            (λ t → liftTest (λ o' → β ∞ o' t) os) (f V))
         x)))
    o
  (subst (λ z → β ∞ o (μTree z)) (functTree g₀ (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
  (subst (β ∞ o) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g₀ (f V))) g₀∘f⊧ϕ))))
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (atom x))) g₀∘f⊧ϕ =
  compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V x) g₀∘f⊧ϕ
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (tes ∧ tes₁))) (fst , snd) =
  (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form tes)) fst) ,
  (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form tes₁)) snd)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (tes ∨ tes₁))) (inj₁ x) =
  inj₁ (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form tes)) x)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (tes ∨ tes₁))) (inj₂ y) =
  inj₂ (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form tes₁)) y)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form val)) tt = tt
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (⋁ x))) (n , g₀∘f⊧ϕ) =
  n , compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (x n))) g₀∘f⊧ϕ
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (⋀ x))) g₀∘f⊧ϕ =
  λ n → compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (bas-Fun V (clo-Form (x n))) (g₀∘f⊧ϕ n)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (atom x)) g₀∘f⊧ϕ =
  compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ x g₀∘f⊧ϕ
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (tes ∧ tes₁)) (fst , snd) =
  (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form tes) fst) ,
  (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form tes₁) snd)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (tes ∨ tes₁)) (inj₁ x) =
  inj₁ (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form tes) x)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (tes ∨ tes₁)) (inj₂ y) =
  inj₂ (compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form tes₁) y)
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form val) tt = tt
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (⋁ x)) (n , g₀∘f⊧ϕ) =
  n , compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (x n)) g₀∘f⊧ϕ
compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (⋀ x)) g₀∘f⊧ϕ =
  λ n → compose-pres-r α-dec β-dec f g₀ g₁ g₀<g₁ (clo-Form (x n)) (g₀∘f⊧ϕ n)

-- Preservations of logical ordering over precomposition of programs (_ ∘ g)
-- Uses the congruent pullback property.
compose-pres-l : {σ τ ρ : Aty} → Decomposable → β-Decomposable
  → (f f' : A-val (σ ⇒ τ)) → (g : A-val (τ ⇒ ρ)) → (cong-prop g)
  → (Log-Order _ _ f f') → Log-Order _ _ (compose f g) (compose f' g)
compose-pres-l α-dec β-dec f f' g co-g f<f' (bas-Fun V (bas-Comα o ϕ)) fgmϕ =
  subst (α o) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g (f' V))))
  (subst (λ z → α o (μTree z)) (sym (functTree g (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f' V)))
    (α-dec (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x)) (f V))
    (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x)) (f' V))
      (λ o₁ os x → subst (α o₁) (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))
                       (λ t → liftTest (λ o' → α o' t) os) (f' V)))
      (monotone (λ V₁ → V₁ ⊧ proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comα o' ϕ) os))))
         (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))) os)
         (λ a x₁ → subst (λ z → z)
                     (sym (liftnatTest (λ o' → bas-Comα o' ϕ) (λ ψ → g a ⊧ ψ) os))
         (subst (λ z → z)
            (sym (clo-Form-eq (functorTest (λ o' → bas-Comα o' ϕ) os) (g a)))
           (proj₁ (proj₂ (co-g (clo-Form (functorTest (λ o' → (bas-Comα o' ϕ)) os))) a) x₁)))
         (f' V) o₁ (f<f' (bas-Fun V (bas-Comα o₁
                        (proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comα o' ϕ) os))))))
         (monotone
            (λ x₁ → liftTest (λ o' → α o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))) os)
            (λ V₁ → V₁ ⊧ proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comα o' ϕ) os))))
            (λ a x₁ → proj₂ (proj₂
                    (co-g (clo-Form (functorTest (λ o' → bas-Comα o' ϕ) os))) a)
            (subst (λ z → z) (clo-Form-eq (functorTest (λ o' → bas-Comα o' ϕ) os) (g a))
            (subst (λ z → z) (liftnatTest (λ o' → bas-Comα o' ϕ) (λ ψ → g a ⊧ ψ) os) x₁)))
      (f V) o₁ (subst (α o₁) (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))
                   (λ t → liftTest (λ o' → α o' t) os) (f V)) x))))) o
      (subst (λ z → α o (μTree z)) (functTree g (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
      ((subst (α o) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g (f V))) fgmϕ)))))
compose-pres-l α-dec β-dec f f' g co-g f<f' (bas-Fun V (bas-Comβ o ϕ)) fgmϕ =
  subst (β ∞ o) (sym (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g (f' V))))
  (subst (λ z → β ∞ o (μTree z)) (sym (functTree g (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f' V)))
    (β-dec (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x)) (f V))
    (mapTree (λ x → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x)) (f' V))
      (λ o₁ os x → subst (β ∞ o₁) (sym (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))
                       (λ t → liftTest (λ o' → β ∞ o' t) os) (f' V)))
    (β-monotone (λ V₁ → V₁ ⊧ proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comβ o' ϕ) os))))
         (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))) os)
         (λ a x₁ → subst (λ z → z)
                     (sym (liftnatTest (λ o' → bas-Comβ o' ϕ) (λ ψ → g a ⊧ ψ) os))
         (subst (λ z → z)
            (sym (clo-Form-eq (functorTest (λ o' → bas-Comβ o' ϕ) os) (g a)))
           (proj₁ (proj₂ (co-g (clo-Form (functorTest (λ o' → (bas-Comβ o' ϕ)) os))) a) x₁)))
         (f' V) o₁ (f<f' (bas-Fun V (bas-Comβ o₁
                        (proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comβ o' ϕ) os))))))
         (β-monotone
            (λ x₁ → liftTest (λ o' → β ∞ o' (mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))) os)
            (λ V₁ → V₁ ⊧ proj₁ (co-g (clo-Form (functorTest (λ o' → bas-Comβ o' ϕ) os))))
            (λ a x₁ → proj₂ (proj₂
                    (co-g (clo-Form (functorTest (λ o' → bas-Comβ o' ϕ) os))) a)
            (subst (λ z → z) (clo-Form-eq (functorTest (λ o' → bas-Comβ o' ϕ) os) (g a))
            (subst (λ z → z) (liftnatTest (λ o' → bas-Comβ o' ϕ) (λ ψ → g a ⊧ ψ) os) x₁)))
      (f V) o₁ (subst (β ∞ o₁) (functTree (λ x₁ → mapTree (λ V₁ → V₁ ⊧ ϕ) (g x₁))
                   (λ t → liftTest (λ o' → β ∞ o' t) os) (f V)) x))))) o
      (subst (λ z → β ∞ o (μTree z)) (functTree g (mapTree (λ V₁ → V₁ ⊧ ϕ)) (f V))
      ((subst (β ∞ o) (μ-natural (λ V₁ → V₁ ⊧ ϕ) (mapTree g (f V))) fgmϕ)))))
-- variable names don't make sense below, as they are copied from above. But they work.
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (atom x))) g₀∘f⊧ϕ =
  compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V x) g₀∘f⊧ϕ
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (tes ∧ tes₁)))
  (fst , snd) =
  (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form tes)) fst) ,
  (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form tes₁)) snd)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (tes ∨ tes₁))) (inj₁ x) =
  inj₁ (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form tes)) x)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (tes ∨ tes₁))) (inj₂ y) =
  inj₂ (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form tes₁)) y)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form val)) tt = tt
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (⋁ x))) (n , g₀∘f⊧ϕ) =
  n , compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (x n))) g₀∘f⊧ϕ
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (⋀ x))) g₀∘f⊧ϕ =
  λ n → compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (bas-Fun V (clo-Form (x n))) (g₀∘f⊧ϕ n)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (atom x)) g₀∘f⊧ϕ =
  compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb x g₀∘f⊧ϕ
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (tes ∧ tes₁)) (fst , snd) =
  (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form tes) fst) ,
  (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form tes₁) snd)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (tes ∨ tes₁)) (inj₁ x) =
  inj₁ (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form tes) x)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (tes ∨ tes₁)) (inj₂ y) =
  inj₂ (compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form tes₁) y)
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form val) tt = tt
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (⋁ x)) (n , g₀∘f⊧ϕ) =
  n , compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (x n)) g₀∘f⊧ϕ
compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (⋀ x)) g₀∘f⊧ϕ =
  λ n → compose-pres-l α-dec β-dec f g₀ g₁ g₀<g₁ pb (clo-Form (x n)) (g₀∘f⊧ϕ n)
