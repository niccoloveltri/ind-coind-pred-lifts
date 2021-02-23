open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool hiding (_∧_; _∨_)

module Relators  {K : Set} (I : K → Set)
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


open import Pred-Lift-ab I O αl αn
open import Trees-Coinductive


-- Relator properties
rel-idin : ∀ {i} {A : Set} (R : A → A → Set i) → Set i
rel-idin R = (a : _) → R a a

rel-comp : ∀ {i} {A B C : Set} (R : A → B → Set i) (S : B → C → Set i) → A → C → Set i
rel-comp R S a c = Σ _ λ b → ((R a b) × (S b c))

rel-ord : ∀ {i} {A B : Set} (R S : A → B → Set i) → Set i
rel-ord R S = (a : _) → (b : _) → (R a b) → (S a b)

rel-tran : ∀ {i} {A : Set} (R : A → A → Set i) → Set i
rel-tran R = rel-ord (rel-comp R R) R

rel-preds : ∀ {i j} {A : Set} {B : Set} (R : A → B → Set i) → (P : A → Set j) → (Q : B → Set j) → Set (i ⊔ j)
rel-preds R P Q = (a : _) → (b : _) → (P a) → (R a b) → (Q b)

Right-Set : ∀ {i j} {A : Set} {B : Set} (R : A → B → Set i) (P : A → Set j) → B → Set (i ⊔ j)
Right-Set R P b = Σ _ (λ a → (P a) × (R a b))

rightset-is-rel : ∀ {i} {A : Set} {B : Set} (R : A → B → Set i) (P : A → Set i) → rel-preds R P (Right-Set R P)
rightset-is-rel R P a b Pa aRb = a , (Pa , aRb)

-- ==============================================
--   O-Relators
-- ==============================================


O-Relator : ∀ {i} {A : Set} {B : Set} (R : A → B → Set i) → (t₁ : Tree I A) → (t₂ : Tree I B) → Set (lsuc lzero ⊔ i)
O-Relator R t₁ t₂ = (P : _ → Set) → (Q : _ → Set) → (rel-preds R P Q) → (o : O) → (liftTree P o t₁) → (liftTree Q o t₂)

Relator-Id :   {A : Set} (R : A → A → Set) → (rel-idin R) → (rel-idin (O-Relator R))
Relator-Id R idR t P Q PorQ o assum = monotone P Q (λ a x → PorQ a a x (idR a)) t o assum

Relator-mono : {A B : Set} (R S : A → B → Set) → rel-ord R S → rel-ord (O-Relator R) (O-Relator S)
Relator-mono R S RorS ta tb assum   P Q P-S-Q o Pta = assum P Q (λ a b Pa aRb → P-S-Q a b Pa (RorS a b aRb)) o Pta

Relator-η : {A B : Set} (R : A → B → Set) → (a : A) → (b : B) → (R a b) → O-Relator R (ηTree I a) (ηTree I b)
Relator-η R a b aRb P Q x₁ o x₂ = mono-leaf (P a) (Q b) (λ s → x₁ a b s aRb) o x₂


-- Compositionality only at base level. Would work at all levels if either generlised or predicates and relations both use impredicative prop

Relator-comp : {A B C : Set} (R : A → B → Set) (S : B → C → Set) → rel-ord (rel-comp (O-Relator R) (O-Relator S)) (O-Relator (rel-comp R S))
Relator-comp R S ta tc (tb , taORtb , tbOStc) P Q P-RS-Q o taMoP = tbOStc (Right-Set R P) Q
             (λ b c Mb bSc → P-RS-Q (proj₁ Mb) c (proj₁ (proj₂ Mb)) (b , ((proj₂ (proj₂ Mb)) , bSc))) o
             (taORtb P (Right-Set R P) (λ a b Pa aRb → a , (Pa , aRb)) o taMoP)

Relator-tran : {A : Set} (R : A → A → Set) → (rel-tran R) → rel-tran (O-Relator R)
Relator-tran R R-tran ta tc x = Relator-mono (rel-comp R R) R R-tran ta tc (Relator-comp R R ta tc x)

-- Preservation over sequencing
Relator-μ : ∀ {i} {A B : Set} → Decomposable → (R : A → B → Set i) → (d₁ : Tree I (Tree I A)) → (d₂ : Tree I (Tree I B))
          →  O-Relator (O-Relator R) d₁ d₂ → O-Relator R (μTree d₁) (μTree d₂)
Relator-μ decom R da db daOORdb P Q P-R-Q o μdaMoP = subst (λ x → α o x) (sym (μ-natural Q db))
          (decom (mapTree (mapTree P) da) (mapTree (mapTree Q) db)
            (λ o' os da-M-o'osP → subst (λ x → α o' x) (sym (functTree (mapTree Q) (λ t → liftTest (λ o'' → α o'' t) os) db))
              (daOORdb (λ x → liftTest (λ o'' → α o'' (mapTree P x)) os) (λ x → liftTest (λ o'' → α o'' (mapTree Q x)) os)
                (λ ta tb V taORtb → base-test-lift (mapTree P ta) (mapTree Q tb) (λ o₁ x → taORtb P Q P-R-Q o₁ x) os V)
                o' (subst (λ x → α o' x) (functTree (mapTree P) (λ t → liftTest (λ o'' → α o'' t) os) da) da-M-o'osP)))
          o (subst (λ x → α o x) (μ-natural P da) μdaMoP))


