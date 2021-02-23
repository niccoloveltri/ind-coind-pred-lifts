{-# OPTIONS --type-in-type #-}

module Examples.Input where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∧_; _∨_) renaming (_≟_ to _≟B_)
open import Data.Bool.Properties
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size
open import Data.Nat.Binary renaming (suc to bsuc; _*_ to _b*_)
open import Data.Nat.Binary.Properties
open import Relation.Nullary 
open import Tests
open import Trees-Coinductive
open import Trees-Comp
open import Examples.Bitlist-help



-- ==============================================
--   BINARY INPUT
-- ==============================================



i-obs = Bit × BitList
clo : BitList → i-obs
clo s = left , s
ope : BitList → i-obs
ope s = right , s

i-leaf : i-obs → Bool
i-leaf (left , EmptyBL) = true
i-leaf (o , s) = false

i-node : True → i-obs → Test (Bit × i-obs)
i-node * (b , AppendBL x s) = atom (x , (b , s))
i-node * (left , EmptyBL) = false
i-node * (right , EmptyBL) = true

bI = (λ (_ : True) → Bit)

import Pred-Lift-ab
open Pred-Lift-ab bI i-obs i-leaf i-node

-- Example:

BL-0 = AppendBL left EmptyBL
BL-110 = AppendBL right (AppendBL right (AppendBL left EmptyBL))
-- List of n rights
BL-nx1 : ℕ → BitList
BL-nx1 zero = EmptyBL
BL-nx1 (suc n) = AppendBL right (BL-nx1 n)

-- even number at left (zero)
input-closed-0-even : liftTree pred-even (clo BL-0) (num-gen zero)
input-closed-0-even = node-α (leaf-α refl pe-zero)

-- even number at right-right-left
input-closed-110-even : liftTree pred-even (clo BL-110) (num-gen zero)
input-closed-110-even = node-α (node-α (node-α (leaf-α refl (pe-ss zero pe-zero))))

-- we can keep inputting right-right-right, is infinitely many times
input-open-left : (n : ℕ) → (m : ℕ) → liftTree (λ x → False) (ope (BL-nx1 n)) (num-gen m)
input-open-left zero m = node-α tt
input-open-left (suc n) m = node-α (input-open-left n (suc m))


-- Decomposable

-- closed list composition
i-strong-clo : (s : BitList) → (bs' : i-obs) → (r : DTree bI) → obsTower r (clo s) bs' → α (bs' .proj₁ , ConcatBL s (bs' .proj₂)) (μTree r)
i-strong-clo EmptyBL (b , s') (leaf x) (leaf-α x₁ x₂) = x₂
i-strong-clo (AppendBL x₁ s) (b , s') (leaf x) (leaf-α () y₂)
i-strong-clo EmptyBL (b , s') (node _ ts) (node-α ())
i-strong-clo (AppendBL x s) (left , s') (node _ ts) (node-α x₁) = node-α (i-strong-clo s ((left , s')) (force (ts x)) x₁)
i-strong-clo (AppendBL x s) (right , s') (node _ ts) (node-α x₁) = node-α (i-strong-clo s ((right , s')) (force (ts x)) x₁)

-- open list composition
i-strong-ope : (s : BitList) → (o : i-obs) → (r : DTree bI) → obsTower r (ope s) o → α (ope s) (μTree r)
i-strong-ope s o (leaf x) (leaf-α () x₂)
i-strong-ope EmptyBL o (node _ ts) pruf = node-α tt
i-strong-ope (AppendBL x s) o (node _ ts) (node-α x₁) =  node-α (i-strong-ope s o (force (ts x)) x₁)

-- closed list decomposition
i-strong-clo-inv : (s : BitList) → (r : DTree bI) → α (clo s) (μTree r) → Σ BitList λ m → Σ BitList λ n → ((ConcatBL m n) ≡ s) × obsTower r (clo m) (clo n)
i-strong-clo-inv s (leaf x) pruf = EmptyBL , (s , (refl , leaf-α refl pruf))
i-strong-clo-inv EmptyBL (node _ ts) (node-α ())
i-strong-clo-inv (AppendBL x s) (node _ ts) (node-α x₁) with i-strong-clo-inv s (force (ts x)) x₁
... | m , n , e , hypo = (AppendBL x m) , (n , (cong (λ x₂ →  AppendBL x x₂) e , node-α hypo))

-- open list decomposition
i-obs-ph = ope EmptyBL    -- placeholder observation, can be any!
i-strong-ope-inv : (s v : BitList) → (r : DTree bI) → α (ope s) (μTree r) →
  ((obsTower r (ope s) (ope v))
  ⊎ (Σ BitList λ m → Σ BitList λ n → ((ConcatBL m n) ≡ s) × obsTower r (clo m) (ope n)))
i-strong-ope-inv s v (leaf x) pruf = inj₂ (EmptyBL , s , (refl , (leaf-α refl pruf)))
i-strong-ope-inv EmptyBL v (node _ ts) (node-α tt) = inj₁ (node-α tt)
i-strong-ope-inv (AppendBL x s) v (node _ ts) (node-α x₁) with i-strong-ope-inv s v (force (ts x)) x₁
... | inj₁ x₂ = inj₁ (node-α x₂)
... | inj₂ (m , n , e , hypo) = inj₂ ((AppendBL x m) , (n , ((cong (λ y → AppendBL x y) e) , (node-α hypo))))


-- deco

i-deco : deco
i-deco (left , σ) = ⋁ (λ n → ⋁ (λ m → if EqBL (ConcatBL (toList n) (toList m)) σ
  then atom ((left , (toList n)) , (left , (toList m))) else false))
i-deco (right , σ) = (atom ((right , σ) , (right , σ))) ∨
  ⋁ (λ n →  ⋁ (λ m → if EqBL (ConcatBL (toList n) (toList m)) σ
  then atom ((left , (toList n)) , (right , (toList m))) else false))

i-help1 : (b : ℕᵇ) → (i-leaf (left , BinaryList (bsuc b))) ≡ false
i-help1 zero = refl
i-help1 2[1+ b ] = refl
i-help1 1+[2 b ] = refl
 
i-help : {A : Set} → (tes : Test A) → (b : Bool) → (f : A → Set) →
  liftTest f (if b then tes else false) → (b ≡ true) × (liftTest f tes)
i-help tes true f k = refl , k

i-deco-α-seq : (deco-α-seq i-deco)
i-deco-α-seq (left , bl) d (n , m , snd)
   with i-help _ (EqBL (ConcatBL (toList n) (toList m)) bl) _ snd
... | fst , snd₁ with EqBL≡ (ConcatBL (BinaryList (fromℕ n)) (BinaryList (fromℕ m))) bl fst
... | help = subst _ help (i-strong-clo (toList n) (clo (toList m)) d snd₁)
i-deco-α-seq (right , bl) d (inj₁ x) = i-strong-ope bl (ope bl) d x
i-deco-α-seq (right , bl) d (inj₂ (n , m , snd))
   with i-help _ (EqBL (ConcatBL (toList n) (toList m)) bl) _ snd
... | fst , snd₁ with EqBL≡ (ConcatBL (BinaryList (fromℕ n)) (BinaryList (fromℕ m))) bl fst
... | help = subst _ help (i-strong-clo (toList n) (ope (toList m)) d snd₁)

i-deco-α-unf : (deco-α-unf i-deco)
i-deco-α-unf (left , bl) d x with i-strong-clo-inv bl d x
... | b0 , b2 , b02l , snd = (fromList b0) , ((fromList b2) ,
  subst
    (λ z →
       liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
       (if EqBL (ConcatBL z (BinaryList (fromℕ (toℕ (ListBinary b2))))) bl
        then
        atom ((left , z) , left , BinaryList (fromℕ (toℕ (ListBinary b2))))
        else false))
    (sym (toList-fromList b0))
    (subst
       (λ z →
          liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
          (if EqBL (ConcatBL b0 z) bl then atom ((left , b0) , left , z) else
           false))
       (sym (toList-fromList b2))
    (subst
       (λ z →
          liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
          (if z then atom ((left , b0) , left , id b2) else false))
       (sym (EqBL≡i (ConcatBL b0 b2) bl b02l)) snd)))
i-deco-α-unf (right , bl) d x with i-strong-ope-inv bl bl d x
... | inj₁ x₁ = inj₁ x₁
... | inj₂ (b0 , b2 , b02l , snd) = inj₂ (fromList b0 , (fromList b2) ,
  (subst
     (λ z →
        liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
        (if EqBL (ConcatBL z (BinaryList (fromℕ (toℕ (ListBinary b2))))) bl
         then
         atom
         ((left , z) , right , BinaryList (fromℕ (toℕ (ListBinary b2))))
         else false))
     (sym (toList-fromList b0))
     (subst
        (λ z →
           liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
           (if EqBL (ConcatBL b0 z) bl then atom ((left , b0) , right , z)
            else false))
        (sym (toList-fromList b2))
      (subst
         (λ z →
            liftTest (λ x₁ → α (proj₁ x₁) (mapTree (α (proj₂ x₁)) d))
            (if z then atom ((left , b0) , right , id b2) else false))
         (sym (EqBL≡i (ConcatBL b0 b2) bl b02l)) snd))))

i-is-strong : Strong-Decomposable
i-is-strong = deco-α-decomp i-deco i-deco-α-seq i-deco-α-unf

-- β deco

i-deco' : deco
i-deco' o = dualTest (i-deco o)

i-deco-β-seq-left : ∀ s d
  → (∀ s1 s2 → ConcatBL s1 s2 ≡ s → β-obsTower d (left , s1) (left , s2))
  → β ∞ (left , s) (μTree d)
i-deco-β-seq-left' : ∀ s d
  → (∀ s1 s2 → ConcatBL s1 s2 ≡ s → β-obsTower d (left , s1) (left , s2))
  → β' ∞ (left , s) (μTree d)
i-deco-β-seq-left s (leaf t) p with p EmptyBL s refl
... | β-leaf q = q
i-deco-β-seq-left EmptyBL (node k ds) p = β-node tt
i-deco-β-seq-left (AppendBL b s) (node k ds) p =
  β-node (i-deco-β-seq-left' s (force (ds b)) lem)
  where
    lem : ∀ s1 s2 → ConcatBL s1 s2 ≡ s
      → β ∞ (left , s1) (mapTree (β ∞ (left , s2)) (force (ds b)))
    lem s1 s2 refl with p (AppendBL b s1) s2 refl
    ... | β-node q = β-force q
β-force (i-deco-β-seq-left' s d p) = i-deco-β-seq-left s d p

i-β-obsTower-right : ∀ s {s' s''} d
  → β-obsTower d (right , s) (right , s')
  → β-obsTower d (right , s) (right , s'')
i-β-obsTower-right' : ∀ s {s' s''} d
  → β-obsTower d (right , s) (right , s')
  → β-obsTower' d (right , s) (right , s'')
i-β-obsTower-right s (leaf t) p = β-exep refl
i-β-obsTower-right (AppendBL b s) (node k ds) (β-node p) =
  β-node (i-β-obsTower-right' s (force (ds b)) (β-force p))
β-force (i-β-obsTower-right' s d p) = i-β-obsTower-right s d p

i-deco-β-seq-right : ∀ s d
  → β ∞ (right , s) (mapTree (β ∞ (right , s)) d)
  → (∀ s1 s2 → ConcatBL s1 s2 ≡ s → β-obsTower d (left , s1) (right , s2))
  → β ∞ (right , s) (μTree d)
i-deco-β-seq-right' : ∀ s d
  → β ∞ (right , s) (mapTree (β ∞ (right , s)) d)
  → (∀ s1 s2 → ConcatBL s1 s2 ≡ s → β-obsTower d (left , s1) (right , s2))
  → β' ∞ (right , s) (μTree d)
i-deco-β-seq-right s (leaf t) (β-leaf p1) p2 = p1
i-deco-β-seq-right s (leaf t) (β-exep p1) p2 with p2 EmptyBL s refl
... | β-leaf q = q
i-deco-β-seq-right EmptyBL (node k ds) (β-node ()) p2
i-deco-β-seq-right (AppendBL b s) (node k ds) (β-node p1) p2 =
  β-node (i-deco-β-seq-right' s (force (ds b)) (i-β-obsTower-right s (force (ds b)) (β-force p1)) lem2)
  where
    lem2 : ∀ s1 s2 → ConcatBL s1 s2 ≡ s
      → β ∞ (left , s1) (mapTree (β ∞ (right , s2)) (force (ds b)))
    lem2 s1 s2 refl with p2 (AppendBL b s1) s2 refl
    ... | β-node q = β-force q
β-force (i-deco-β-seq-right' s d p1 p2) = i-deco-β-seq-right s d p1 p2

i-deco-β-seq : deco-β-seq i-deco'
i-deco-β-seq (left , s) d x = i-deco-β-seq-left s d lem
  where
    lem : ∀ s1 s2 → ConcatBL s1 s2 ≡ s
      → β ∞ (left , s1) (mapTree (β ∞ (left , s2)) d)
    lem s1 s2 refl with x (fromList s1) (fromList s2)
    ... | p rewrite toList-fromList s1 | toList-fromList s2
        | EqBL≡i (ConcatBL s1 s2) (ConcatBL s1 s2) refl = p
i-deco-β-seq (right , s) d (x1 , x2) = i-deco-β-seq-right s d x1 lem2
  where
    lem2 : ∀ s1 s2 → ConcatBL s1 s2 ≡ s
      → β ∞ (left , s1) (mapTree (β ∞ (right , s2)) d)
    lem2 s1 s2 refl with x2 (fromList s1) (fromList s2)
    ... | p rewrite toList-fromList s1 | toList-fromList s2
        | EqBL≡i (ConcatBL s1 s2) (ConcatBL s1 s2) refl = p

i-deco-β-unf-left : ∀ {b} s1 s2 d
  → β ∞ (b , ConcatBL s1 s2) (μTree d)
  → β-obsTower d (left , s1) (b , s2)
i-deco-β-unf-left' : ∀ {b} s1 s2 d
  → β ∞ (b , ConcatBL s1 s2) (μTree d)
  → β-obsTower' d (left , s1) (b , s2)
i-deco-β-unf-left EmptyBL s2 (leaf x) p = β-leaf p
i-deco-β-unf-left EmptyBL s2 (node k ts) p = β-node tt
i-deco-β-unf-left (AppendBL b s1) s2 (leaf t) p = β-exep refl
i-deco-β-unf-left (AppendBL b s1) s2 (node k ts) (β-node p) = 
  β-node (i-deco-β-unf-left' s1 s2 (force (ts b)) (β-force p))
β-force (i-deco-β-unf-left' s1 s2 d p) = i-deco-β-unf-left s1 s2 d p

i-deco-β-unf-left-gen : ∀ {b} s d
  → β ∞ (b , s) (μTree d)
  → ∀ s1 s2 → ConcatBL s1 s2 ≡ s → β-obsTower d (left , s1) (b , s2)
i-deco-β-unf-left-gen ._ d p s1 s2 refl = i-deco-β-unf-left s1 s2 d p

i-deco-β-unf-right : ∀ s {s'} d
  → β ∞ (right , s) (μTree d)
  → β-obsTower d (right , s) (right , s')
i-deco-β-unf-right' : ∀ s {s'} d
  → β ∞ (right , s) (μTree d)
  → β-obsTower' d (right , s) (right , s')

i-deco-β-unf-right s (leaf x) p = β-exep refl
i-deco-β-unf-right EmptyBL (node k ts) (β-node x) = β-node x
i-deco-β-unf-right (AppendBL b s) (node k ts) (β-node x) =
  β-node (i-deco-β-unf-right' s (force (ts b)) (β-force x))

β-force (i-deco-β-unf-right' s d p) = i-deco-β-unf-right s d p

i-deco-β-unf : deco-β-unf i-deco'
i-deco-β-unf (left , s) d p n m with EqBL (ConcatBL (toList n) (toList m)) s ≟B true
... | no ¬eq rewrite ¬-not ¬eq = tt
... | yes eq rewrite eq = i-deco-β-unf-left-gen s d p _ _ (EqBL≡ _ _ eq)
proj₁ (i-deco-β-unf (right , s) d p) = i-deco-β-unf-right s d p
proj₂ (i-deco-β-unf (right , s) d p) n m with EqBL (ConcatBL (toList n) (toList m)) s ≟B true
... | no ¬eq rewrite ¬-not ¬eq = tt
... | yes eq rewrite eq = i-deco-β-unf-left-gen s d p _ _ (EqBL≡ _ _ eq)

n-β-decomp : β-Strong-Decomposable
n-β-decomp = deco-β-decomp i-deco' i-deco-β-seq i-deco-β-unf


-- -- PROPOSITION: input toggle is Strong-Decomposable
-- i-is-strong : Strong-Decomposable
-- i-is-strong r r' pruf (left , s) assum with i-strong-clo-inv s r assum
-- ... | m , n , e , hypo with i-strong-clo m (clo n) r' (pruf (clo m) (clo n) hypo)
-- ... | z = subst (λ y → (α (left , y) (μTree r'))) e z
-- i-is-strong r r' pruf (right , s) assum with i-strong-ope-inv s r assum
-- ... | inj₁ x = i-strong-ope s i-obs-ph r' (pruf (ope s) i-obs-ph x)
-- ... | inj₂ (m , n , e , hypo) with i-strong-clo m (ope n) r' (pruf (clo m) (ope n) hypo)
-- ... | z = subst (λ y → (α (right , y) (μTree r'))) e z


