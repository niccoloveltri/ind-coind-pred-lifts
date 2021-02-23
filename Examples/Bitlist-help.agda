module Examples.Bitlist-help where

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
open import Trees-Comp
  
data BitList : Set where
  EmptyBL : BitList
  AppendBL : Bit → BitList → BitList

ConcatBL : BitList → BitList → BitList
ConcatBL EmptyBL s' = s'
ConcatBL (AppendBL x s) s' = AppendBL x (ConcatBL s s')

BinaryList : ℕᵇ → BitList
BinaryList zero = EmptyBL
BinaryList 2[1+ k ] = AppendBL left (BinaryList k)
BinaryList 1+[2 k ] = AppendBL right (BinaryList k)

ListBinary : BitList → ℕᵇ
ListBinary EmptyBL = zero
ListBinary (AppendBL left k) = 2[1+ ListBinary k ]
ListBinary (AppendBL right k) = 1+[2 ListBinary k ]

LB-BL : ListBinary ∘ BinaryList ≗ id
LB-BL zero = refl
LB-BL 2[1+ b ] = cong (λ z → 2[1+ z ]) (LB-BL b)
LB-BL 1+[2 b ] = cong (λ z → 1+[2 z ]) (LB-BL b)

BL-LB : BinaryList ∘ ListBinary ≗ id
BL-LB EmptyBL = refl
BL-LB (AppendBL left k) = cong (λ z → AppendBL left z) (BL-LB k)
BL-LB (AppendBL right k) = cong (λ z → AppendBL right z) (BL-LB k)

toList : ℕ → BitList
toList = BinaryList ∘ fromℕ

fromList : BitList → ℕ
fromList = toℕ ∘ ListBinary

fromList-toList : fromList ∘ toList ≗ id
fromList-toList n = subst (λ z → toℕ z ≡ n) (sym (LB-BL (fromℕ n))) (toℕ-fromℕ n)

toList-fromList : toList ∘ fromList ≗ id
toList-fromList l = subst (λ z → BinaryList z ≡ l) (sym (fromℕ-toℕ (ListBinary l))) (BL-LB l)


EqBL : BitList → BitList → Bool
EqBL EmptyBL EmptyBL = true
EqBL EmptyBL (AppendBL x τ) = false
EqBL (AppendBL x σ) EmptyBL = false
EqBL (AppendBL left σ) (AppendBL left τ) = EqBL σ τ
EqBL (AppendBL left σ) (AppendBL right τ) = false
EqBL (AppendBL right σ) (AppendBL left τ) = false
EqBL (AppendBL right σ) (AppendBL right τ) = EqBL σ τ

EqBL≡ : (a b : BitList) → (EqBL a b ≡ true) → (a ≡ b)
EqBL≡ EmptyBL EmptyBL hypo = refl
EqBL≡ (AppendBL left a) (AppendBL left b) hypo =
  cong (λ z → AppendBL left z) (EqBL≡ a b hypo)
EqBL≡ (AppendBL right a) (AppendBL right b) hypo =
  cong (λ z → AppendBL right z) (EqBL≡ a b hypo)

EqBL≡i : (a b : BitList) → (a ≡ b) → (EqBL a b ≡ true)
EqBL≡i EmptyBL EmptyBL hypo = refl
EqBL≡i (AppendBL left a) (AppendBL left .a) refl = EqBL≡i a a refl
EqBL≡i (AppendBL right a) (AppendBL right .a) refl = EqBL≡i a a refl

EqBLnot≡ : (a b : BitList) → (EqBL a b ≡ false) → a ≡ b → ⊥
EqBLnot≡ a b eq eq' with trans (sym eq) (EqBL≡i a b eq')
... | ()

EqBLnot≡i : (a b : BitList) → (a ≡ b → ⊥) → EqBL a b ≡ false
EqBLnot≡i EmptyBL EmptyBL noteq = ⊥-elim (noteq refl)
EqBLnot≡i EmptyBL (AppendBL x b) noteq = refl
EqBLnot≡i (AppendBL x a) EmptyBL noteq = refl
EqBLnot≡i (AppendBL left a) (AppendBL left b) noteq = EqBLnot≡i a b (λ eq → noteq (cong (AppendBL left) eq))
EqBLnot≡i (AppendBL left a) (AppendBL right b) noteq = refl
EqBLnot≡i (AppendBL right a) (AppendBL left b) noteq = refl
EqBLnot≡i (AppendBL right a) (AppendBL right b) noteq = EqBLnot≡i a b (λ eq → noteq (cong (AppendBL right) eq))
