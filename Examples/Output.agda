module Examples.Output where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
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
--   OUTPUT
-- ==============================================

cI : Bit → Set
cI n = ⊤

c-obs : Set
c-obs = Bit × BitList

c-leaf : c-obs → Bool
c-leaf (left , EmptyBL) = true
c-leaf (left , AppendBL x snd) = false
c-leaf (right , snd) = false

c-node : Bit → c-obs → Test (⊤ × c-obs)
c-node b (left , EmptyBL) = false
c-node b (right , EmptyBL) = true
c-node left (fst , AppendBL left snd) = atom (tt , ((fst , snd)))
c-node left (fst , AppendBL right snd) = false
c-node right (fst , AppendBL left snd) = false
c-node right (fst , AppendBL right snd) = atom (tt , (fst ,  snd))

import Pred-Lift-ab
open Pred-Lift-ab cI c-obs c-leaf c-node


i-help : {A : Set} → (tes : Test A) → (b : Bool) → (f : A → Set) →
  liftTest f (if b then tes else false) → (b ≡ true) × (liftTest f tes)
i-help tes true f k = refl , k


⋁BL : {A : Set} → (f : BitList → Test A) → Test A
⋁BL f = ⋁ (λ n → f (toList n))


-- deco formulation
-- proof of decomposability not included. Should be similar to input example
o-deco : deco
o-deco (left , σ) = ⋁BL (λ bl₁ → ⋁BL (λ bl₂ → if EqBL (ConcatBL bl₁ bl₂) σ
  then atom ((left , bl₁) , (left , bl₂)) else false))
o-deco (right , σ) = (atom ((right , σ) , (right , σ))) ∨
  ⋁BL (λ bl₁ →  ⋁BL (λ bl₂ → if EqBL (ConcatBL bl₁ bl₂) σ
  then atom ((left , bl₁) , (right , bl₂)) else false))

