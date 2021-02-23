module Examples.Probability where

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

open import Tests
open import Trees-Coinductive
open import Trees-Comp


-- ==============================================
--   PROBABILISTIC CHOICE
-- ==============================================

-- Rational numbers interval [0,1), encoded (n,m) ↦ n/(n+m+1)
data RatInt : Set where
  RatEnc : (ℕ × ℕ) → RatInt

-- minus natural
_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m

-- make
RatMake : ℕ → ℕ → RatInt
RatMake n m = RatEnc (n , (m - suc n))

-- denominator
RatDen : RatInt → ℕ
RatDen (RatEnc (p , q)) = suc (p + q)
-- average function
RatAve : RatInt → RatInt → RatInt
RatAve (RatEnc (p , q)) (RatEnc (p' , q')) =
  RatEnc (p * (suc (p' + q')) + p' * (suc (p + q)) , 2 * q * q' + 2 * (q + q') + p * q' + p' * q + p + p' + 1)
-- order function nat
NatOrd : ℕ → ℕ → Bool
NatOrd zero m = true
NatOrd (suc n) zero = false
NatOrd (suc n) (suc m) = NatOrd n m
-- order function rat
RatOrd : RatInt → RatInt → Bool
RatOrd (RatEnc (p , q)) (RatEnc (p' , q')) =
  NatOrd (p * (suc (p' + q'))) (p' * (suc (p + q)))
-- check if below 1/2
RatLow : RatInt → Bool
RatLow (RatEnc (p , q)) = NatOrd p q
-- double rational
RatDou : RatInt → RatInt
RatDou (RatEnc (p , q)) = RatEnc ((2 * p) , (q - p))

p-obs = RatInt

p-leaf : p-obs → Bool
p-leaf = λ x → true

p-node : True → p-obs → Test (Bit × p-obs)
p-node * x = ((boolTest (RatLow x)) ∧  ((atom (left , RatDou x)) ∨ (atom (right , RatDou x )))) ∨
  ⋁ (λ a → ⋁ (λ b → ⋁ (λ a' → ⋁ (λ b' → (boolTest (RatOrd x (RatAve (RatEnc (a , b)) (RatEnc (a' , b')))))
                     ∧ ((atom (left , (RatEnc (a , b)))) ∧ atom (right , (RatEnc (a' , b'))))))))
-- Proof description:
-- left means: all probablity in one branch, pair:
--             fst: check that probability is lower than a half
--             snd: choose branch to go into (left or right) and check double that probability in the branch)
-- right means: separate probability into two probabilities which average above the original. Choose explicit numbers. Pair:
--             fst: prove that your picked numbers average above the original number
--             snd: prove the two picked probabilities for the left and right branch respectively (pair)

bI = (λ (_ : True) → Bit)

import Pred-Lift-ab
open Pred-Lift-ab bI p-obs p-leaf p-node

-- Examples

RThird = RatEnc (1 , 1)
RHalf = RatEnc (1 , 0)

-- even number more than 1/3 chance, proof: check 2/3 chance on left branch, which is zero leaf hence 1 prob of being even.
prob-third-even : liftTree pred-even (RThird) (num-gen zero)
prob-third-even = node-α (inj₁ (tt , (inj₁ (leaf-α refl pe-zero))))

-- even number more than 1/2 chance, proof: split into 4/5 (4,0) and 1/5 (1,3). Left branch can be directly proven since zero is even.
--   right branch: double 1/5 to 2/5 and go right branch again. Double again but now go left. Two is even, so finished.

prob-half-even : liftTree pred-even (RHalf) (num-gen zero)
prob-half-even = node-α (inj₂ (4 , (0 , (1 , (3 , tt ,((       -- node: split into 4/5 left, 1/5 right
                     leaf-α refl pe-zero) ,                                 -- left leaf: to prove 4/5, leaf with zero, done
                     node-α (inj₁ (tt , inj₂ (                  -- right node: to prove 1/5, prove 2/5 right
                         node-α (inj₁ (tt , inj₁ (              -- righ-right node: to prove 2/5, prove 4/5 left
                             leaf-α refl (pe-ss zero pe-zero)))))))) ))))) -- right-right-left leaf: to prove 4/5, leaf with 2, done


