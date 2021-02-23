module Signatures where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Function
open import Trees-Coinductive

data True : Set where
  true : True

data False : Set where

data BSig : Set where
  b-or : BSig
Bit = Bool
BAr : BSig → Set
BAr b-or = Bool

-- extending signatures with skip operation
module add-skip (Sig : Set) (ar : Sig → Set) where
  Sig⊥ : Set
  Sig⊥ = Sig ⊎ ⊤

  ar⊥ : Sig⊥ → Set
  ar⊥ (inj₁ σ) = ar σ
  ar⊥ (inj₂ tt) = ⊤

  ` : Sig → Sig⊥
  ` = inj₁

  skip : Sig⊥
  skip = inj₂ tt
