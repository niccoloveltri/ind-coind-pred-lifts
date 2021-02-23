open import Tests
open import Data.Product renaming (map to map×)
open import Data.Bool

module Program-Types {Sig : Set} (ar : Sig → Set) where

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


-- basic agda types, for describing program denotations
data Aty : Set where
  N : Aty
  _⇒_ : Aty → Aty → Aty
  _⊗_ : Aty → Aty → Aty
  U : Aty → Aty

pattern val = true
pattern cpt = false

-- Value and computations terms for Agda types
A-val : Aty → Set
A-cpt : Aty → Set
A-cpt' : Aty → Set
A-val N = ℕ
A-val (τ ⇒ ρ) = A-val τ → A-cpt ρ
A-val (τ ⊗ ρ) = A-val τ × A-val ρ
A-val (U τ) = A-cpt τ
A-cpt τ = Tree ar (A-val τ)
A-cpt' τ = STree' ar (A-val τ) ∞

A-term : Bool → Aty → Set
A-term cpt τ = A-cpt τ
A-term val τ = A-val τ
