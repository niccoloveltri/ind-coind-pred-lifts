module Languages.Automata where

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
open import Trees-Coinductive

data Unit : Set where
  * : Unit

-- Effectful automata
Autom : (K : Set) → (I : K → Set) → (Start End : Set) → (State : Set) → Set
Autom K I Start End State = (Start → State) × (State → (Unit ⊎ End))
  × (State → (Σ K λ op → (I op) → State))

Autom-Tree : {K : Set} {I : K → Set} {Start End : Set} {State : Set}
  → (Autom K I Start End State) → Start → Tree I End
Autom-Tree' : {K : Set} {I : K → Set} {Start End : Set} {State : Set}
  → (Autom K I Start End State) → Start → STree' I End ∞
Autom-Tree (Init , Final , Trans) s with (Final (Init s)) , (Trans (Init s))
... | inj₁ _ , op , cont = node op (λ i → Autom-Tree' ((λ u → cont i) , Final , Trans) tt)
... | inj₂ e , b = leaf e
force (Autom-Tree' A s) = Autom-Tree A s

-- Composing automata
Comp-Autom : {K : Set} → {I : K → Set} → {A B C StateX StateY : Set}
  → (Autom K I A B StateX) → (Autom K I B C StateY)
  → Autom K I A C (StateX ⊎ StateY)
Comp-Autom AX AY = (λ x → inj₁ (proj₁ AX x)) ,
  ((λ { (inj₁ x) → [ (λ i → inj₁ i) ,
                     (λ s → proj₁ (proj₂ AY) (proj₁ AY s)) ] (proj₁ (proj₂ AX) x) ;
        (inj₂ y) →  proj₁ (proj₂ AY) y}) ,
    λ {(inj₁ x) → (proj₁ (proj₂ (proj₂ AX) x)) , (λ x₁ → inj₁ (proj₂ (proj₂ (proj₂ AX) x) x₁))
     ;(inj₂ y) → (proj₁ (proj₂ (proj₂ AY) y)) , (λ x₁ → inj₂ (proj₂ (proj₂ (proj₂ AY) y) x₁))})

-- Layered automata
Comp-Autom-Tower : {K : Set} → {I : K → Set} → {A B C StateX StateY : Set}
  → (Autom K I A B StateX) → (Autom K I B C StateY)
  → A → Tree I (Tree I C)
Comp-Autom-Tower AX AY a = mapTree (Autom-Tree AY) (Autom-Tree AX a)









