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


Comp-Autom : {K : Set} → {I : K → Set} → {A B C StateX StateY : Set}
  → (Autom K I A B StateX) → (Autom K I B C StateY)
  → Autom K I A C (StateX ⊎ StateY)
Comp-Autom AX AY = (λ x → inj₁ (proj₁ AX x)) ,
  ((λ { (inj₁ x) → [ (λ i → inj₁ i) ,
                     (λ s → proj₁ (proj₂ AY) (proj₁ AY s)) ] (proj₁ (proj₂ AX) x) ;
        (inj₂ y) →  proj₁ (proj₂ AY) y}) ,
    λ {(inj₁ x) → (proj₁ (proj₂ (proj₂ AX) x)) , (λ x₁ → inj₁ (proj₂ (proj₂ (proj₂ AX) x) x₁))
     ;(inj₂ y) → (proj₁ (proj₂ (proj₂ AY) y)) , (λ x₁ → inj₂ (proj₂ (proj₂ (proj₂ AY) y) x₁))})

Comp-Autom-Tower : {K : Set} → {I : K → Set} → {A B C StateX StateY : Set}
  → (Autom K I A B StateX) → (Autom K I B C StateY)
  → A → Tree I (Tree I C)
Comp-Autom-Tower AX AY a = mapTree (Autom-Tree AY) (Autom-Tree AX a)

-- Comp-Autom-seqbis : ∀ {K : Set} {I : K → Set} {A B C StateX StateY : Set} {i : Size}
--   (X : Autom K I A B StateX) (Y : Autom K I B C StateY) (s : A)
--   → Bisim i (Autom-Tree (Comp-Autom X Y) s) (μTree (Comp-Autom-Tower X Y s))
-- Comp-Autom-seqbis X Y s with (proj₁ (proj₂ X) (proj₁ X s), proj₂ (proj₂ X) (proj₁ X s))
-- ... | inj₁ * , op , con = {!node-eq!}
-- ... | inj₂ y , h = {!!}
  

-- Comp-Autom : (K : Set) → (KA : K → Set) → (StateA StateB : Set) → (A : Autom K KA StateA) → (B : Autom K KA StateB) → Autom K KA (StateA ⊎ StateB)
-- Comp-Autom K KA StateA StateB (InitA , FinalA , TransA) (InitB , FinalB , TransB) =
--   (λ x → inj₂ (InitB *)) , (λ {(inj₁ s) → false ; (inj₂ s) → FinalB s  }) ,
--   λ {(inj₁ s) → if (FinalA s) then (proj₁ (TransB (InitB *))) , (λ x → inj₂ (proj₂ (TransB (InitB *)) x)) else
--   (proj₁ (TransA s)) , (λ x → inj₁ (proj₂ (TransA s) x)) ; (inj₂ s) → (proj₁ (TransB s)) , (λ x → inj₂ (proj₂ (TransB s) x))}

-- open import Trees-Comp

-- s-autom : Autom True (λ x → Bit) Bool
-- s-autom = (λ x → false) , ((λ x → x) , λ s → true , (λ {left → false ; right → true}))






-- -- -- open import Tests









