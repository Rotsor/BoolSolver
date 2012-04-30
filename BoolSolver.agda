open import Algebra

open import Level using () renaming (zero to ₀)

module BoolSolver (Alg : BooleanAlgebra ₀ ₀) where

open BooleanAlgebra Alg
import Relation.Binary.Reflection as Reflection

import ConstantPropagation
open ConstantPropagation Alg

import Data.Product as Product
open Product
open import Function  hiding (const)

import Algebra.Props.BooleanAlgebra as BoolProps
open BoolProps Alg
open CommutativeSemiring ∨-∧-commutativeSemiring using () 
  renaming 
  ( zero to ∧-zero
  ; *-identity to ∧-identity
  ; +-identity to ∨-identity
  )

open CommutativeSemiring ∧-∨-commutativeSemiring using () 
  renaming 
  ( zero to ∨-zero
  )

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Bool using (Bool; true; false)

import ShannonExpander
open ShannonExpander Alg

import BooleanExpr
open BooleanExpr Alg

data NF : ℕ → Set where
  :constant : Bool → NF 0
  _/\_ : ∀ {n} → NF n → NF n → NF (suc n)

open import Data.Vec

⇓⟦_⟧ : ∀ {n} → NF n → Vec Carrier n → Carrier
⇓⟦_⟧ (:constant c) ρ = const c
⇓⟦_⟧ (l /\ r) ρ  = if (head ρ) (⇓⟦ l ⟧ (tail ρ)) (⇓⟦ r ⟧ (tail ρ))

if-cong : ∀ {a₁ b₁ c₁ a₂ b₂ c₂} → c₁ ≈ c₂ → a₁ ≈ a₂ → b₁ ≈ b₂ → if c₁ a₁ b₁ ≈ if c₂ a₂ b₂
if-cong c-eq a-eq b-eq = ∨-cong (∧-cong c-eq a-eq) (∧-cong (¬-cong c-eq) b-eq)

open import Data.Vec
import Relation.Binary.EqReasoning as EqReasoning
import Data.Empty

wtf-no-constants : (e : Expr (Fin 0)) → (No-Constants e → Data.Empty.⊥)
wtf-no-constants (:op (:constant c) inp) bt = bt
wtf-no-constants (:op (:unary neg) inp) bt = wtf-no-constants (inp (# 0)) (bt (# 0))
wtf-no-constants (:op (:binary op) inp) bt = wtf-no-constants (inp (# 0)) (bt (# 0))
wtf-no-constants (var ()) bt

eval : (e : Expr (Fin 0)) → ∃ (λ c → (∀ {ρ} → ⟦ e ⟧ ρ ≈ const c))
eval e with constantPropagation e
... | :constant c , prf = c , prf
... | :no-constants x noo , _ = Data.Empty.⊥-elim (wtf-no-constants x noo)

normalise : ∀ {n} → (f : Expr (Fin n)) → ∃ (λ nf → ∀ {ρ} → ⟦ f ⟧ ρ ≈ ⇓⟦ nf ⟧ ρ)
normalise {zero} f with eval f
... | f-val , proof = (:constant f-val) , proof
normalise {suc n} f with shannon-expand f
... | f₁ , f₀ , snannon-proof with normalise f₁ | normalise f₀
... | nf₁ , nf₁-proof | nf₀ , nf₀-proof  = nf₁ /\ nf₀ , trans snannon-proof (prf _) where
  prf : ∀ ρ → ⟦ :if (var zero) (f₁ ↑) (f₀ ↑) ⟧ ρ ≈ ⇓⟦ nf₁ /\ nf₀ ⟧ ρ
  prf (x ∷ ρ) = if-cong refl (trans (raise-sem f₁ ρ) nf₁-proof) (trans (raise-sem f₀ ρ) nf₀-proof)

⟦_⇓⟧ : {n : ℕ} → Expr (Fin n) → Vec Carrier n → Carrier
⟦_⇓⟧ expr = ⇓⟦ proj₁ (normalise expr) ⟧

correct : ∀ {n} (e : Expr (Fin n)) (ρ : Vec Carrier n) → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct e ρ = sym (proj₂ (normalise e) {ρ})

open Reflection setoid var ⟦_⟧ ⟦_⇓⟧ correct

theoremm : ∀ x y z → x ∧ (y ∨ z) ≈ y ∧ x ∨ z ∧ z ∧ x ∧ x ∧ ⊤
theoremm = solve 3 (λ x y z → x :∧ (y :∨ z) ⊜ y :∧ x :∨ z :∧ z :∧ x :∧ x :∧ :⊤) refl

theoremm2 : ∀ x y → ¬ (¬ x ∧ y) ≈ x ∨ ¬ y
theoremm2 = solve 2 (λ x y → :¬ (:¬ x :∧ y) ⊜ x :∨ :¬ y) refl

theoremm4 : ∀ x y z  → x ∧ (y ∨ z) ≈ y ∧ x ∨ z ∧ z ∧ x ∧ x ∧ ⊤
theoremm4 = solve 3 (λ x y z → x :∧ (y :∨ z) ⊜ y :∧ x :∨ z :∧ z :∧ x :∧ x :∧ :⊤) refl

theorem5 : ∀ x y → _ ≈ _
theorem5 = solve 2 (λ x y → y :∧ x ⊜ x :∧ y) refl

theorem6 = solve 0 (:⊤ ⊜ :⊤) refl
