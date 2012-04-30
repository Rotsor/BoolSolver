open import Algebra
open import Level using () renaming (zero to ₀)

module ConstantPropagation (Alg : BooleanAlgebra ₀ ₀) where

import Relation.Binary.Reflection as Reflection
open import Data.Bool using (Bool; true; false)
open import Data.Fin
open import Data.Nat
open import Data.Vec
open BooleanAlgebra Alg

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

import BooleanExpr
open BooleanExpr Alg
import Data.Empty
import Data.Unit

No-Constants : ∀ {n} → (a : Expr (Fin n)) → Set
No-Constants (:op (:constant _) _) = Data.Empty.⊥
No-Constants (:op op params) = ∀ (i : Fin (InputsCount op)) → No-Constants (params i)
No-Constants _ = Data.Unit.⊤

data Propagated (n : ℕ) : Set where
  :constant : Bool → Propagated n
  :no-constants : (e : Expr (Fin n)) → No-Constants e → Propagated n

unProp : ∀ {n} → Propagated n → Expr (Fin n)
unProp (:constant c) = :op (:constant c) (λ ())
unProp (:no-constants e _) = e

Propagation : ∀ {n} → (a : Expr (Fin n)) → Set
Propagation expr = ∃ (λ r → expr ≛ unProp r)

constBin : (op : BinOp) → ∀ {n} → (a : Propagated n) → (c : Bool) → Propagation (:bin op (unProp a) (:const c))
constBin And x true = x , proj₂ ∧-identity _
constBin And _ false = :constant false , proj₂ ∧-zero _
constBin Or _ true = :constant true , proj₂ ∨-zero _
constBin Or x false = x , proj₂ ∨-identity _

cleverBin : ∀ {n} → (op : BinOp) → (a b : Propagated n) → Propagation (:bin op (unProp a) (unProp b))
cleverBin op a (:constant b) = constBin op a b
cleverBin op (:constant a) b with constBin op b a
... | res , proof = res , trans (bin-comm op (const a) (⟦ unProp b ⟧ _)) proof
cleverBin op (:no-constants a a-propd) (:no-constants b b-propd) = :no-constants (:bin op a b) (λ { zero → a-propd ; (suc zero) → b-propd ; (suc (suc ())) }) , refl

bool-neg-sem : ∀ (c : Bool) → ¬ const c ≈ const (Data.Bool.not c)
bool-neg-sem true = ¬⊤=⊥
bool-neg-sem false = ¬⊥=⊤

clever¬ : ∀ {n} → (x : Propagated n) → Propagation (:¬ unProp x)
clever¬ (:constant c) = :constant (Data.Bool.not c) , bool-neg-sem c
clever¬ (:no-constants x x-propd) = :no-constants (:¬ x) (λ {zero → x-propd ; (suc ())}) , refl

clever-op : ∀ {n} (op : Op) → (inp : Inputs op (Propagated n)) → Propagation (:op op (unProp ∘ inp))
clever-op (:unary true) inp = inp (# 0) , refl
clever-op (:unary false) inp = clever¬ (inp (# 0))
clever-op (:binary op) inp = cleverBin op (inp (# 0)) (inp (# 1))
clever-op (:constant c) _ = :constant c , refl

constantPropagation : ∀ {n} → (a : Expr (Fin n)) → Propagation a
constantPropagation (var v) = :no-constants (var v) Data.Unit.tt , refl
constantPropagation (:op op inp) with clever-op op (λ i → proj₁ (constantPropagation (inp i)))
... | res , prf = res , trans (apply-cong op (λ i →  proj₂ (constantPropagation (inp i)))) prf

theorem : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem x y z = proj₂ (constantPropagation ((var (# 0) :∨ var (# 2) :∧ :⊥) :∨ (var (# 1) :∧ :⊤))) {x ∷ y ∷ z ∷ []}

module Solver = Reflection setoid var ⟦_⟧ (⟦_⟧ ∘ unProp ∘ proj₁ ∘ constantPropagation) (λ e ρ → sym (proj₂ (constantPropagation e)))

open Solver

theorem2 : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem2 = solve 3 (λ x y z → (x :∨ z :∧ :⊥) :∨ (y :∧ :⊤) ⊜ x :∨ y) refl
