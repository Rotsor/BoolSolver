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

constBin : (op : BinOp) → ∀ {n} → (a : Expr (Fin n)) → (c : Bool) → ∃ (_≛_ (:bin op a (:const c)))
constBin And x true = x , proj₂ ∧-identity _
constBin And _ false = :const false , proj₂ ∧-zero _
constBin Or _ true = :const true ,  proj₂ ∨-zero _
constBin Or x false = x , proj₂ ∨-identity _

cleverBin : ∀ {n} → (op : BinOp) → (a b : Expr (Fin n)) → ∃ (_≛_ (:bin op a b))
cleverBin op a (:op (:constant b) _) = constBin op a b
cleverBin op (:op (:constant a) _) b with constBin op b a
... | res , proof = res , trans (bin-comm op (const a) (⟦ b ⟧ _)) proof
cleverBin op a b = :bin op a b , refl

bool-neg-sem : ∀ (c : Bool) → ¬ const c ≈ const (Data.Bool.not c)
bool-neg-sem true = ¬⊤=⊥
bool-neg-sem false = ¬⊥=⊤

clever¬ : ∀ {n} → (x : Expr (Fin n)) → ∃ (_≛_ (:¬ x))
clever¬ (:op (:constant c) _) = :const (Data.Bool.not c) , bool-neg-sem c
clever¬ x = :¬ x , refl

clever-op : ∀ {n} (op : Op) → (inp : Inputs op (Expr (Fin n))) → ∃ (_≛_ (:op op inp))
clever-op (:unary true) inp = inp (# 0) , refl
clever-op (:unary false) inp = clever¬ (inp (# 0))
clever-op (:binary op) inp = cleverBin op (inp (# 0)) (inp (# 1))
clever-op op inp = :op op inp , refl

constantPropagation : ∀ {n} → (a : Expr (Fin n)) → ∃ (_≛_ a)
constantPropagation (var v) = var v , refl
constantPropagation (:op op inp) with clever-op op (λ i → proj₁ (constantPropagation (inp i)))
... | res , prf = res ,  trans (apply-cong op (λ i → proj₂ (constantPropagation (inp i)))) prf

import Data.Empty
import Data.Unit

No-Constants : ∀ {n} → (a : Expr (Fin n)) → Set
No-Constants (:op (:constant _) _) = Data.Empty.⊥
No-Constants (:op op params) = ∀ (i : Fin (InputsCount op)) → No-Constants (params i)
No-Constants _ = Data.Unit.⊤

Constants-Propagated : ∀ {n} → (a : Expr (Fin n)) → Set
Constants-Propagated (:op (:constant _) _) = Data.Unit.⊤
Constants-Propagated e = No-Constants e

constBin-propagates : (op : BinOp) → ∀ {n} → (a : Expr (Fin n)) → (c : Bool) → Constants-Propagated a → Constants-Propagated (proj₁ (constBin op a c))
constBin-propagates And a true a-propa = a-propa
constBin-propagates And a false a-propa = Data.Unit.tt
constBin-propagates Or a true a-propa = Data.Unit.tt
constBin-propagates Or a false a-propa = a-propa

cleverBin-propagates : ∀ {n} → (op : BinOp) → (a b : Expr (Fin n)) → Constants-Propagated a → Constants-Propagated b → Constants-Propagated (proj₁ (cleverBin op a b))
cleverBin-propagates op a (:op (:constant c) y) prop-a prop-b = constBin-propagates op a c prop-a
cleverBin-propagates op (:op (:constant c) y) (:op (:unary neg) y') prop-a prop-b = constBin-propagates op (:op (:unary neg) y') c prop-b
cleverBin-propagates op (:op (:unary neg) y) (:op (:unary neg') y') prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (:op (:binary op') y) (:op (:unary neg) y') prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (var x) (:op (:unary neg) y) prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (:op (:constant c) y) (:op (:binary op0) y') prop-a prop-b = constBin-propagates op (:op (:binary op0) y') c prop-b
cleverBin-propagates op (:op (:unary neg) y) (:op (:binary op0) y') prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (:op (:binary op') y) (:op (:binary op0) y') prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (var x) (:op (:binary op') y) prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (:op (:constant c) y) (var x) prop-a prop-b = constBin-propagates op (var x) c Data.Unit.tt
cleverBin-propagates op (:op (:unary neg) y) (var x) prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (:op (:binary op') y) (var x) prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }
cleverBin-propagates op (var x) (var x') prop-a prop-b = λ { zero → prop-a ; (suc zero) → prop-b; (suc (suc ())) }


constants-propagated : ∀ {n} → (e : Expr (Fin n)) → Constants-Propagated (proj₁ (constantPropagation e))
constants-propagated (:op (:constant c) inp) = Data.Unit.tt
constants-propagated (:op (:unary true) inp) = constants-propagated (inp (# 0))
constants-propagated (:op (:unary false) inp) with proj₁ (constantPropagation (inp zero)) | constants-propagated (inp zero)
constants-propagated (:op (:unary false) inp) | :op (:constant c) y | propad = Data.Unit.tt
constants-propagated (:op (:unary false) inp) | :op (:unary neg) y | propad = λ _ i → propad i
constants-propagated (:op (:unary false) inp) | :op (:binary op) y | propad = λ _ i → propad i
constants-propagated (:op (:unary false) inp) | var x | propad = λ i → Data.Unit.tt
constants-propagated (:op (:binary op) inp) with proj₁ (constantPropagation (inp zero)) | constants-propagated (inp zero) | proj₁ (constantPropagation (inp (# 1))) | constants-propagated (inp (# 1))
constants-propagated (:op (:binary op') inp) | propa₁ | propad₁ | propa₂ | propad₂ = cleverBin-propagates op' propa₁ propa₂ propad₁ propad₂
constants-propagated (var x) = Data.Unit.tt

theorem : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem x y z = proj₂ (constantPropagation ((var (# 0) :∨ var (# 2) :∧ :⊥) :∨ (var (# 1) :∧ :⊤))) {x ∷ y ∷ z ∷ []}

module Solver = Reflection setoid var ⟦_⟧ (⟦_⟧ ∘ proj₁ ∘ constantPropagation) (λ e ρ → sym (proj₂ (constantPropagation e)))

open Solver

theorem2 : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem2 = solve 3 (λ x y z → (x :∨ z :∧ :⊥) :∨ (y :∧ :⊤) ⊜ x :∨ y) refl
