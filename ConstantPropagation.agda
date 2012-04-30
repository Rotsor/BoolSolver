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

const-neg-const : ∀ (c : Bool) → ¬ const c ≈ const (Data.Bool.not c)
const-neg-const true = ¬⊤=⊥
const-neg-const false = ¬⊥=⊤

clever¬ : ∀ {n} → (x : Expr (Fin n)) → ∃ (_≛_ (:¬ x))
clever¬ (:op (:constant c) _) = :const (Data.Bool.not c) , const-neg-const c
clever¬ x = :¬ x , refl

constantPropagation : ∀ {n} → (a : Expr (Fin n)) → ∃ (_≛_ a)
constantPropagation (:op (:binary op) ab) with constantPropagation (ab (# 0)) | constantPropagation (ab (# 1))
... | ar , a-proof | br , b-proof = Product.map id (λ pr {ρ} → trans (bin-cong op a-proof b-proof) (pr {ρ})) (cleverBin op ar br)
constantPropagation (:op (:unary false) a) with constantPropagation (a (# 0))
... | ar , a-proof = Product.map id (λ prf {ρ} → trans (¬-cong (a-proof {ρ})) (prf {ρ})) (clever¬ ar)
constantPropagation x = x , refl

theorem : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem x y z = proj₂ (constantPropagation ((var (# 0) :∨ var (# 2) :∧ :⊥) :∨ (var (# 1) :∧ :⊤))) {x ∷ y ∷ z ∷ []}

module Solver = Reflection setoid var ⟦_⟧ (⟦_⟧ ∘ proj₁ ∘ constantPropagation) (λ e ρ → sym (proj₂ (constantPropagation e)))

open Solver

theorem2 : ∀ x y z → (x ∨ z ∧ ⊥) ∨ (y ∧ ⊤) ≈ x ∨ y
theorem2 = solve 3 (λ x y z → (x :∨ z :∧ :⊥) :∨ (y :∧ :⊤) ⊜ x :∨ y) refl
