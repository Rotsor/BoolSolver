open import Algebra
open import Level using () renaming (zero to ₀)

module BooleanExpr (Alg : BooleanAlgebra ₀ ₀) where

open BooleanAlgebra Alg
open import Data.Bool using (Bool; true; false)
open import Data.Fin
open import Data.Vec

infixr 6 _:∨_
infixr 7 _:∧_
infix 8 :¬_

data BinOp : Set where
 And : BinOp
 Or : BinOp

bin : BinOp → Carrier → Carrier → Carrier
bin And = _∧_
bin Or = _∨_

data Op : Set where
  :constant : (c : Bool) → Op
  :unary : (neg : Bool) → Op
  :binary : (op : BinOp) → Op

open import Data.Nat

InputsCount : Op → ℕ
InputsCount (:constant _) = 0
InputsCount (:unary _) = 1
InputsCount (:binary _) = 2

Inputs : Op → Set → Set
Inputs op A = Fin (InputsCount op) → A

data Expr (B : Set) : Set where
  :op : (op : Op) → Inputs op (Expr B) → Expr B
  var : (x : B) → Expr B

:¬_ : ∀ {A} → Expr A → Expr A
:¬_ x = :op (:unary false) (λ _ → x)

:bin : ∀ {A} → BinOp → Expr A → Expr A → Expr A
:bin op a b = :op (:binary op) (λ {zero → a; (suc zero) → b; (suc (suc ()))})

_:∧_ : ∀ {A : Set} → Expr A → Expr A → Expr A
_:∧_ = :bin And
_:∨_ : ∀ {A : Set} → Expr A → Expr A → Expr A
_:∨_ = :bin Or

:const : ∀ {A : Set} → Bool → Expr A
:const c = :op (:constant c) (λ ())

:⊤ : ∀ {A : Set} → Expr A
:⊤ = :const true
:⊥ : ∀ {A : Set} → Expr A
:⊥ = :const false

const : Bool → Carrier
const true = ⊤
const false = ⊥

lit : Bool → Carrier → Carrier
lit true x = x
lit false x = ¬ x

apply : (op : Op) → (inputs : Inputs op Carrier) → Carrier
apply (:constant y) _ = const y
apply (:unary y) inps = lit y (inps zero)
apply (:binary op) inps = bin op (inps zero) (inps (suc zero))

⟦_⟧₀ : ∀ {A} → Expr A → (A → Carrier) → Carrier
⟦_⟧₀ (:op op rec) vars = apply op (λ i → ⟦ rec i ⟧₀ vars)
⟦_⟧₀ (var y) vars = vars y

⟦_⟧ : ∀ {n} → Expr (Fin n) → Vec Carrier n → Carrier
⟦ expr ⟧ vars = ⟦ expr ⟧₀ (λ x → lookup x vars)

infix 3 _≛_

_≛_ : ∀ {n} → Expr (Fin n) → Expr (Fin n) → Set
p₁ ≛ p₂ = ∀ {ρ} → ⟦ p₁ ⟧ ρ ≈ ⟦ p₂ ⟧ ρ

import Algebra.Props.BooleanAlgebra as BoolProps
open BoolProps Alg

bin-comm : ∀ op a b → bin op a b ≈ bin op b a
bin-comm And a b = ∧-comm _ _
bin-comm Or a b = ∨-comm _ _

bin-assoc : ∀ op a b c → bin op (bin op a b) c ≈ bin op a (bin op b c)
bin-assoc And a b c = ∧-assoc _ _ _
bin-assoc Or a b c = ∨-assoc _ _ _

bin-idempotent : ∀ op a → bin op a a ≈ a
bin-idempotent And = ∧-idempotent
bin-idempotent Or = ∨-idempotent

bin-cong : ∀ op {a b c d} → a ≈ b → c ≈ d → bin op a c ≈ bin op b d
bin-cong And ab cd = ∧-cong ab cd
bin-cong Or ab cd = ∨-cong ab cd

lit-cong : ∀ (c : Bool) → {a b : Carrier} → a ≈ b → lit c a ≈ lit c b
lit-cong true eq = eq
lit-cong false eq = ¬-cong eq

apply-cong : ∀ (oper : Op)
  → {inp₁ : Inputs oper Carrier}
  → {inp₂ : Inputs oper Carrier}
  → (∀ i → inp₁ i ≈ inp₂ i)
  → apply oper inp₁ ≈ apply oper inp₂
apply-cong (:constant y) eq = refl
apply-cong (:unary c) eq = lit-cong c (eq zero) 
apply-cong (:binary op) eq = bin-cong op (eq (# 0)) (eq (# 1))
