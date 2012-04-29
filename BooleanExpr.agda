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

data Op : Set where
 And : Op
 Or : Op

bin : Op → Carrier → Carrier → Carrier
bin And = _∧_
bin Or = _∨_

data Expr (B : Set) : Set where
  :bin : (op : Op) → (a b : Expr B) → Expr B
  :¬_ : (a : Expr B) → Expr B
  :const : Bool → Expr B
  var : (x : B) → Expr B

_:∧_ : ∀ {A : Set} → Expr A → Expr A → Expr A
_:∧_ = :bin And
_:∨_ : ∀ {A : Set} → Expr A → Expr A → Expr A
_:∨_ = :bin Or

:⊤ : ∀ {A : Set} → Expr A
:⊤ = :const true
:⊥ : ∀ {A : Set} → Expr A
:⊥ = :const false

const : Bool → Carrier
const true = ⊤
const false = ⊥

⟦_⟧₀ : ∀ {A} → Expr A → (A → Carrier) → Carrier
⟦_⟧₀ (:bin op a b) vars = bin op (⟦ a ⟧₀ vars) (⟦ b ⟧₀ vars)
⟦_⟧₀ (:¬ a) vars = ¬ ⟦ a ⟧₀ vars
⟦ :const c ⟧₀ _ = const c
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
