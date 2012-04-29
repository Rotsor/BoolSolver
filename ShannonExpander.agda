open import Algebra

open import Level using () renaming (zero to ₀)

module ShannonExpander (Alg : BooleanAlgebra ₀ ₀) where

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

import BooleanExpr
open BooleanExpr Alg

mapBF : ∀ {A B : Set} → (A → B) → Expr A → Expr B
mapBF f (:bin op a b) = :bin op (mapBF f a) (mapBF f b)
mapBF f (:¬ a) = :¬ mapBF f a
mapBF f (:const c) = :const c
mapBF f (var v) = var (f v)

open import Data.Fin
open import Data.Nat

_↑ : ∀ {n} → Expr (Fin n) → Expr (Fin (suc n)) 
_↑ = mapBF suc

open import Data.Bool using (Bool; true; false)

lit : Bool → Carrier → Carrier
lit true x = x
lit false x = ¬ x

:lit : Bool → ∀ {A} → Expr A → Expr A
:lit true x = x
:lit false x = :¬ x

:lit-sem : ∀ {n} → (c : Bool) → (e : Expr (Fin n)) → ∀ {ρ} → ⟦ :lit c e ⟧ ρ ≈ lit c (⟦ e ⟧ ρ)
:lit-sem true e = refl
:lit-sem false e = refl

data BoolOperation : Set where
  :const : Bool → BoolOperation
  :unary : Bool → BoolOperation
  :binary : Op → BoolOperation

data BoolF (A : Set) : Set where
  :const : Bool → BoolF A
  :bin : Op → A → A → BoolF A
  ::lit : Bool → A → BoolF A

InputsCount : BoolOperation → ℕ
InputsCount (:const _) = 0
InputsCount (:unary _) = 1
InputsCount (:binary _) = 2

import Data.Vec as Vec
open Vec

Inputs : BoolOperation → Set → Set
Inputs op A = Fin (InputsCount op) → A

apply : (oper : BoolOperation) → (inputs : Inputs oper Carrier) → Carrier
apply (:const y) _ = const y
apply (:unary y) inps = lit y (inps zero)
apply (:binary op) inps = bin op (inps zero) (inps (suc zero))

:apply : ∀ {A} → (oper : BoolOperation) → (inputs : Inputs oper (Expr A)) → (Expr A)
:apply (:const y) _ = :const y
:apply (:unary y) inps = :lit y (inps zero)
:apply (:binary op) inps = :bin op (inps zero) (inps (suc zero))

:apply-sem : ∀ {n} oper (inputs : Inputs oper (Expr (Fin n))) → ∀ {ρ} → ⟦ :apply oper inputs ⟧ ρ ≈ apply oper (λ x → ⟦ inputs x ⟧ ρ)
:apply-sem (:const y) inputs = refl
:apply-sem (:unary y) inputs = :lit-sem y (inputs zero)
:apply-sem (:binary y) inputs = refl

import Relation.Binary.EqReasoning as EqReasoning

bin-comassoc-2x2 : ∀ (op : Op) → let _⊕_ = bin op in ∀ {a b c d} → (a ⊕ b) ⊕ (c ⊕ d) ≈ (a ⊕ c) ⊕ (b ⊕ d)
bin-comassoc-2x2 op {c} {a} {d} {b} = let infixr 8 _⊕_; _⊕_ = bin op in let open EqReasoning setoid in
 begin
  (c ⊕ a) ⊕ (d ⊕ b)
    ≈⟨ bin-assoc op _ _ _ ⟩
  c ⊕ (a ⊕ d ⊕ b)
    ≈⟨ bin-cong op refl (sym (bin-assoc op _ _ _)) ⟩
  c ⊕ ((a ⊕ d) ⊕ b)
    ≈⟨ bin-cong op refl (bin-cong op (bin-comm op _ _) refl) ⟩
  c ⊕ ((d ⊕ a) ⊕ b)
    ≈⟨ bin-cong op refl (bin-assoc op d a b) ⟩
  c ⊕ (d ⊕ (a ⊕ b))
    ≈⟨ sym (bin-assoc op _ _ _) ⟩
  (c ⊕ d) ⊕ (a ⊕ b)
 ∎


bin-self-distribˡ : ∀ (op : Op) → let _⊕_ = bin op in ∀ c a b → (c ⊕ a) ⊕ (c ⊕ b) ≈ c ⊕ (a ⊕ b)
bin-self-distribˡ op c a b = let infixr 8 _⊕_; _⊕_ = bin op; open EqReasoning setoid in 
 begin
  (c ⊕ a) ⊕ (c ⊕ b)
    ≈⟨ bin-comassoc-2x2 op ⟩
  (c ⊕ c) ⊕ (a ⊕ b)
    ≈⟨ bin-cong op (bin-idempotent op c) refl ⟩
  c ⊕ (a ⊕ b)
 ∎

bin-distribˡ : ∀ op₁ op₂ a b c → bin op₁ a (bin op₂ b c) ≈ bin op₂ (bin op₁ a b) (bin op₁ a c)
bin-distribˡ And And a b c = sym (bin-self-distribˡ And _ _ _)
bin-distribˡ And Or a b c = proj₁ ∧-∨-distrib _ _ _
bin-distribˡ Or And a b c = proj₁ ∨-∧-distrib _ _ _
bin-distribˡ Or Or a b c = sym (bin-self-distribˡ Or _ _ _)

absorbb : ∀ c a → c ∧ c ∧ a ≈ c ∧ a
absorbb c a = trans (sym (∧-assoc _ _ _)) (∧-cong (∧-idempotent _) refl)

bin-tyty : ∀ op c a b →  c ∧ bin op a b ≈ c ∧ bin op (c ∧ a) (c ∧ b)
bin-tyty op c a b = trans (bin-distribˡ And op c a b) 
                     (trans (sym (bin-cong op (absorbb c a) (absorbb c b))) 
                      (sym (bin-distribˡ And op c (c ∧ a) (c ∧ b))))

tyty : ∀ c → (oper : BoolOperation) → (inp : Inputs oper Carrier) → c ∧ apply oper inp ≈ c ∧ (apply oper ((_∧_ c) ∘ inp))
tyty c (:const y) _ = refl
tyty c (:unary true) inps = sym (trans (sym (∧-assoc _ _ _)) (∧-cong (∧-idempotent c) refl))
tyty c (:unary false) inps = trans (trans (trans (sym (proj₁ ∨-identity _)) (∨-cong (sym (proj₂ ∧-complement _)) refl )) (sym (proj₁ ∧-∨-distrib _ _ _))) (∧-cong refl (sym (deMorgan₁ _ _)))
tyty c (:binary op) inps = bin-tyty op c _ _

ss : ∀ sign {n} → :lit sign (var (zero {n})) :∧ var zero ≛ :lit sign (var zero) :∧ :lit sign :⊤
ss true = trans (∧-idempotent _) (sym (proj₂ ∧-identity _))
ss false = trans (proj₁ ∧-complement _) (let open Solver in solve 1 (λ x → :⊥ ⊜ :¬ x :∧ :¬ :⊤) refl _)

raise-sem : ∀ {n x} (e : Expr (Fin n)) ρ →
              ⟦ e ↑ ⟧ (x ∷ ρ) ≈ ⟦ e ⟧ ρ
raise-sem {n} {x} (:bin op a b) ρ = bin-cong op (raise-sem a ρ) (raise-sem b ρ)
raise-sem (:¬_ a) ρ = ¬-cong (raise-sem a ρ)
raise-sem (:const c) ρ =  refl
raise-sem (var x) ρ = refl

data All {A : Set} (P : A → Set) : {n : ℕ} → Vec A n → Set where
  [] : All P []
  _∷_ : ∀ {x m} {v : Vec A m} → P x → All P v → All P (x ∷ v)

expr-cata : ∀ {A : Set} {P : Expr A → Set} 
  → (∀ {c} → P (:const c))
  → (∀ op {a b} → P a → P b → P (:bin op a b))
  → (∀ {a} → P a → P (:¬ a))
  → (∀ {x} → P (var x))
  → ∀ e → P e
expr-cata const bin neg v (:bin op a b) = bin op (expr-cata const bin neg v a) (expr-cata const bin neg v b)
expr-cata const bin neg v (:¬_ a) = neg (expr-cata const bin neg v a)
expr-cata const bin neg v (:const y) = const
expr-cata const bin neg v (var x) = v

expr-cata' : ∀ {A} {P : Expr A → Set} 
  → (∀ oper (inp : Fin (InputsCount oper) → ∃ P) → P (:apply oper (proj₁ ∘ inp)))
  → (∀ {v} → P (var v))
  → ∀ e → P e
expr-cata' opers vars = expr-cata 
  (λ {c} → opers (:const c) (λ ()))
  (λ op pa pb → opers (:binary op) (flip lookup ((, pa) ∷ (, pb) ∷ [])))
  (λ pa → opers (:unary false) (flip lookup ((, pa) ∷ [])))
  vars

Elim-Under-And : ∀ {n} (sign : Bool) → (e : Expr (Fin (suc n))) → Set
Elim-Under-And sign e = ∃ (λ e' → :lit sign (var zero) :∧ e ≛ :lit sign (var zero) :∧ e' ↑)

lit-cong : ∀ (c : Bool) → {a b : Carrier} → a ≈ b → lit c a ≈ lit c b
lit-cong true eq = eq
lit-cong false eq = ¬-cong eq

apply-cong : ∀ (oper : BoolOperation)
  → {inp₁ : Inputs oper Carrier}
  → {inp₂ : Inputs oper Carrier}
  → (∀ i → inp₁ i ≈ inp₂ i)
  → apply oper inp₁ ≈ apply oper inp₂
apply-cong (:const y) eq = refl
apply-cong (:unary c) eq = lit-cong c (eq zero) 
apply-cong (:binary op) eq = bin-cong op (eq (# 0)) (eq (# 1))

eliminate-under-and' : ∀ {n} (sign : Bool) → (e : Expr (Fin (suc n))) → Elim-Under-And sign e
eliminate-under-and' {n} sign = expr-cata' opers (λ {v} → vars {v}) where

  vars : {v : Fin (suc n)} → Elim-Under-And sign (var v)
  vars {zero} = :lit sign :⊤ , trans (ss sign) (∧-cong refl (sym qq)) where
    qq : :lit sign :⊤ ↑ ≛ :lit sign :⊤
    qq with sign
    qq | true = refl
    qq | false = refl
  vars {suc i} = var i , refl

  opers : ∀ (oper : BoolOperation) (inp : Fin (InputsCount oper) → ∃ (Elim-Under-And {n} sign)) → Elim-Under-And sign (:apply oper (proj₁ ∘ inp))
  opers oper inp = :apply oper (proj₁ ∘ proj₂ ∘ inp) , λ { {x ∷ ρ} → let open EqReasoning setoid; xlit = ⟦ :lit sign (var zero) ⟧ (x ∷ ρ) in 
   begin
    xlit ∧ ⟦ :apply oper (proj₁ ∘ inp) ⟧ (x ∷ ρ)
   ≈⟨ ∧-cong refl (:apply-sem oper (proj₁ ∘ inp)) ⟩

    xlit ∧ apply oper ((λ f → f (x ∷ ρ)) ∘ ⟦_⟧ ∘ proj₁ ∘ inp)
   ≈⟨ tyty xlit oper (λ i → ⟦ (proj₁ ∘ inp) i ⟧ (x ∷ ρ)) ⟩
    xlit ∧ apply oper (_∧_ xlit ∘ (λ f → f (x ∷ ρ)) ∘ ⟦_⟧ ∘ proj₁ ∘ inp)
   ≈⟨ ∧-cong refl (apply-cong oper (λ i → trans (proj₂ (proj₂ (inp i))) (∧-cong refl (raise-sem ( proj₁ (proj₂ (inp i))) ρ)) )) ⟩
    xlit ∧ apply oper (_∧_ xlit ∘ (λ p → ⟦ p ⟧ ρ) ∘ proj₁ ∘ proj₂ ∘ inp)
   ≈⟨ sym (tyty xlit oper _) ⟩
    xlit ∧ apply oper (λ i → ⟦ (proj₁ ∘ proj₂ ∘ inp) i ⟧ ρ)

   ≈⟨ ∧-cong refl (sym (:apply-sem oper (proj₁ ∘ proj₂ ∘ inp)))  ⟩
    xlit ∧ ⟦ :apply oper (proj₁ ∘ proj₂ ∘ inp) ⟧ ρ
   ≈⟨ ∧-cong refl (sym (raise-sem (:apply oper (proj₁ ∘ proj₂ ∘ inp)) ρ)) ⟩
    xlit ∧ ⟦ :apply oper (proj₁ ∘ proj₂ ∘ inp) ↑ ⟧ (x ∷ ρ)
   ∎ }

eliminate-under-and : ∀ {n} (sign : Bool) → (e : Expr (Fin (suc n))) → ∃ (λ e' → :lit sign (var zero) :∧ e ≛ :lit sign (var zero) :∧ e' ↑)
eliminate-under-and sign (:bin op a b) with eliminate-under-and sign a | eliminate-under-and sign b
... | a' , a-prf | b' , b-prf = :bin op a' b' , (λ {ρ} → 
       trans (tyty _ (:binary op) (flip lookup (⟦ a ⟧ ρ ∷ ⟦ b ⟧ ρ ∷ []))) 
       (trans ( ∧-cong refl (bin-cong op a-prf b-prf)) 
        (sym (tyty _ (:binary op) (flip lookup (⟦ a' ↑ ⟧ ρ ∷ ⟦ b' ↑ ⟧ ρ ∷ []))))))
eliminate-under-and sign (:¬ a) with eliminate-under-and sign a
... | a' , a-prf = :¬ a' , (λ {ρ} → trans (tyty _ (:unary false) (flip lookup (⟦ a ⟧ ρ ∷ [])))
        (trans ( ∧-cong refl (¬-cong a-prf)) (sym(tyty _ (:unary false) (flip lookup (⟦ a' ↑ ⟧ ρ ∷ []))))))
eliminate-under-and sign (:const y) = :const y , refl
eliminate-under-and {n} sign (var zero) = :lit sign :⊤ , trans (ss sign) (∧-cong refl (sym qq)) where
  qq : :lit sign :⊤ ↑ ≛ :lit sign :⊤
  qq with sign
  qq | true = refl
  qq | false = refl
eliminate-under-and sign (var (suc i)) = var i , refl

:if : ∀ {A : Set} → Expr A → Expr A → Expr A → Expr A
:if c t f = c :∧ t :∨ :¬ c  :∧ f

if : Carrier → Carrier → Carrier → Carrier
if c t f = c ∧ t ∨ ¬ c  ∧ f


shannon-expand : ∀ {n} → (e : Expr (Fin (suc n))) → ∃₂ (λ a b → e ≛ :if (var zero) (a ↑) (b ↑))
shannon-expand e with eliminate-under-and true e | eliminate-under-and false e
... | e₁ , proof₁ | e₀ , proof₀ = e₁ , (e₀ , proof) where
  proof : e ≛ :if (var zero) (e₁ ↑) (e₀ ↑)
  proof {x ∷ ρ} = let open EqReasoning setoid in
   begin
    ⟦ e ⟧ (x ∷ ρ)
     ≈⟨ sym (trans (∧-cong (proj₂ ∨-complement _) refl) (proj₁ ∧-identity _)) ⟩
    (x ∨ ¬ x) ∧ ⟦ e ⟧ (x ∷ ρ)
     ≈⟨ proj₂ ∧-∨-distrib _ _ _ ⟩
    x ∧ ⟦ e ⟧ (x ∷ ρ) ∨ ¬ x ∧ ⟦ e ⟧ (x ∷ ρ)
     ≈⟨ ∨-cong (proof₁ {x ∷ ρ}) (proof₀ {x ∷ ρ}) ⟩
    if x (⟦ e₁ ↑ ⟧ (x ∷ ρ)) (⟦ e₀ ↑ ⟧ (x ∷ ρ))
   ∎

