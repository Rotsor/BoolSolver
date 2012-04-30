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
mapBF f (:op op params) = :op op (λ i → mapBF f (params i))
mapBF f (var v) = var (f v)

open import Data.Fin
open import Data.Nat

_↑ : ∀ {n} → Expr (Fin n) → Expr (Fin (suc n)) 
_↑ = mapBF suc

open import Data.Bool using (Bool; true; false)

:lit : Bool → ∀ {A} → Expr A → Expr A
:lit true x = x
:lit false x = :¬ x


import Data.Vec as Vec
open Vec

import Relation.Binary.EqReasoning as EqReasoning

bin-comassoc-2x2 : ∀ (op : BinOp) → let _⊕_ = bin op in ∀ {a b c d} → (a ⊕ b) ⊕ (c ⊕ d) ≈ (a ⊕ c) ⊕ (b ⊕ d)
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


bin-self-distribˡ : ∀ (op : BinOp) → let _⊕_ = bin op in ∀ c a b → (c ⊕ a) ⊕ (c ⊕ b) ≈ c ⊕ (a ⊕ b)
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

tyty : ∀ c → (oper : Op) → (inp : Inputs oper Carrier) → c ∧ apply oper inp ≈ c ∧ (apply oper ((_∧_ c) ∘ inp))
tyty c (:constant y) _ = refl
tyty c (:unary true) inps = sym (trans (sym (∧-assoc _ _ _)) (∧-cong (∧-idempotent c) refl))
tyty c (:unary false) inps = trans (trans (trans (sym (proj₁ ∨-identity _)) (∨-cong (sym (proj₂ ∧-complement _)) refl )) (sym (proj₁ ∧-∨-distrib _ _ _))) (∧-cong refl (sym (deMorgan₁ _ _)))
tyty c (:binary op) inps = bin-tyty op c _ _

raise-sem : ∀ {n x} (e : Expr (Fin n)) ρ →
              ⟦ e ↑ ⟧ (x ∷ ρ) ≈ ⟦ e ⟧ ρ
raise-sem {n} {x} (:op op params) ρ = apply-cong op (λ i → raise-sem (params i) ρ)
raise-sem (var x) ρ = refl

Elim-Under-And : ∀ {n} (sign : Bool) → (e : Expr (Fin (suc n))) → Set
Elim-Under-And sign e = ∃ (λ e' → :lit sign (var zero) :∧ e ≛ :lit sign (var zero) :∧ e' ↑)

dibilizm : ∀ {n} (sign : Bool) → :lit sign (:⊤ {Fin n}) ↑ ≛ :lit sign :⊤
dibilizm true = refl
dibilizm false = refl

ss : ∀ sign {n} → :lit sign (var (zero {n})) :∧ var zero ≛ :lit sign (var zero) :∧ :lit sign :⊤
ss true = trans (∧-idempotent _) (sym (proj₂ ∧-identity _))
ss false = trans (proj₁ ∧-complement _) (let open Solver in solve 1 (λ x → :⊥ ⊜ :¬ x :∧ :¬ :⊤) refl _)

eliminate-under-and : ∀ {n} (sign : Bool) → (e : Expr (Fin (suc n))) → Elim-Under-And sign e
eliminate-under-and sign (var zero) = :lit sign :⊤ , trans (ss sign) (∧-cong refl (sym (dibilizm sign)))
eliminate-under-and sign (var (suc i)) = var i , refl
eliminate-under-and sign (:op op inp) = result where
  rec = λ i → eliminate-under-and sign (inp i)
  result = :op op (proj₁ ∘ rec) , λ { {x ∷ ρ} → let open EqReasoning setoid; xlit = ⟦ :lit sign (var zero) ⟧ (x ∷ ρ) in 
   begin
    xlit ∧ ⟦ :op op (inp) ⟧ (x ∷ ρ)
   ≈⟨ refl ⟩
    xlit ∧ apply op (λ i → ⟦ inp i ⟧ (x ∷ ρ))
   ≈⟨ tyty xlit op (λ i → ⟦ inp i ⟧ (x ∷ ρ)) ⟩
    xlit ∧ apply op (λ i → xlit ∧ ⟦ inp i ⟧ (x ∷ ρ))
   ≈⟨ ∧-cong refl (apply-cong op (λ i → trans (proj₂ (rec i)) (∧-cong refl (raise-sem ( proj₁ (rec i)) ρ)) )) ⟩
    xlit ∧ apply op (_∧_ xlit ∘ (λ p → ⟦ p ⟧ ρ) ∘ proj₁ ∘ rec)
   ≈⟨ sym (tyty xlit op _) ⟩
    xlit ∧ apply op (λ i → ⟦ (proj₁ ∘ rec) i ⟧ ρ)
   ≈⟨ refl ⟩
    xlit ∧ ⟦ :op op (proj₁ ∘ rec) ⟧ ρ
   ≈⟨ ∧-cong refl (sym (raise-sem (:op op (proj₁ ∘ rec)) ρ)) ⟩
    xlit ∧ ⟦ :op op (proj₁ ∘ rec) ↑ ⟧ (x ∷ ρ)
   ∎ }

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
