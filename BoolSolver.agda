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

bool-bin : ∀ (op : BinOp) → Bool → Bool → Bool
bool-bin And = Data.Bool._∧_
bool-bin Or = Data.Bool._∨_

bool-lit : Bool → Bool → Bool
bool-lit true x = x
bool-lit false x = Data.Bool.not x

bool-bin-sem : ∀ op a b → bin op (const a) (const b) ≈ const (bool-bin op a b)
bool-bin-sem And true b = let open Solver in solve 1 (λ b → :⊤ :∧ b ⊜ b) refl _
bool-bin-sem And false b = let open Solver in solve 1 (λ b → :⊥ :∧ b ⊜ :⊥) refl _
bool-bin-sem Or true b = let open Solver in solve 1 (λ b → :⊤ :∨ b ⊜ :⊤) refl _
bool-bin-sem Or false b = let open Solver in solve 1 (λ b → :⊥ :∨ b ⊜ b) refl _

bool-lit-sem : ∀ neg a → lit neg (const a) ≈ const (bool-lit neg a)
bool-lit-sem true a = refl
bool-lit-sem false a = bool-neg-sem a

if-cong : ∀ {a₁ b₁ c₁ a₂ b₂ c₂} → c₁ ≈ c₂ → a₁ ≈ a₂ → b₁ ≈ b₂ → if c₁ a₁ b₁ ≈ if c₂ a₂ b₂
if-cong c-eq a-eq b-eq = ∨-cong (∧-cong c-eq a-eq) (∧-cong (¬-cong c-eq) b-eq)

open import Data.Vec

import Relation.Binary.EqReasoning as EqReasoning

bool-apply : (op : Op) → Inputs op Bool → Bool
bool-apply (:constant c) inps = c
bool-apply (:unary neg) inps = bool-lit neg (inps (# 0))
bool-apply (:binary op) inps = bool-bin op (inps (# 0)) (inps (# 1))

bool-apply-sem : ∀ (op : Op) → (inp : Inputs op Bool) → apply op (const ∘ inp) ≈ const (bool-apply op inp)
bool-apply-sem (:constant c) inp = refl
bool-apply-sem (:unary neg) inp = bool-lit-sem neg _
bool-apply-sem (:binary op) inp = bool-bin-sem op _ _

eval'' : (e : Expr (Fin 0)) → ∃ (λ c → (∀ {ρ} → ⟦ e ⟧ ρ ≈ const c))
eval'' (var ())
eval'' (:op op params) =
  bool-apply op (proj₁ ∘ rec) ,
  trans (apply-cong op (λ i → proj₂ (rec i))) (bool-apply-sem op _) where
   rec = (λ x → eval'' (params x))

import Data.Empty

wtf-no-constants : (e : Expr (Fin 0)) → (No-Constants e → Data.Empty.⊥)
wtf-no-constants (BooleanExpr.:op (BooleanExpr.:constant c) inp) bt = bt
wtf-no-constants (BooleanExpr.:op (BooleanExpr.:unary neg) inp) bt = wtf-no-constants (inp (# 0)) (bt (# 0))
wtf-no-constants (BooleanExpr.:op (BooleanExpr.:binary op) inp) bt = wtf-no-constants (inp (# 0)) (bt (# 0))
wtf-no-constants (BooleanExpr.var ()) bt

eval''' : (e : Expr (Fin 0)) → ∃ (λ c → (∀ {ρ} → ⟦ e ⟧ ρ ≈ const c))
eval''' e with constantPropagation e | constants-propagated e
eval''' e | BooleanExpr.:op (BooleanExpr.:constant c) y , prf | proped = c , prf
eval''' e | BooleanExpr.:op (BooleanExpr.:unary neg) y , prf | proped = Data.Empty.⊥-elim (wtf-no-constants (y zero) (proped zero))
eval''' e | BooleanExpr.:op (BooleanExpr.:binary op) y , prf | proped = Data.Empty.⊥-elim (wtf-no-constants (y zero) (proped zero))
eval''' e | BooleanExpr.var () , prf | proped

{-eval : (e : Expr (Fin 0)) → ∃ (λ c → (∀ {ρ} → ⟦ e ⟧ ρ ≈ const c))
eval (:op (:binary op) params) with eval (params (# 0)) | eval (params (# 1))
... | a' , a-proof | b' , b-proof = (bool-bin op a' b') , (trans (bin-cong op a-proof b-proof) (bool-bin-sem op a' b'))
eval (:op (:unary true) a) = eval (a (# 0))
eval (:op (:unary false) a) with eval (a (# 0))
... | a' , a-proof = Data.Bool.not a' , trans (¬-cong a-proof) (bool-neg-sem a')
eval (:op (:constant y) _) = y , refl
eval (var ()) -}

normalise : ∀ {n} → (f : Expr (Fin n)) → ∃ (λ nf → ∀ {ρ} → ⟦ f ⟧ ρ ≈ ⇓⟦ nf ⟧ ρ)
normalise {zero} f with eval'' f
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
