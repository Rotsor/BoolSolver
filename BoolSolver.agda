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

data NF : ℕ → Set where
  :const : Bool → NF 0
  _/\_ : ∀ {n} → NF n → NF n → NF (suc n)

open import Data.Vec

⇓⟦_⟧ : ∀ {n} → NF n → Vec Carrier n → Carrier
⇓⟦_⟧ (:const y) ρ = const y
⇓⟦_⟧ (l /\ r) ρ  = if (head ρ) (⇓⟦ l ⟧ (tail ρ)) (⇓⟦ r ⟧ (tail ρ))

sem : ∀ {n} → NF n → Expr (Fin n)
sem (:const y) = :const y
sem (l /\ r) = :if (var zero) (sem l ↑) (sem r ↑)

boolOpSem : ∀ (op : Op) → Bool → Bool → Bool
boolOpSem And = Data.Bool._∧_
boolOpSem Or = Data.Bool._∨_

const-op-sem : ∀ op a b → const (boolOpSem op a b) ≈ bin op (const a) (const b)
const-op-sem And true b = let open Solver in solve 1 (λ b → b ⊜ :⊤ :∧ b) refl _
const-op-sem And false b = let open Solver in solve 1 (λ b → :⊥ ⊜ :⊥ :∧ b) refl _
const-op-sem Or true b = let open Solver in solve 1 (λ b → :⊤ ⊜ :⊤ :∨ b) refl _
const-op-sem Or false b = let open Solver in solve 1 (λ b → b ⊜ :⊥ :∨ b) refl _

if-cong : ∀ {a₁ b₁ c₁ a₂ b₂ c₂} → c₁ ≈ c₂ → a₁ ≈ a₂ → b₁ ≈ b₂ → if c₁ a₁ b₁ ≈ if c₂ a₂ b₂
if-cong c-eq a-eq b-eq = ∨-cong (∧-cong c-eq a-eq) (∧-cong (¬-cong c-eq) b-eq)

{-if-op-distrib : ∀ {op} {cond a b c d} → if cond (bin op a b) (bin op c d) ≈ bin op (if cond a c) (if cond b d)
if-op-distrib = {!!} 

:if-op-distrib : ∀ {op} {n a b c d cond} → :if {Fin n} cond (:bin op a b) (:bin op c d) ≛ :bin op (:if cond a c) (:if cond b d)
:if-op-distrib {op} = if-op-distrib {op}
-}
open import Data.Vec


import Relation.Binary.EqReasoning as EqReasoning

{-if-nf-distrib : ∀ {n} (f : NF n) → ∀ {x y z} {ρ} → if x (⇓⟦ f ⟧ y) (⇓⟦ f ⟧ z) ≈ ⇓⟦ f ⟧ (if x y z)
if-nf-distrib f = ?-}

applyNF : ∀ {n m} (f : NF (suc n)) (x : NF m) → NF (m + n)
applyNF f (x₁ /\ x₀) = applyNF f x₁ /\ applyNF f x₀
applyNF (f₁ /\ f₀) (:const x) = Data.Bool.if_then_else_ x f₁ f₀

{-applynf-theorem : ∀ {m n} → (f : NF (suc n)) → (x : NF m) → ∀ p q 
                  → ⇓⟦ applyNF f x ⟧ (p ++ q) ≈ ⇓⟦ f ⟧ (⇓⟦ x ⟧ p ∷ q)
applynf-theorem (f₁ /\ f₀) (:const true) [] q = 
      (let open Solver in solve 2 (λ x y → x ⊜ :if :⊤ x y) refl _ _)
applynf-theorem (f₁ /\ f₀) (:const false) [] q =
      (let open Solver in solve 2 (λ x y → y ⊜ :if :⊥ x y) refl _ _)
applynf-theorem (f₁ /\ f₀) (x₁ /\ x₀) (ph ∷ p) q = proof where
  rec₁ : ⇓⟦ (applyNF (f₁ /\ f₀) x₁) ⟧ (p ++ q) ≈ ⇓⟦ (f₁ /\ f₀) ⟧ (⇓⟦ x₁ ⟧ p ∷ q)
  rec₁ = applynf-theorem (f₁ /\ f₀) x₁ p q

  rec₂ : ⇓⟦ applyNF (f₁ /\ f₀) x₀ ⟧ (p ++ q) ≈ ⇓⟦ (f₁ /\ f₀) ⟧ (⇓⟦ x₀ ⟧ p ∷ q)
  rec₂ = applynf-theorem (f₁ /\ f₀) x₀ p q

  proof : ⇓⟦ applyNF (f₁ /\ f₀) (x₁ /\ x₀) ⟧ (ph ∷ p ++ q) ≈ ⇓⟦ (f₁ /\ f₀) ⟧ (⇓⟦ (x₁ /\ x₀) ⟧ (ph ∷ p) ∷ q)
  proof = trans (if-cong refl rec₁ rec₂) {!!} -- if ph (if (⇓⟦ x₁ ⟧ p) (⇓⟦ f₁ ⟧ q) (⇓⟦ f₀ ⟧ q))  (if (⇓⟦ x₀ ⟧ p) (⇓⟦ f₁ ⟧ q) (⇓⟦ f₀ ⟧ q)) ) -}

eval : (e : Expr (Fin 0)) → ∃ (λ c → (∀ {ρ} → ⟦ e ⟧ ρ ≈ const c))
eval (:bin op a b) with eval a | eval b
... | a' , a-proof | b' , b-proof = (boolOpSem op a' b') , (trans (op-cong op a-proof b-proof) (sym (const-op-sem op a' b')))
eval (:¬_ a) with eval a
... | a' , a-proof = Data.Bool.not a' , trans (¬-cong a-proof) (const-neg-const a')
eval (:const y) = y , refl
eval (var ())

normalise : ∀ {n} → (f : Expr (Fin n)) → ∃ (λ nf → ∀ {ρ} → ⟦ f ⟧ ρ ≈ ⇓⟦ nf ⟧ ρ)
normalise {zero} f with eval f
... | f-val , proof = (:const f-val) , proof
normalise {suc n} f with shannon-expand f
... | f₁ , f₀ , snannon-proof with normalise f₁ | normalise f₀
... | nf₁ , nf₁-proof | nf₀ , nf₀-proof  = nf₁ /\ nf₀ , trans snannon-proof (prf _) where
  prf : ∀ ρ → ⟦ :if (var zero) (f₁ ↑) (f₀ ↑) ⟧ ρ ≈ ⇓⟦ nf₁ /\ nf₀ ⟧ ρ
  prf (x ∷ ρ) = if-cong refl (trans (raise-sem f₁ ρ) nf₁-proof) (trans (raise-sem f₀ ρ) nf₀-proof)

{-binNF : ∀ {n} → (op : Op) → (a b : NF n) → ∃ (λ c → :bin op (sem a) (sem b) ≛ sem c)
binNF op (:const a) (:const b) = :const (boolOpSem op a b) , sym (const-op-sem op a b {zero} {[]})
binNF op (a₀ /\ a₁) (b₀ /\ b₁) with binNF op a₀ b₀ | binNF op a₁ b₁
... | r₀ , proof₀ | r₁ , proof₁ = r₀ /\ r₁ , proof
  where
   pr₀ : ∀ {x ρ} → bin op (⟦ sem a₀ ↑ ⟧ (x ∷ ρ)) (⟦ sem b₀ ↑ ⟧ (x ∷ ρ)) ≈ ⟦ sem r₀ ↑ ⟧ (x ∷ ρ)
   pr₀ {x} {ρ} =  trans (op-cong {op} (raise-sem (sem a₀) ρ) (raise-sem (sem b₀) ρ)) (trans proof₀ (sym (raise-sem (sem r₀) ρ)))

   pr₁ : ∀ {x ρ} → bin op (⟦ sem a₁ ↑ ⟧ (x ∷ ρ)) (⟦ sem b₁ ↑ ⟧ (x ∷ ρ)) ≈ ⟦ sem r₁ ↑ ⟧ (x ∷ ρ)
   pr₁ {x} {ρ} =  trans (op-cong {op} (raise-sem (sem a₁) ρ) (raise-sem (sem b₁) ρ)) (trans proof₁ (sym (raise-sem (sem r₁) ρ)))

   proof : :bin op (sem (a₀ /\ a₁)) (sem (b₀ /\ b₁)) ≛ :if (var zero) (sem r₀ ↑) (sem r₁ ↑)
   proof {x ∷ ρ} = let open EqReasoning setoid in
    begin
     ⟦ :bin op (sem (a₀ /\ a₁)) (sem (b₀ /\ b₁)) ⟧ (x ∷ ρ)
      ≈⟨ refl ⟩
     bin op (if x (⟦ sem a₀ ↑ ⟧ (x ∷ ρ)) (⟦ sem a₁ ↑ ⟧ (x ∷ ρ))) (if x (⟦ sem b₀ ↑ ⟧ (x ∷ ρ)) (⟦ sem b₁ ↑ ⟧ (x ∷ ρ)))
      ≈⟨ sym (if-op-distrib {op} {x}) ⟩
     if x (bin op (⟦ sem a₀ ↑ ⟧ (x ∷ ρ)) (⟦ sem b₀ ↑ ⟧ (x ∷ ρ))) (bin op (⟦ sem a₁ ↑ ⟧ (x ∷ ρ)) (⟦ sem b₁ ↑ ⟧ (x ∷ ρ)))
      ≈⟨ if-cong refl pr₀ pr₁ ⟩
     if x (⟦ sem r₀ ↑ ⟧ (x ∷ ρ)) (⟦ sem r₁ ↑ ⟧ (x ∷ ρ))
      ≈⟨ refl ⟩
     ⟦ :if (var zero) (sem r₀ ↑) (sem r₁ ↑) ⟧ (x ∷ ρ)
    ∎ -}

 {-
andNF (:const l) r = ?
andNF 0# b = cast (sym (proj₁ ∧-zero _)) 0#
andNF 1# b = cast (sym (proj₁ ∧-identity _)) b
andNF (cast eq a) b = cast (∧-cong eq refl) (andNF a b)
andNF a (cast eq b) = cast (∧-cong refl eq) (andNF a b)
andNF (a₀ /\ a₁) (b₀ /\ b₁) = cast if-and-distrib (andNF a₀ b₀ /\ andNF a₁ b₁) -}


-- import BoolSolverLemmas
-- open BoolSolverLemmas Alg

{-

if-or-distrib : ∀ {a b c d cond} → if cond (a ∨ b) (c ∨ d) ≈ if cond a c ∨ if cond b d
if-or-distrib {a} {b} {c} {d} {cond} = {!!}

if-neg-distrib : ∀ {a b cond} → if cond (¬ a) (¬ b) ≈ ¬ if cond a b
if-neg-distrib {a} {b} {cond} = {!!}


data NF : {n : ℕ} → Expr (Fin n) → Set where
  0# : NF {0} :⊥
  1# : NF {0} :⊤
  _/\_ : ∀ {n a b} → NF {n} a → NF b → NF (:if (var zero) (b ↑) (a ↑))
  cast : ∀ {n a b} → a ≛ b → NF {n} a → NF {n} b

andNF : ∀ {n a b} → NF {n} a → NF b → NF (a :∧ b)
andNF 0# b = cast (sym (proj₁ ∧-zero _)) 0#
andNF 1# b = cast (sym (proj₁ ∧-identity _)) b
andNF (cast eq a) b = cast (∧-cong eq refl) (andNF a b)
andNF a (cast eq b) = cast (∧-cong refl eq) (andNF a b)
andNF (a₀ /\ a₁) (b₀ /\ b₁) = cast if-and-distrib (andNF a₀ b₀ /\ andNF a₁ b₁)

orNF : ∀ {n a b} → NF {n} a → NF b → NF (a :∨ b)
orNF 0# b = cast (sym (proj₁ ∨-identity _)) b
orNF 1# b = cast (sym (proj₁ ∨-zero _)) 1#
orNF (cast eq a) b = cast (∨-cong eq refl) (orNF a b)
orNF a (cast eq b) = cast (∨-cong refl eq) (orNF a b)
orNF (a₀ /\ a₁) (b₀ /\ b₁) = cast if-or-distrib (orNF a₀ b₀ /\ orNF a₁ b₁)

negNF : ∀ {n a} → NF {n} a → NF (:¬ a)
negNF 0# = cast (sym ¬⊥=⊤) 1#
negNF 1# = cast (sym ¬⊤=⊥) 0#
negNF (a /\ b) = cast if-neg-distrib (negNF a /\ negNF b)
negNF (cast eq x) = cast (¬-cong eq) (negNF x)

norm1 : ∀ {n} → NF {n} :⊤
norm1 {zero} = 1#
norm1 {suc n} = cast {!!} {-if-same-elim -} (norm1 /\ norm1)

norm0 : ∀ {n} → NF {n} :⊥
norm0 {zero} = 0#
norm0 {suc n} = cast {!!} {- if-same-elim -} (norm0 /\ norm0)

normvar : ∀ {n} m → NF {n} (var m)
normvar zero = cast {!!} {- if-⊤-⊥-simpl -} (norm0 /\ norm1)
normvar (suc i) = cast {!!} {- if-same-elim -} (normvar i /\ normvar i)

normaliseBF : ∀ {n} → (f : Expr (Fin n)) → NF f
normaliseBF (a :∧ b) = andNF (normaliseBF a) (normaliseBF b)
normaliseBF (a :∨ b) = orNF (normaliseBF a) (normaliseBF b)
normaliseBF (:¬ y) = negNF (normaliseBF y)
normaliseBF :⊤ = norm1
normaliseBF :⊥ = norm0
normaliseBF (var v) = normvar v

⇓⟦_⟧ : ∀ {n f} → NF {n} f → Vec Carrier n → Carrier
⇓⟦ 0# ⟧ vars = ⊥
⇓⟦ 1# ⟧ vars = ⊤
⇓⟦ l /\ r ⟧ (h ∷ t) = if h (⇓⟦ r ⟧ t)  (⇓⟦ l ⟧ t)
⇓⟦ cast _ x ⟧ vars = ⇓⟦ x ⟧ vars

nf-sound : ∀ {n p} (nf : NF {n} p) ρ →
             ⇓⟦ nf ⟧ ρ ≈ ⟦ p ⟧ ρ
nf-sound 0# ρ = refl
nf-sound 1# ρ = refl
nf-sound (_/\_ {a = a} {b} l r) (x ∷ xs) = ∨-cong 
   (∧-cong refl (trans (nf-sound r xs) (sym (raise-sem b xs)))) 
   (∧-cong refl (trans (nf-sound l xs) (sym (raise-sem a xs))))
nf-sound (cast eq x) ρ = trans (nf-sound x ρ) eq

-}

⟦_⇓⟧ : {n : ℕ} → Expr (Fin n) → Vec Carrier n → Carrier
⟦_⇓⟧ expr = ⇓⟦ proj₁ (normalise expr) ⟧

correct : ∀ {n} (e : Expr (Fin n)) (ρ : Vec Carrier n) → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct e ρ = sym (proj₂ (normalise e) {ρ})

open Reflection setoid var ⟦_⟧ ⟦_⇓⟧ correct

theoremm : ∀ x y z → x ∧ (y ∨ z) ≈ y ∧ x ∨ z ∧ z ∧ x ∧ x ∧ ⊤
theoremm = solve 3 (λ x y z → x :∧ (y :∨ z) ⊜ y :∧ x :∨ z :∧ z :∧ x :∧ x :∧ :⊤) refl

theoremm2 : ∀ x y → ¬ (¬ x ∧ y) ≈ x ∨ ¬ y
theoremm2 = solve 2 (λ x y → :¬ (:¬ x :∧ y) ⊜ x :∨ :¬ y) refl

