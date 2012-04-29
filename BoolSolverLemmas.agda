
open import Level using () renaming (zero to ₀)
open import Algebra

module BoolSolverLemmas (Alg : BooleanAlgebra ₀ ₀) where


open BooleanAlgebra Alg

import Relation.Binary.EqReasoning as EqReasoning
open EqReasoning setoid
open import Data.Product

import Algebra.Props.BooleanAlgebra as BoolProps
open BoolProps (Alg)
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

if : Carrier → Carrier → Carrier → Carrier
if c t f = c ∧ t ∨ ¬ c  ∧ f

if-same-elim : ∀ {cond x} → if cond x x ≈ x
if-same-elim {c} {x} = 
  begin
   if c x x
    ≈⟨ refl ⟩
   c ∧ x ∨ ¬ c ∧ x
    ≈⟨ sym (proj₂ ∧-∨-distrib x c (¬ c)) ⟩
   (c ∨ ¬ c) ∧ x
    ≈⟨ ∧-cong (proj₂ ∨-complement c) refl ⟩
   ⊤ ∧ x
    ≈⟨ proj₁ ∧-identity x ⟩
   x
  ∎

if-⊤-⊥-simpl : ∀ {x} → if x ⊤ ⊥ ≈ x
if-⊤-⊥-simpl {x} = 
  begin
    if x ⊤ ⊥
     ≈⟨ refl ⟩
    x ∧ ⊤ ∨ ¬ x ∧ ⊥
     ≈⟨ ∨-cong (proj₂ ∧-identity _) (proj₂ ∧-zero _) ⟩
    x ∨ ⊥
     ≈⟨ proj₂ ∨-identity _ ⟩
    x
  ∎


if-swap : ∀ {a b c} → if (¬ c) a b ≈ if c b a
if-swap {a} {b} {c} =
  begin
    ¬ c ∧ a ∨ ¬ ¬ c ∧ b
     ≈⟨ ∨-cong refl (∧-cong (¬-involutive c) refl) ⟩
    ¬ c ∧ a ∨ c ∧ b
     ≈⟨ ∨-comm _ _ ⟩
    c ∧ b ∨ ¬ c ∧ a
  ∎

-- import Algebra.RingSolver as Solver

-- open Solver ∨-∧-semiring

∧-comassoc-2x2 : ∀ {a b c d} → (a ∧ b) ∧ (c ∧ d) ≈ (a ∧ c) ∧ (b ∧ d)
∧-comassoc-2x2 {c} {a} {d} {b} =
 begin
  (c ∧ a) ∧ (d ∧ b)
    ≈⟨ ∧-assoc _ _ _ ⟩
  c ∧ (a ∧ d ∧ b)
    ≈⟨ ∧-cong refl (sym (∧-assoc _ _ _)) ⟩
  c ∧ ((a ∧ d) ∧ b)
    ≈⟨ ∧-cong refl (∧-cong (∧-comm _ _) refl) ⟩
  c ∧ ((d ∧ a) ∧ b)
    ≈⟨ ∧-cong refl (∧-assoc d a b) ⟩
  c ∧ (d ∧ (a ∧ b))
    ≈⟨ sym (∧-assoc _ _ _) ⟩
  (c ∧ d) ∧ (a ∧ b)
 ∎


∧-∧-distribˡ : ∀ c a b → (c ∧ a) ∧ (c ∧ b) ≈ c ∧ (a ∧ b)
∧-∧-distribˡ c a b =
 begin
  (c ∧ a) ∧ (c ∧ b)
    ≈⟨ ∧-comassoc-2x2 ⟩
  (c ∧ c) ∧ (a ∧ b)
    ≈⟨ ∧-cong (∧-idempotent c) refl ⟩
  c ∧ (a ∧ b)
 ∎

if-and-distribˡ : ∀ {c d a b} → if c (a ∧ b) d ≈ if c a d ∧ if c b d
if-and-distribˡ {c} {d} {a} {b} =
 begin
  c ∧ (a ∧ b) ∨ ¬ c ∧ d
   ≈⟨ ∨-cong (sym (∧-∧-distribˡ _ _ _)) refl ⟩
  ((c ∧ a) ∧ (c ∧ b)) ∨ ¬ c ∧ d
   ≈⟨ proj₂ ∨-∧-distrib (¬ c ∧ d) (c ∧ a) (c ∧ b) ⟩
  (c ∧ a ∨ ¬ c ∧ d) ∧ (c ∧ b ∨ ¬ c ∧ d)
 ∎

if-and-distribʳ : ∀ {c d a b} → if c d (a ∧ b) ≈ if c d a ∧ if c d b
if-and-distribʳ {c} {d} {a} {b} =
 begin
  if c d (a ∧ b)
   ≈⟨ sym if-swap ⟩
  if (¬ c) (a ∧ b) d
   ≈⟨ if-and-distribˡ ⟩
  if (¬ c) a d ∧ if (¬ c) b d
   ≈⟨ ∧-cong if-swap if-swap ⟩
  if c d a ∧ if c d b
 ∎

∧-∨-distrib-2x2 : ∀ {a b c d} → (a ∨ b) ∧ (c ∨ d) ≈ (a ∧ c ∨ a ∧ d) ∨ (b ∧ c ∨ b ∧ d)
∧-∨-distrib-2x2 {a} {b} {c} {d} =
 begin
  (a ∨ b) ∧ (c ∨ d)
   ≈⟨ proj₂ ∧-∨-distrib (c ∨ d) a b ⟩
  a ∧ (c ∨ d) ∨ b ∧ (c ∨ d)
   ≈⟨ ∨-cong (proj₁ ∧-∨-distrib _ _ _) (proj₁ ∧-∨-distrib _ _ _) ⟩
  (a ∧ c ∨ a ∧ d) ∨ (b ∧ c ∨ b ∧ d)
 ∎

open import Function

if-and-distrib : ∀ {a b c d cond} → if cond (a ∧ b) (c ∧ d) ≈ if cond a c ∧ if cond b d
if-and-distrib {a} {b} {c} {d} {f} =
 begin
  if f (a ∧ b) (c ∧ d)
   ≈⟨ refl ⟩
  f ∧ (a ∧ b) ∨ ¬ f ∧ (c ∧ d)
   ≈⟨ sym (proj₂ ∨-identity _) ⟨ ∨-cong ⟩ sym (proj₁ ∨-identity _) ⟩
  (f ∧ (a ∧ b) ∨ ⊥) ∨ (⊥ ∨ (¬ f) ∧ (c ∧ d))
   ≈⟨ refl ⟨ ∨-cong ⟩ trans kill (∧-cong (∧-comm _ _) refl) ⟨ ∨-cong ⟩ (kill ⟨ ∨-cong ⟩ refl) ⟩
  (f ∧ (a ∧ b) ∨ (f ∧ ¬ f) ∧ (a ∧ d)) ∨ ((¬ f ∧ f) ∧ (c ∧ b) ∨ (¬ f) ∧ (c ∧ d))
   ≈⟨         sym (∧-∧-distribˡ _ _ _) ⟨ ∨-cong ⟩ ∧-comassoc-2x2  
      ⟨ ∨-cong ⟩   (∧-comassoc-2x2     ⟨ ∨-cong ⟩ sym (∧-∧-distribˡ _ _ _) ) ⟩
  ((f ∧ a) ∧ (f ∧ b) ∨ (f ∧ a) ∧ (¬ f ∧ d)) ∨ ((¬ f ∧ c) ∧ (f ∧ b) ∨ (¬ f ∧ c) ∧ (¬ f ∧ d))
   ≈⟨ sym ∧-∨-distrib-2x2 ⟩
  (f ∧ a ∨ ¬ f ∧ c) ∧ (f ∧ b ∨ ¬ f ∧ d)
   ≈⟨ refl ⟩
  if f a c ∧ if f b d
 ∎ where
  kill : ∀ {x} → ⊥ ≈ (¬ f ∧ f) ∧ x
  kill = sym ( trans (∧-cong (proj₁ ∧-complement f) refl) (proj₁ ∧-zero _))

{-if-absorbs-∧ : ∀ {a b c} → if c a b ∨ (a ∧ b) ≈ if c a b
if-absorbs-∧ {a} {b} {c} =
 begin
  if c a b ∨ (a ∧ b)
   ≈⟨ ∨-cong refl (sym if-same-elim) ⟩
  if c a b ∨ if c (a ∧ b) (a ∧ b)
   ≈⟨ sym if-and-distrib ⟩
  if c (a ∧ (a ∧ b)) (b ∧ (a ∧ b))
   ≈⟨ if-cong refl {!!} {!!} ⟩
  if c a b
 ∎

 tricky : ∀ {a b c} → c ∧ a ∨ ¬ c ∧ b ≈ (¬ c ∨ a) ∧ (c ∨ b)
tricky =
 begin
  c ∧ a ∨ ¬ c ∧ b
   ≈⟨ ? ⟩
  (c ∧ a ∨ ¬ c ∧ b
   ≈⟨ ? ⟩
  (¬ c ∧ b) ∨ (a ∧ c ∨ a ∧ b)
   ≈⟨ ? ⟩
  (¬ c ∧ c ∨ ¬ c ∧ b) ∨ (a ∧ c ∨ a ∧ b)
   ≈⟨ ? ⟩
  (¬ c ∨ a) ∧ (c ∨ b)
 ∎ -}

if-neg-distrib : ∀ {a b cond} → if cond (¬ a) (¬ b) ≈ ¬ if cond a b
if-neg-distrib {a} {b} {cond} = 
 begin
  cond ∧ ¬ a ∨ ¬ cond ∧ ¬ b
   ≈⟨ {!sym (deMorgan₂ _ _)!} ⟩
  (¬ cond ∨ ¬ a) ∧ (¬ ¬ cond ∨ ¬ b)
   ≈⟨ sym (deMorgan₁ _ _) ⟨ ∧-cong ⟩ sym (deMorgan₁ _ _) ⟩
  ¬ (cond ∧ a) ∧ ¬ (¬ cond ∧ b)
   ≈⟨ sym (deMorgan₂ _ _) ⟩
  ¬ (cond ∧ a ∨ ¬ cond ∧ b)
 ∎
  

if-or-distrib : ∀ {a b c d cond} → if cond (a ∨ b) (c ∨ d) ≈ if cond a c ∨ if cond b d
if-or-distrib {a} {b} {c} {d} {cond} = {!!}


 {-
 begin
  if cond (a ∨ b) (c ∨ d)
  if (¬ cond) (a ∨ b) (c ∨ d)
   {!!} -}

