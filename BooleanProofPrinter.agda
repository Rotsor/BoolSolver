
module BooleanProofPrinter where

record Input : Set₁ where
 field
   A : Set
   _∧_ : A → A → A
   _∨_ : A → A → A
   ¬_ : A → A
   ⊤ : A
   ⊥ : A

module Dummy (Inp : Input) where

  open Input Inp
  open import Algebra
  open import Algebra.Structures

  infix 3 _≈_

  open import Algebra.FunctionProperties
  open import Relation.Binary

  data _≈_ : A → A → Set where
      refl  : Reflexive _≈_
      sym   : Symmetric _≈_
      trans : Transitive _≈_
      ∨-comm        : Commutative _≈_ _∨_
      ∨-assoc       : Associative _≈_ _∨_
      ∨-cong        : _∨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
      ∧-comm        : Commutative _≈_ _∧_
      ∧-assoc       : Associative _≈_ _∧_
      ∧-cong        : _∧_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
      ∧-absorbs-∨    : _Absorbs_ _≈_ _∧_ _∨_
      ∨-absorbs-∧    : _Absorbs_ _≈_ _∨_ _∧_
      ∨-∧-distribʳ : _DistributesOverʳ_ _≈_ _∨_  _∧_
      ∨-complementʳ         : RightInverse _≈_ ⊤ ¬_ _∨_
      ∧-complementʳ         : RightInverse _≈_ ⊥ ¬_ _∧_
      ¬-cong                : ¬_ Preserves _≈_ ⟶ _≈_

  onRefl : ∀ {a b} → a ≈ b → ∀ {P : A → Set} → P b → P a → P a
  onRefl refl pb _ = pb
  onRefl _ _ pa = pa

  trans-eliming₂ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  trans-eliming₂ ab refl = ab
  trans-eliming₂ ab bc = trans ab bc

  trans-eliming : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  trans-eliming refl bc = bc
  trans-eliming ab bc = trans-eliming₂ ab bc

  ∨-cong-eliming : ∀ {a b c d} → a ≈ b → c ≈ d → a ∨ c ≈ b ∨ d
  ∨-cong-eliming refl refl = refl
  ∨-cong-eliming eq1 eq2 = ∨-cong eq1 eq2

  ∧-cong-eliming : ∀ {a b c d} → a ≈ b → c ≈ d → a ∧ c ≈ b ∧ d
  ∧-cong-eliming refl refl = refl
  ∧-cong-eliming eq1 eq2 = ∧-cong eq1 eq2

  ¬-cong-eliming : ∀ {a b} → a ≈ b → ¬ a ≈ ¬ b
  ¬-cong-eliming refl = refl
  ¬-cong-eliming eq1 = ¬-cong eq1

  sym-eliming : ∀ {a b} → a ≈ b → b ≈ a
  sym-eliming refl = refl
  sym-eliming ab = sym ab

  refl-elim : ∀ {a b} → a ≈ b → a ≈ b
  refl-elim refl = refl
  refl-elim (sym y) = sym-eliming (refl-elim y)
  refl-elim (trans l r) = trans-eliming (refl-elim l) (refl-elim r)

  refl-elim (∨-cong l r) = ∨-cong-eliming (refl-elim l) (refl-elim r)
  refl-elim (∧-cong l r) = ∧-cong-eliming (refl-elim l) (refl-elim r)
  refl-elim (¬-cong x) = ¬-cong-eliming (refl-elim x)

  refl-elim prf = prf

  open import Data.Product

  Alg : BooleanAlgebra _ _
  Alg = record {
          isBooleanAlgebra = record {
                               isDistributiveLattice = record { isLattice = record {
                                                                              isEquivalence = record { refl = refl; sym = sym; trans = trans };
                                                                              ∨-comm = ∨-comm;
                                                                              ∨-assoc = ∨-assoc;
                                                                              ∨-cong = ∨-cong;
                                                                              ∧-comm = ∧-comm;
                                                                              ∧-assoc = ∧-assoc;
                                                                              ∧-cong = ∧-cong;
                                                                              absorptive = ∨-absorbs-∧ , ∧-absorbs-∨ }; ∨-∧-distribʳ = ∨-∧-distribʳ };
                               ∨-complementʳ = ∨-complementʳ;
                               ∧-complementʳ = ∧-complementʳ;
                               ¬-cong = ¬-cong } }

  import ConstantPropagation
  open  ConstantPropagation Alg

  open Solver

  theorem3 : ∀ x y z → (x ∨ (z ∧ ⊥)) ∨ (y ∧ ⊤) ≈ x ∨ y
  theorem3 = solve 3 (λ x y z → (x :∨ z :∧ :⊥) :∨ (y :∧ :⊤) ⊜ x :∨ y) refl

  open import Data.Vec
  open import Data.Fin

  theorem4 : ∀ y → _ ≈ _
  theorem4 = λ y → proj₂ (constantPropagation (var (# 0) :∨ :⊥)) {y ∷ []}

  theorem5 = {!λ y → refl-elim (theorem4 y)!} 
