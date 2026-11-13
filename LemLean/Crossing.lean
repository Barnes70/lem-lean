/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Typed crossings: a relation between two structures along which claims are carried, with a
declared kind and with what it carries stated as propositions that have to be proved.

`Basic.lean` labels an edge with its type and nothing more. This file adds the second
component: preservation and reflection of predicates, invariance of relations, and the
carrying of an operation under a side condition.

Two worked crossings show why the two components are kept apart. The cast `Nat → Int` and
the reading `BitVec 64 → Nat` have the same structure: each is an injective map that
carries an operation only as far as a side condition allows. Their declared kinds differ:
the first extends its source, the second represents a referent and can misrepresent it.
-/
import LemLean.Basic

namespace LEM

/-- A crossing between `A` and `B` with a declared kind of type `K`. The kind is data:
    nothing in `rel` determines it. `K` can be `EdgeType` or `CrossingRole`. -/
structure Crossing (K : Type) (A : Type) (B : Type) where
  kind : K
  rel  : A → B → Prop

namespace Crossing

variable {K A B : Type} (c : Crossing K A B)

/-- `c` preserves a predicate: what holds at the source holds at the target. -/
def Preserves (PA : A → Prop) (PB : B → Prop) : Prop :=
  ∀ a b, c.rel a b → PA a → PB b

/-- `c` reflects a predicate: what holds at the target holds at the source. -/
def Reflects (PA : A → Prop) (PB : B → Prop) : Prop :=
  ∀ a b, c.rel a b → PB b → PA a

/-- A predicate is invariant under `c`: preserved and reflected. -/
def Invariant (PA : A → Prop) (PB : B → Prop) : Prop :=
  c.Preserves PA PB ∧ c.Reflects PA PB

theorem invariant_iff (PA : A → Prop) (PB : B → Prop) :
    c.Invariant PA PB ↔ ∀ a b, c.rel a b → (PA a ↔ PB b) :=
  ⟨fun h a b r => ⟨h.1 a b r, h.2 a b r⟩,
   fun h => ⟨fun a b r => (h a b r).mp, fun a b r => (h a b r).mpr⟩⟩

/-- Reuse of a claim at the target. It takes the preservation proof as an argument:
    without one, the claim established at the source says nothing about the target. -/
theorem transport {PA : A → Prop} {PB : B → Prop} (h : c.Preserves PA PB)
    {a : A} {b : B} (r : c.rel a b) (ha : PA a) : PB b :=
  h a b r ha

/-- A binary relation is invariant under `c`. -/
def InvariantRel (rA : A → A → Prop) (rB : B → B → Prop) : Prop :=
  ∀ a₁ a₂ b₁ b₂, c.rel a₁ b₁ → c.rel a₂ b₂ → (rA a₁ a₂ ↔ rB b₁ b₂)

/-- A binary operation is carried by `c` wherever the side condition holds. -/
def CarriesOp (opA : A → A → A) (opB : B → B → B) (side : A → A → Prop) : Prop :=
  ∀ a₁ a₂ b₁ b₂, c.rel a₁ b₁ → c.rel a₂ b₂ → side a₁ a₂ → c.rel (opA a₁ a₂) (opB b₁ b₂)

/-- The kind is declared, not derived: one relation can be given any two kinds. This holds
    by construction, because `kind` is a field that `rel` does not constrain. -/
theorem kind_not_determined (r : A → B → Prop) (k₁ k₂ : K) (h : k₁ ≠ k₂) :
    ∃ c₁ c₂ : Crossing K A B, c₁.rel = r ∧ c₂.rel = r ∧ c₁.kind ≠ c₂.kind :=
  ⟨⟨k₁, r⟩, ⟨k₂, r⟩, rfl, rfl, h⟩

end Crossing

/-- Three roles of a map between types. The list is not claimed to be complete, and the
    roles are not exclusive classes of maps. -/
inductive CrossingRole where
  | extension      : CrossingRole  -- the target adds to the source
  | identification : CrossingRole  -- the target is defined by a relation on the source
  | representation : CrossingRole  -- the source answers to a referent in the target
  deriving DecidableEq, Repr

/-! ### The cast `Nat → Int`, declared an extension -/

/-- The cast from the natural numbers to the integers. -/
def natToInt : Crossing CrossingRole Nat Int where
  kind := .extension
  rel  := fun n z => (n : Int) = z

/-- Addition is carried unconditionally. -/
theorem natToInt_carries_add :
    natToInt.CarriesOp (· + ·) (· + ·) (fun _ _ => True) := by
  intro a₁ a₂ b₁ b₂ h₁ h₂ _
  have e₁ : (a₁ : Int) = b₁ := h₁
  have e₂ : (a₂ : Int) = b₂ := h₂
  show ((a₁ + a₂ : Nat) : Int) = b₁ + b₂
  rw [← e₁, ← e₂]
  exact Int.natCast_add a₁ a₂

/-- Subtraction is carried under the side condition `a₂ ≤ a₁`. -/
theorem natToInt_carries_sub :
    natToInt.CarriesOp (· - ·) (· - ·) (fun a₁ a₂ => a₂ ≤ a₁) := by
  intro a₁ a₂ b₁ b₂ h₁ h₂ hside
  have e₁ : (a₁ : Int) = b₁ := h₁
  have e₂ : (a₂ : Int) = b₂ := h₂
  show ((a₁ - a₂ : Nat) : Int) = b₁ - b₂
  rw [← e₁, ← e₂]
  exact Int.ofNat_sub hside

/-- Without the side condition it is not: `2 - 3` is `0` in `Nat` and `-1` in `Int`. -/
theorem natToInt_sub_needs_side :
    ¬ natToInt.CarriesOp (· - ·) (· - ·) (fun _ _ => True) := by
  intro h
  have e : ((2 - 3 : Nat) : Int) = (2 : Int) - 3 := h 2 3 2 3 rfl rfl trivial
  exact absurd e (by decide)

/-- The order is invariant: a relation between casts is a relation between the originals. -/
theorem natToInt_le_invariant : natToInt.InvariantRel (· ≤ ·) (· ≤ ·) := by
  intro a₁ a₂ b₁ b₂ h₁ h₂
  have e₁ : (a₁ : Int) = b₁ := h₁
  have e₂ : (a₂ : Int) = b₂ := h₂
  show a₁ ≤ a₂ ↔ b₁ ≤ b₂
  rw [← e₁, ← e₂]
  exact Int.ofNat_le.symm

/-- The cast is injective. -/
theorem natToInt_injective (a₁ a₂ : Nat) (b : Int)
    (h₁ : natToInt.rel a₁ b) (h₂ : natToInt.rel a₂ b) : a₁ = a₂ := by
  have e₁ : (a₁ : Int) = b := h₁
  have e₂ : (a₂ : Int) = b := h₂
  exact Int.ofNat.inj (e₁.trans e₂.symm)

/-! ### The reading `BitVec 64 → Nat`, declared a representation -/

/-- A 64-bit vector read as the number it stands for. -/
def bitVecToNat : Crossing CrossingRole (BitVec 64) Nat where
  kind := .representation
  rel  := fun x n => x.toNat = n

/-- Addition is carried while nothing overflows. -/
theorem bitVecToNat_carries_add :
    bitVecToNat.CarriesOp (· + ·) (· + ·) (fun x y => x.toNat + y.toNat < 2 ^ 64) := by
  intro x y n m hx hy hside
  have ex : x.toNat = n := hx
  have ey : y.toNat = m := hy
  show (x + y).toNat = n + m
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt hside, ex, ey]

/-- Without the side condition it is not: the sum of two representations then represents
    something other than the sum. -/
theorem bitVecToNat_add_needs_side :
    ¬ bitVecToNat.CarriesOp (· + ·) (· + ·) (fun _ _ => True) := by
  intro h
  have e : (BitVec.allOnes 64 + 1#64).toNat = (BitVec.allOnes 64).toNat + (1#64).toNat :=
    h _ _ _ _ rfl rfl trivial
  exact absurd e (by decide)

/-- The reading is injective. -/
theorem bitVecToNat_injective (x y : BitVec 64) (n : Nat)
    (hx : bitVecToNat.rel x n) (hy : bitVecToNat.rel y n) : x = y := by
  have ex : x.toNat = n := hx
  have ey : y.toNat = n := hy
  exact BitVec.eq_of_toNat_eq (ex.trans ey.symm)

/-- Same structure, different declared kind. -/
theorem natToInt_kind_ne_bitVecToNat_kind : natToInt.kind ≠ bitVecToNat.kind := by
  decide

end LEM
