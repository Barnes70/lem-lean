/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

P4 (state-partition test) applied to S5: what does an omission mean?

With three norm types — right, obligation, prohibition — the type of a norm alone settles the
standing of an idle step. With two types, where a prohibition is encoded as an obligation to
omit (`Forbid φ ≡ Oblige ¬φ`), it does not: two norms of the same type give the identical
`skip` opposite standings, and only their content tells them apart.

This is the diagnostic reason LEM v0.6 keeps prohibition distinct. It is not a claim of logical
irreducibility: the two-type encoding loses no expressive power (`toNorm2_preserves_omission`),
only this property.
-/
import LemLean.Basic

namespace LEM

/-- The standing an idle step (`skip`) has under a norm. Under a right, doing nothing is
    neither fulfilment nor violation: the right is simply not exercised. -/
inductive OmissionStanding where
  | fulfilment  : OmissionStanding
  | violation   : OmissionStanding
  | noStanding  : OmissionStanding
  deriving DecidableEq, Repr

variable {A : Type}  -- the acts norms are about

/-! ### Three types -/

/-- A norm with one of the three deontic types about an act. -/
structure Norm3 (A : Type) where
  kind : DeonticPrimitive
  act  : A

/-- How `skip` stands under a three-type norm. Read off the type alone. -/
def Norm3.omission (n : Norm3 A) : OmissionStanding :=
  match n.kind with
  | .right       => .noStanding
  | .obligation  => .violation
  | .prohibition => .fulfilment

/-- P4 holds: the standing of an omission is a function of the norm's type alone. -/
theorem three_types_settle_omission :
    ∃ f : DeonticPrimitive → OmissionStanding, ∀ n : Norm3 A, n.omission = f n.kind :=
  ⟨fun k => match k with
    | .right => .noStanding | .obligation => .violation | .prohibition => .fulfilment,
   fun _ => rfl⟩

/-! ### Two types: prohibition as obligation to omit -/

/-- The economised vocabulary: only permission and obligation. -/
inductive DeonticPair where
  | permission : DeonticPair
  | obligation : DeonticPair
  deriving DecidableEq, Repr

/-- Whether a two-type norm is about doing the act or refraining from it. -/
inductive Polarity where
  | perform : Polarity
  | refrain : Polarity
  deriving DecidableEq, Repr

structure Norm2 (A : Type) where
  kind     : DeonticPair
  act      : A
  polarity : Polarity

/-- How `skip` stands under a two-type norm. Under an obligation the content decides:
    `Oblige(φ)` is violated by `skip`, `Oblige(¬φ)` (the encoded prohibition) is fulfilled. -/
def Norm2.omission (n : Norm2 A) : OmissionStanding :=
  match n.kind, n.polarity with
  | .permission, _        => .noStanding
  | .obligation, .perform => .violation
  | .obligation, .refrain => .fulfilment

/-- The identical `skip` gets opposite standings under two norms of the same type. -/
theorem two_types_same_kind_opposite_standing (a : A) :
    ∃ n m : Norm2 A, n.kind = m.kind ∧ n.omission = .violation ∧ m.omission = .fulfilment :=
  ⟨⟨.obligation, a, .perform⟩, ⟨.obligation, a, .refrain⟩, rfl, rfl, rfl⟩

/-- P4 fails: as soon as there is any act at all, no function of the type alone gives the
    standing of an omission. -/
theorem two_types_do_not_settle_omission (a : A) :
    ¬ ∃ f : DeonticPair → OmissionStanding, ∀ n : Norm2 A, n.omission = f n.kind := by
  intro ⟨f, hf⟩
  have h1 := hf ⟨.obligation, a, .perform⟩
  have h2 := hf ⟨.obligation, a, .refrain⟩
  simp only [Norm2.omission] at h1 h2
  rw [← h1] at h2
  cases h2

/-- The standard reduction `Forbid φ ≡ Oblige ¬φ`. -/
def Norm3.toNorm2 (n : Norm3 A) : Norm2 A :=
  match n.kind with
  | .right       => ⟨.permission, n.act, .perform⟩
  | .obligation  => ⟨.obligation, n.act, .perform⟩
  | .prohibition => ⟨.obligation, n.act, .refrain⟩

/-- The reduction loses nothing in what it says about `skip`. -/
theorem toNorm2_preserves_omission (n : Norm3 A) : n.toNorm2.omission = n.omission := by
  cases n with
  | mk kind act => cases kind <;> rfl

end LEM
