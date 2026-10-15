/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Δt is defined only for causal edges (LEM §6, §12).

`CausalDuration.deltaT` demands a proof `e.kind = .causal`. This file states the consequence
as theorems: for every non-causal edge no such proof exists, and the total, `Option`-valued
reading of Δt is `none` exactly on the non-causal edges.
-/
import LemLean.Basic

namespace LEM

variable {V : Layer → Type u} {R : Type}

/-- Δt is defined for an edge iff a causal witness can be given. -/
def DurationDefined (e : TypedEdge V) : Prop := e.kind = EdgeType.causal

instance (e : TypedEdge V) : Decidable (DurationDefined e) :=
  inferInstanceAs (Decidable (e.kind = EdgeType.causal))

/-- No duration on a non-causal edge: the witness `deltaT` needs cannot be built. -/
theorem not_durationDefined_of_ne {e : TypedEdge V} (h : e.kind ≠ EdgeType.causal) :
    ¬ DurationDefined e := h

/-- Constitutive, classificatory and normative edges carry no Δt (the three cases §6 names). -/
theorem no_duration_constitutive {e : TypedEdge V} (h : e.kind = .constitutive) :
    ¬ DurationDefined e := by simp [DurationDefined, h]

theorem no_duration_classificatory {e : TypedEdge V} (h : e.kind = .classificatory) :
    ¬ DurationDefined e := by simp [DurationDefined, h]

theorem no_duration_normative {e : TypedEdge V} (h : e.kind = .normative) :
    ¬ DurationDefined e := by simp [DurationDefined, h]

/-- The total reading of Δt: some duration on causal edges, `none` everywhere else. -/
def CausalDuration.deltaT? (D : CausalDuration V R) (e : TypedEdge V) : Option R :=
  if h : e.kind = EdgeType.causal then some (D.deltaT e h) else none

/-- Δt is absent exactly on the non-causal edges. -/
theorem CausalDuration.deltaT?_eq_none_iff (D : CausalDuration V R) (e : TypedEdge V) :
    D.deltaT? e = none ↔ e.kind ≠ EdgeType.causal := by
  unfold CausalDuration.deltaT?
  split <;> simp_all

/-- On a causal edge the total reading agrees with `deltaT`. -/
theorem CausalDuration.deltaT?_of_causal (D : CausalDuration V R) (e : TypedEdge V)
    (h : e.kind = EdgeType.causal) : D.deltaT? e = some (D.deltaT e h) := by
  simp [CausalDuration.deltaT?, h]

end LEM
