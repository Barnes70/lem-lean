/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Δt is defined only for causal edges (LEM §6, §11).

`CausalDuration.deltaT` is a function on the causal edges of a graph. This file states the
consequence as theorems: a non-causal edge is not in its domain, the total, `Option`-valued
reading of Δt is `none` exactly on the non-causal edges, and — because edges are a type of
their own — two parallel causal edges between the same nodes may carry different durations.
-/
import LemLean.Basic

namespace LEM

variable {V : Layer → Type u} {R : Type}

/-- Δt is defined for an edge iff the edge is causal. -/
def DurationDefined (G : EventGraph V) (e : G.Edge) : Prop := G.kind e = EdgeType.causal

instance (G : EventGraph V) (e : G.Edge) : Decidable (DurationDefined G e) :=
  inferInstanceAs (Decidable (G.kind e = EdgeType.causal))

/-- No duration on a non-causal edge: it is not an element of `G.CausalEdge`. -/
theorem not_durationDefined_of_ne {G : EventGraph V} {e : G.Edge}
    (h : G.kind e ≠ EdgeType.causal) : ¬ DurationDefined G e := h

/-- Constitutive, classificatory and normative edges carry no Δt (the three cases §6 names). -/
theorem no_duration_constitutive {G : EventGraph V} {e : G.Edge}
    (h : G.kind e = .constitutive) : ¬ DurationDefined G e := by simp [DurationDefined, h]

theorem no_duration_classificatory {G : EventGraph V} {e : G.Edge}
    (h : G.kind e = .classificatory) : ¬ DurationDefined G e := by simp [DurationDefined, h]

theorem no_duration_normative {G : EventGraph V} {e : G.Edge}
    (h : G.kind e = .normative) : ¬ DurationDefined G e := by simp [DurationDefined, h]

/-- The total reading of Δt: some duration on causal edges, `none` everywhere else. -/
def CausalDuration.deltaT? {G : EventGraph V} (D : CausalDuration G R) (e : G.Edge) : Option R :=
  if h : G.kind e = EdgeType.causal then some (D.deltaT ⟨e, h⟩) else none

/-- Δt is absent exactly on the non-causal edges. -/
theorem CausalDuration.deltaT?_eq_none_iff {G : EventGraph V} (D : CausalDuration G R)
    (e : G.Edge) : D.deltaT? e = none ↔ G.kind e ≠ EdgeType.causal := by
  unfold CausalDuration.deltaT?
  split <;> simp_all

/-- On a causal edge the total reading agrees with `deltaT`. -/
theorem CausalDuration.deltaT?_of_causal {G : EventGraph V} (D : CausalDuration G R)
    (e : G.Edge) (h : G.kind e = EdgeType.causal) : D.deltaT? e = some (D.deltaT ⟨e, h⟩) := by
  simp [CausalDuration.deltaT?, h]

/-- The graph is a multigraph: between any two nodes there can be two distinct causal edges
    with different durations. Duration belongs to the edge, not to the pair of nodes. -/
theorem parallel_edges_may_differ (a b : TotalNode V) :
    ∃ (G : EventGraph.{u, 0} V) (D : CausalDuration G Nat) (e₁ e₂ : G.CausalEdge),
      G.src e₁.1 = a ∧ G.src e₂.1 = a ∧ G.tgt e₁.1 = b ∧ G.tgt e₂.1 = b ∧
      D.deltaT e₁ ≠ D.deltaT e₂ :=
  ⟨⟨Bool, fun _ => a, fun _ => b, fun _ => .causal⟩,
   ⟨fun e => if e.1 then 1 else 2⟩,
   ⟨true, rfl⟩, ⟨false, rfl⟩, rfl, rfl, rfl, rfl,
   fun h => absurd h (by decide : (1 : Nat) ≠ 2)⟩

end LEM
