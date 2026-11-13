/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Predicate locality (A2) as a statement about the total node space.

A state assignment on the whole graph that respects layers — one whose value at a node lies
in that node's own layer's state space `St x.1` — is nothing more than a family of layer
states, one per layer. The two directions below are mutually inverse, so nothing is lost by
insisting that states are declared layer by layer. The same holds for predicates: a
predicate on the total node space is a family of local predicates.

What locality adds is the other direction of use: a local predicate cannot be applied to a
node of another layer, whatever the carriers are. That needs no theorem: the term does not
type-check. See `test/Rejections.lean`.
-/
import LemLean.Basic

namespace LEM

variable {V : Layer → Type u} {St : Layer → Type v}

/-- A layer-respecting state assignment on the total node space. -/
abbrev GlobalState (V : Layer → Type u) (St : Layer → Type v) :=
  (x : TotalNode V) → St x.1

/-- Assemble a family of layer states into one assignment on the total space. -/
def GlobalState.ofLocal (σ : (l : Layer) → LayerState V St l) : GlobalState V St :=
  fun x => σ x.1 x.2

/-- Restrict a layer-respecting assignment to one layer. -/
def GlobalState.toLocal (G : GlobalState V St) (l : Layer) : LayerState V St l :=
  fun v => G ⟨l, v⟩

theorem GlobalState.toLocal_ofLocal (σ : (l : Layer) → LayerState V St l) :
    GlobalState.toLocal (GlobalState.ofLocal σ) = σ := rfl

theorem GlobalState.ofLocal_toLocal (G : GlobalState V St) :
    GlobalState.ofLocal (GlobalState.toLocal G) = G := rfl

/-- A predicate on the total node space. -/
abbrev GlobalPredicate (V : Layer → Type u) := TotalNode V → Prop

/-- Assemble a family of local predicates into one predicate on the total space. -/
def GlobalPredicate.ofLocal (P : (l : Layer) → LocalPredicate V l) : GlobalPredicate V :=
  fun x => P x.1 x.2

/-- Restrict a predicate on the total space to one layer. -/
def GlobalPredicate.toLocal (G : GlobalPredicate V) (l : Layer) : LocalPredicate V l :=
  fun v => G ⟨l, v⟩

theorem GlobalPredicate.toLocal_ofLocal (P : (l : Layer) → LocalPredicate V l) :
    GlobalPredicate.toLocal (GlobalPredicate.ofLocal P) = P := rfl

theorem GlobalPredicate.ofLocal_toLocal (G : GlobalPredicate V) :
    GlobalPredicate.ofLocal (GlobalPredicate.toLocal G) = G := rfl

end LEM
