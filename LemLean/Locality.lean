/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Predicate locality (A2) as a statement about the total node space.

A predicate on the whole graph that respects layers — one whose value at a node lies in that
node's own layer's state space `S x.1` — is nothing more than a family of local predicates,
one per layer. The two directions below are mutually inverse, so nothing is lost by insisting
that every domain predicate is declared layer by layer.

(That a local predicate cannot be applied to a node of another layer needs no theorem: the
term does not type-check. See `test/Rejections.lean`.)
-/
import LemLean.Basic

namespace LEM

variable {V : Layer → Type u} {S : Layer → Type v}

/-- A layer-respecting predicate on the total node space. -/
abbrev GlobalPredicate (V : Layer → Type u) (S : Layer → Type v) :=
  (x : TotalNode V) → S x.1

/-- Assemble a family of local predicates into one predicate on the total space. -/
def GlobalPredicate.ofLocal (P : (l : Layer) → LocalPredicate V S l) : GlobalPredicate V S :=
  fun x => P x.1 x.2

/-- Restrict a layer-respecting predicate to one layer. -/
def GlobalPredicate.toLocal (G : GlobalPredicate V S) (l : Layer) : LocalPredicate V S l :=
  fun v => G ⟨l, v⟩

theorem GlobalPredicate.toLocal_ofLocal (P : (l : Layer) → LocalPredicate V S l) :
    GlobalPredicate.toLocal (GlobalPredicate.ofLocal P) = P := rfl

theorem GlobalPredicate.ofLocal_toLocal (G : GlobalPredicate V S) :
    GlobalPredicate.ofLocal (GlobalPredicate.toLocal G) = G := rfl

end LEM
