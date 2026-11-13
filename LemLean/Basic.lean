/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Minimal formalisation of Layered Event Modelling (Axioms A1–A6).
Source: B. Kreinz, "Layered Event Modelling: Semantic Separation as a Precondition
for Explicit Causal Analysis", Version 1.0, https://doi.org/10.5281/zenodo.23438101
Essay: https://www.barnes.ch/BP-Invisible-Coercions.html

These are the definitions printed in the essay, unchanged except for the `LEM` namespace.
-/

universe u v w

namespace LEM

/-- The five structures (LEM §4). -/
inductive StructureKind where
  | S1_Substrate      : StructureKind
  | S2_Event          : StructureKind
  | S3_Representation : StructureKind
  | S4_Epistemic      : StructureKind
  | S5_Normative      : StructureKind
  deriving DecidableEq, Repr

/-- A layer is a level within one structure (§11). -/
structure Layer where
  struct : StructureKind
  level  : Nat
  deriving DecidableEq, Repr

/-- A1 (node typing). A node of layer `l`. The layer is part of the node's type, so nodes
    of two layers differ in type even where their carriers `V l` coincide. -/
structure Node (V : Layer → Type u) (l : Layer) where
  val : V l

/-- The node set is the disjoint union over layers: every node lies in exactly one. -/
abbrev TotalNode (V : Layer → Type u) := Σ l : Layer, Node V l

/-- States and predicates are kept apart (§11). Each node carries a state in the state
    space `St l` of its own layer. -/
def LayerState (V : Layer → Type u) (St : Layer → Type v) (l : Layer) :=
  Node V l → St l

/-- A2 (predicate locality). A domain predicate ranges over the nodes of one layer. -/
def LocalPredicate (V : Layer → Type u) (l : Layer) :=
  Node V l → Prop

/-- A relational predicate takes further arguments of a declared sort `A`, as
    retrievability does: retrievable by an agent. -/
def LocalRelation (V : Layer → Type u) (l : Layer) (A : Type v) :=
  Node V l → A → Prop

/-- A3 (explicit cross-layer identity). Co-reference is a declared relation between nodes
    of different layers. It is not an edge and carries no dynamics. -/
structure CrossLayerCoRef (V : Layer → Type u) where
  rel         : TotalNode V → TotalNode V → Prop
  cross_layer : ∀ a b, rel a b → a.1 ≠ b.1

/-- The six edge types (§6). -/
inductive EdgeType where
  | causal           : EdgeType  -- brings about under intervention; alone carries Δt
  | constitutive     : EdgeType  -- synchronous realisation; nothing propagates
  | classificatory   : EdgeType  -- satisfies the criteria of a declared scheme
  | normative        : EdgeType  -- stands as fulfilment or violation of an S5 norm
  | representational : EdgeType  -- corresponds to a referent; can misrepresent
  | evidential       : EdgeType  -- an observation supports an inference (S4)
  deriving DecidableEq, Repr

/-- A4 (edge typing). Edges form a type of their own with source, target and type maps,
    so two edges of one type may join the same pair of nodes: a multigraph, not a
    relation. A5 (directional openness) is the absence of any constraint between the
    layers of `src` and `tgt`. -/
structure EventGraph (V : Layer → Type u) where
  Edge : Type w
  src  : Edge → TotalNode V
  tgt  : Edge → TotalNode V
  kind : Edge → EdgeType

/-- The causal edges. -/
def EventGraph.CausalEdge {V : Layer → Type u} (G : EventGraph V) :=
  { e : G.Edge // G.kind e = EdgeType.causal }

/-- Δt is a function on the causal edges and on nothing else (§6, §11), with values in a
    type `Dur` of durations (the non-negative reals in LEM). Asking it of any other edge
    requires a proof that the edge is causal. -/
structure CausalDuration {V : Layer → Type u} (G : EventGraph V) (Dur : Type) where
  deltaT : G.CausalEdge → Dur

/-- The three object-level elements of S5. They are kept distinct so that the type of a
    norm alone settles how an omission is evaluated: a diagnostic convention, not a claim
    of logical irreducibility. -/
inductive DeonticPrimitive where
  | right       : DeonticPrimitive
  | obligation  : DeonticPrimitive
  | prohibition : DeonticPrimitive
  deriving DecidableEq, Repr

/-- A6 (stratum separation). Dependencies and the normative meta-layer form a separate
    type-level graph. `licenses` relates it to token-level edges; how that relation is
    to be constrained is left open (§11). -/
structure TypeLevelStratum (TV : Layer → Type u) {V : Layer → Type u}
    (G : EventGraph V) where
  dependsOn : TotalNode TV → TotalNode TV → Prop
  licenses  : TotalNode TV → G.Edge → Prop

end LEM
