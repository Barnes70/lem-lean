/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Minimal formalisation of Layered Event Modelling (Axioms A1–A6).
Source: B. Kreinz, "Layered Event Modelling: Semantic Separation as a Precondition
for Explicit Causal Analysis", Draft v0.6, https://www.tlctc.net/tlctc-layered-event-modelling.html
Essay: https://www.barnes.ch/BP-Invisible-Coercions.html

These are the definitions printed in the essay, unchanged except for the `LEM` namespace.
-/

universe u v

namespace LEM

/-- The five orthogonal structures (Section 4) -/
inductive StructureKind where
  | S1_Substrate      : StructureKind
  | S2_Event          : StructureKind
  | S3_Representation : StructureKind
  | S4_Epistemic      : StructureKind
  | S5_Normative      : StructureKind
  deriving DecidableEq, Repr

/-- A Layer is uniquely identified by its StructureKind and a local level index. -/
structure Layer where
  struct : StructureKind
  level  : Nat
  deriving DecidableEq, Repr

/-- Axiom A1 (Node Typing): Every domain node belongs to exactly one Layer `l`.
    The total vertex space is the sigma type (disjoint union) `Σ l, V l`. -/
abbrev TotalNode (V : Layer → Type u) := Σ (l : Layer), V l

/-- Axiom A2 (Predicate Locality): A domain predicate is strictly local to a single Layer `l`
    and maps into a layer-specific state partition `S l`. It cannot be applied across layers. -/
def LocalPredicate (V : Layer → Type u) (S : Layer → Type v) (l : Layer) :=
  V l → S l

/-- Axiom A3 (Explicit Cross-Layer Identity): Co-reference between nodes in distinct layers
    is a static equivalence/declaration relation, not a dynamic transition edge. -/
structure CrossLayerCoRef (V : Layer → Type u) where
  rel : TotalNode V → TotalNode V → Prop

/-- Section 6: The six-type Edge Taxonomy. -/
inductive EdgeType where
  | causal           : EdgeType  -- Brings about under intervention; carries Δt ≥ 0
  | constitutive     : EdgeType  -- Synchronous realisation; no propagation
  | classificatory   : EdgeType  -- Satisfies criteria under a declared classification scheme
  | normative        : EdgeType  -- Occurrent stands as fulfilment/violation of an S5 norm under the meta-layer
  | representational : EdgeType  -- Semantic correspondence to a referent
  | evidential       : EdgeType  -- Epistemic inference from world to observer (S4)
  deriving DecidableEq, Repr

/-- Axiom A4 & A5 (Typed Edges with Directional Openness):
    Every edge carries an explicit EdgeType. Layer ordering does not restrict causal direction. -/
structure TypedEdge (V : Layer → Type u) where
  src  : TotalNode V
  dst  : TotalNode V
  kind : EdgeType

/-- Section 6 & 12: Transition duration Δt is a partial function defined ONLY for causal edges.
    In Dependent Type Theory, we enforce this at compile time via a proof witness `e.kind = .causal`. -/
structure CausalDuration (V : Layer → Type u) (NonNegReal : Type) where
  deltaT : (e : TypedEdge V) → (h : e.kind = EdgeType.causal) → NonNegReal

/-- S5 Deontic Primitives (Compliance Ontology): the triple is kept distinct so that the type of a
    norm alone settles how an omission is evaluated (P4, State Partition) — a diagnostic
    convention, not a claim of logical irreducibility. -/
inductive DeonticPrimitive where
  | right       : DeonticPrimitive
  | obligation  : DeonticPrimitive
  | prohibition : DeonticPrimitive
  deriving DecidableEq, Repr

/-- Axiom A6 (Stratum Separation): Type-level dependencies and S5 normative meta-rules
    live in a separate stratum that licenses token-level edges. -/
structure TypeLevelStratum (TypeNode : Layer → Type u) (TokenNode : Layer → Type u) where
  dependencyRel : TotalNode TypeNode → TotalNode TypeNode → Prop
  licenses      : TotalNode TypeNode → TypedEdge TokenNode → Prop

end LEM
