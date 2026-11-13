/-
Negative tests: each `#guard_msgs` block asserts that Lean REJECTS the term with exactly the
recorded error. These are the essay's two "the type-checker enforces" claims.
Run: lake env lean test/Rejections.lean
-/
import LemLean

open LEM

def lSRE : Layer := ⟨.S2_Event, 1⟩
def lDRE : Layer := ⟨.S2_Event, 2⟩

-- Claim 1 (A2): an SRE-local predicate cannot be applied to a DRE node.
/--
error: Application type mismatch: The argument
  d
has type
  Node V lDRE
but is expected to have type
  Node V lSRE
in the application
  Compromised d
-/
#guard_msgs in
example (V : Layer → Type) (Compromised : LocalPredicate V lSRE) (d : Node V lDRE) : Prop :=
  Compromised d

-- The same holds where both layers have the same carrier: the layer is in the node's type.
def Vconst : Layer → Type := fun _ => Nat

/--
error: Application type mismatch: The argument
  d
has type
  Node Vconst lDRE
but is expected to have type
  Node Vconst lSRE
in the application
  Compromised d
-/
#guard_msgs in
example (Compromised : LocalPredicate Vconst lSRE) (d : Node Vconst lDRE) : Prop :=
  Compromised d

-- Claim 2 (§6): Δt cannot be asked of a normative edge — it is not a causal edge.
/--
error: Tactic `decide` proved that the proposition
  EdgeType.normative = EdgeType.causal
is false
-/
#guard_msgs in
example (V : Layer → Type) (G : EventGraph V) (D : CausalDuration G Nat) (e : G.Edge)
    (h : G.kind e = .normative) : Nat := D.deltaT ⟨e, by rw [h]; decide⟩
