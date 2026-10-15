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
  V lDRE
but is expected to have type
  V lSRE
in the application
  Compromised d
-/
#guard_msgs in
example (V : Layer → Type) (S : Layer → Type)
    (Compromised : LocalPredicate V S lSRE) (d : V lDRE) : S lSRE := Compromised d

-- Claim 2 (§6): Δt cannot be asked of a normative edge — no causal witness exists.
/--
error: Tactic `decide` proved that the proposition
  EdgeType.normative = EdgeType.causal
is false
-/
#guard_msgs in
example (V : Layer → Type) (D : CausalDuration V Nat) (e : TypedEdge V)
    (h : e.kind = .normative) : Nat := D.deltaT e (by rw [h]; decide)
