/-
Copyright (c) 2026 Bernhard Kreinz. Released under the Apache 2.0 license.
Authors: Bernhard Kreinz

Reasoning traces: what verifying a trace certifies, and what it cannot.

A model's mechanism (S2: the causal chain of computation that runs) produces a written trace
(S3: a chain of thought, or a proof script). Three different edges are involved, and LEM
types them differently:

* `produce`  — causal: the mechanism brings the trace about.
* `faithful` — representational: the trace stands in correspondence to a mechanism. Failure
               is misrepresentation (an unfaithful chain of thought).
* `valid`    — classificatory: the trace satisfies the rules of a declared scheme. A proof
               kernel such as Lean's checks exactly this edge.

The results below show that the classificatory edge is blind to the mechanism, and that
wherever two mechanisms write the same trace, no judgement made on the trace alone can detect
whether the representational edge holds.
This is the formal core of LEM §11 (evaluation inside S3 does not identify the transition
structure that produced the output).
-/
import LemLean.Basic

namespace LEM

/-- A reasoning system: mechanisms, the traces they produce, and two judgements on traces. -/
structure ReasoningSystem where
  Mech     : Type
  Trace    : Type
  produce  : Mech → Trace           -- causal edge (S2 → S3)
  valid    : Trace → Prop           -- classificatory edge (trace satisfies the rules)
  faithful : Trace → Mech → Prop    -- representational edge (trace describes this mechanism)

namespace ReasoningSystem

variable (R : ReasoningSystem)

/-- A trace describes at most one mechanism: it says *how* the result was reached. -/
def FaithfulFunctional : Prop :=
  ∀ t m₁ m₂, R.faithful t m₁ → R.faithful t m₂ → m₁ = m₂

/-- Validity cannot tell apart two mechanisms that produce the same trace. -/
theorem valid_blind_to_mechanism {m₁ m₂ : R.Mech} (h : R.produce m₁ = R.produce m₂) :
    R.valid (R.produce m₁) ↔ R.valid (R.produce m₂) := by
  rw [h]

/-- If two different mechanisms produce the same trace, the trace cannot faithfully describe
    both — however valid it is. -/
theorem not_both_faithful (hf : R.FaithfulFunctional)
    {m₁ m₂ : R.Mech} (hne : m₁ ≠ m₂) (h : R.produce m₁ = R.produce m₂) :
    ¬ (R.faithful (R.produce m₁) m₁ ∧ R.faithful (R.produce m₂) m₂) := by
  intro ⟨h₁, h₂⟩
  rw [← h] at h₂
  exact hne (hf _ _ _ h₁ h₂)

/-- No judgement on traces alone detects faithfulness. Whatever `D` looks at — validity, a
    reward model, a comparison with a reference answer — if it only sees the trace, it cannot
    agree with faithfulness on two mechanisms that share a trace when one of them is
    faithfully described. -/
theorem no_trace_only_faithfulness_test (hf : R.FaithfulFunctional)
    {m₁ m₂ : R.Mech} (hne : m₁ ≠ m₂) (h : R.produce m₁ = R.produce m₂)
    (hfaith : R.faithful (R.produce m₁) m₁) :
    ¬ ∃ D : R.Trace → Prop, ∀ m, D (R.produce m) ↔ R.faithful (R.produce m) m := by
  intro ⟨D, hD⟩
  have d₁ : D (R.produce m₁) := (hD m₁).mpr hfaith
  have d₂ : D (R.produce m₂) := by rw [← h]; exact d₁
  have f₂ : R.faithful (R.produce m₂) m₂ := (hD m₂).mp d₂
  rw [← h] at f₂
  exact hne (hf _ _ _ hfaith f₂)

end ReasoningSystem

/-! ### The hypotheses are satisfiable: a two-mechanism witness

One valid trace, two ways of producing it: by following the rules the trace states, or by
using a hint the trace never mentions. The trace describes only the first. -/

/-- How the answer was actually reached. -/
inductive Route where
  | byRules : Route
  | byHint  : Route
  deriving DecidableEq, Repr

/-- The example system: both routes write the same, valid trace. -/
def hintExample : ReasoningSystem where
  Mech     := Route
  Trace    := Unit
  produce  := fun _ => ()
  valid    := fun _ => True
  faithful := fun _ m => m = .byRules

theorem hintExample_functional : hintExample.FaithfulFunctional := by
  intro _ m₁ m₂ h₁ h₂
  exact h₁.trans h₂.symm

/-- In the example the trace is valid, yet the hint route is misrepresented by it. -/
theorem hintExample_valid_but_unfaithful :
    hintExample.valid (hintExample.produce Route.byHint) ∧
    ¬ hintExample.faithful (hintExample.produce Route.byHint) Route.byHint := by
  refine ⟨trivial, ?_⟩
  show ¬ (Route.byHint = Route.byRules)
  intro h
  cases h

/-- And no trace-only test can detect it. -/
theorem hintExample_no_test :
    ¬ ∃ D : hintExample.Trace → Prop,
      ∀ m, D (hintExample.produce m) ↔ hintExample.faithful (hintExample.produce m) m :=
  hintExample.no_trace_only_faithfulness_test hintExample_functional
    (m₁ := Route.byRules) (m₂ := Route.byHint) (show Route.byRules ≠ Route.byHint by decide) rfl rfl

end LEM
