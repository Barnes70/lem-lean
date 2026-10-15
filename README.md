# lem-lean

Layered Event Modelling (LEM) in Lean 4: the definitions behind the essay
[*Invisible Coercions and Untyped Refinement*](https://www.barnes.ch/BP-Invisible-Coercions.html),
with machine-checked theorems about them.

LEM is described in B. Kreinz, *Layered Event Modelling: Semantic Separation as a Precondition
for Explicit Causal Analysis*, Draft v0.6 —
<https://www.tlctc.net/tlctc-layered-event-modelling.html>.

## What is in it

| File | Content |
|---|---|
| `LemLean/Basic.lean` | Axioms A1–A6 as types: layers, the total node space, local predicates, the six edge types, typed edges, causal duration, the three deontic primitives, the type-level stratum. Identical to the essay's code block (plus a namespace). |
| `LemLean/Duration.lean` | Δt only on causal edges (§6, §12): no duration for constitutive, classificatory or normative edges; the total reading `deltaT?` is `none` exactly on non-causal edges. |
| `LemLean/Locality.lean` | Predicate locality (A2): a layer-respecting predicate on the whole graph is the same thing as a family of local predicates (round trip both ways). |
| `LemLean/Deontic.lean` | P4 on S5: with three norm types the type alone settles what an omission means; with two (`Forbid φ ≡ Oblige ¬φ`) it does not — while the reduction loses no expressive power. |
| `LemLean/Trace.lean` | Reasoning traces (§11): a mechanism (S2) causally produces a trace (S3); validity is classificatory, faithfulness representational. Validity is blind to the mechanism; two mechanisms sharing a trace cannot both be faithfully described; no judgement on the trace alone can detect faithfulness. A two-route witness (rules vs. unmentioned hint) shows the hypotheses are satisfiable. |
| `test/Rejections.lean` | Negative tests: terms Lean must reject (an SRE predicate applied to a DRE node; Δt asked of a normative edge). |

No `sorry` and no Mathlib dependency. `#print axioms` shows at most `propext` (one of Lean's three standard axioms); the deontic and locality results use no axioms at all.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```sh
lake build
lake env lean test/Rejections.lean
```

## Status

Version 0.2.0, a formal companion to LEM Draft v0.6. Definitions follow the paper; when
the paper changes, this package follows it.

## License

Apache License 2.0 — see `LICENSE`. Copyright (c) 2026 Bernhard Kreinz.
