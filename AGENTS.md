# OEIS proof repository instructions

- Follow `ADDING_A_PROOF.md` for publication and verification.
- Attribute standalone Lean files to Wentao Li. For reused Formal Conjectures
  statements, retain The Formal Conjectures Authors; Wentao Li may be added for
  the new contribution. Do not use AI4Math Lab or another workspace/tool label
  as an author or copyright holder. Preserve required third-party notices and
  mathematical citations.
- Keep exactly one canonical Lean file and one proof/source pair per sequence.
  Do not add compatibility copies, redirects, or separate copies for disproofs.
- Distinguish contribution category (New Proofs, New Formalizations, or
  Independent Formalizations) from outcome (Proved, Disproved, or Negative answer).
  Preserve exact claim scope.
- A disproof proves the negation of the original statement. Document that
  original statement without importing or asserting it as an admitted theorem;
  give a verified counterexample certificate when available.
- Preserve existing release tags and pinned links. Keep verification dates,
  source hashes, compiler results, and attribution accurate.
- Reserve NewFormalization for known mathematics with no earlier matching public
  Lean proof located in a dated search. Use IndependentFormalization when a public
  Lean proof already covers the assigned claim. For mixed coverage, identify the
  exact new clauses or bridges; existing supporting Lean results are not new work.
