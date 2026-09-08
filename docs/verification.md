# Verification checkpoint

The current checkout records a partial, reproducible checkpoint rather than a
terminal theorem. `PLAN.md` is authoritative for scope. The implemented
declarations compile under the exact Lean, Mathlib, AlgebraicAnalysis, and
Stafford38 pins in `formalization.yaml`; independent consumers exercise the
semantic, ordered, and finite division-coordinate scalar-pencil interfaces.
The scalar utility does not yet prove arbitrary finite-length activated
pencils or original-U simultaneous source selection.

The localization, divisor-indexed assembly and strong-P_h files are
conditional scaffold checkpoints. Their checks verify the stated consumers;
concrete full-symbol localization, actual local-test semantics, successor
construction and final cofactor extraction remain open M02–M11 obligations.
The proof map labels these nodes LEAN-SCAFFOLD.

Run the checks sequentially from the repository root:

```sh
./scripts/check-resources.sh
./scripts/verify.sh --phase-i
./scripts/verify.sh --phase-ii
./scripts/verify-palomar.sh
```

The phase-I command is meaningful for the current C01--C03/P01--P03
checkpoint, not a completed SS-all Phase I. The final-paper M01–M11
obligations and exact target are in `docs/phase-instructions.md`. The
checkpoint Phase-II and Palomar commands can audit the displayed challenge,
but they are not phase-completion or publication evidence; only
`check-release-readiness.sh` enforces the release gates. The complete
source-selection/assembly endpoints and evidence files do not yet exist.
This is intentional: a successful Lean build of a semantic contract is not
evidence for the paper's universal source producer.

The source audit permits exactly one `sorry`, in `Challenge.lean`, and forbids
project `axiom` declarations and native proof shortcuts. `Solution.lean` does
not import `Challenge.lean`; the import-closure audit checks that separation.
Endpoint axiom reports may use only `propext`, `Classical.choice`, and
`Quot.sound`. Human mathematical review and paper/Lean statement correspondence
remain independent release gates.
