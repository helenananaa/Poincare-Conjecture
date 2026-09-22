# Proof boundary V1 — scope and operating rules

## What is frozen

The exact public target is `ProofContract.V1.TopologicalPoincareStatement`:
nonempty, compact, connected, Hausdorff, second-countable topological 3-manifolds
without boundary, with simple connectivity, are homeomorphic to the actual unit
sphere in Euclidean four-space. A Lean theorem in `TargetAudit.lean` proves
that the bundled statement is equivalent to the usual unbundled statement.

`SmoothPoincareStatement` separately records the blueprint's diffeomorphism
endpoint. It is NOT silently identified with the public topological assertion.
`SmoothingStatement` asks for a smooth atlas on the original topological space;
the assembly preserves the topology, not the arbitrary original atlas.

V1 freezes the outer target, supporting definitions, six obligation types,
and the already checked recursive assembly. Definitions are included in the
hash boundary, not merely printed theorem signatures. Nine existing external
git dependencies and the Lean toolchain are pinned. Additional proof modules
can be added without changing these files.

## Actual typed reduction

The geometric producer must construct `FiniteExtinctionTrace [M]`. Its only
constructors are a finite list ending at the empty list, with exact operations:
remove a genuinely sphere-covered component, remove an actual S² × S¹ component,
or replace a component by the two factors of a concrete connected-sum quotient.
A connected-sum presentation uses coordinate balls with a larger neighborhood,
their actual punctured complements, a homeomorphism of the boundary spheres,
and a homeomorphism to the quotient by those seam identifications.

There is no field asserting that the initial manifold is a sphere. There is no
axiom asserting the existence of this trace. The trace is not renamed or used
as the definition of a Ricci flow. The producer remains a substantial open goal.

The checked assembly reconstructs a finite standard-factor expression by
induction over the trace. A second induction consumes sphere-cover recognition,
handle exclusion, simply-connectedness of connected-sum factors, and the
connected-sum sphere identity. Smoothing connects the smooth topological output
to the exact public root. All six input propositions are explicit parameters of
`topological_of_contracts`; no unconditional Poincare theorem is exported.

## Current mathematical frontier

| Frozen goal | State |
|---|---|
| `SmoothingStatement` | Open |
| `GeometricTraceStatement` | Open |
| `SphereCoverRecognitionStatement` | Proved by unique covering lifts; exact binding checked |
| `HandleExclusionStatement` | Open |
| `ConnectedSumFactorsStatement` | Open |
| `ConnectedSumSphereStatement` | Open |

These are interface counts, not percentages of the mathematical workload.
In particular the geometric producer contains much of the remaining project.
The geometry branch still needs normalization, a controlled surgery flow,
finite extinction and event control, and a proof that the actual surgery history
produces the specified topological rewrites. Those deeper definitions and their
complete recursive task decomposition are NOT claimed to be frozen.

This boundary lets those internal representations evolve without rewriting the
outer proof, PROVIDED a checked adapter still returns the same V1 trace type.
There is no guarantee that every research subgoal is already correctly chosen
or that future work is free of local refactoring.

## Frozen files and version changes

`v1.lock.json` contains the approved file hashes. A trusted earlier git revision
is compared with the candidate manifest as well as the candidate files. Editing
a definition AND updating its manifest hash is rejected. The root import cannot
be removed or replaced by a comment/string decoy. The graph is checked for
cycles, missing nodes, duplicate nodes and nodes disconnected from the root.

V1 is append-only at the version level: do not edit the frozen files or rehash
them to fix a failing task. Add implementation modules outside `V1/`. To change
an interface, retain V1, create a reviewed new version, and prove an adapter
back to the V1 target. Changes to a mistaken original mathematical specification
must be reviewed as such, not hidden behind a new version label.

`v1.bindings.json` records module and declaration names, never `done` booleans.
A binding is accepted only after Lean verifies it has the EXACT frozen Prop,
with no extra proof assumptions, and its transitive axioms are a subset of
`propext`, `Classical.choice`, `Quot.sound`. A conditional assembly theorem
cannot be substituted for a proof of an open leaf.

## Commands

From the repository root, with the pinned `lake` on PATH:

```bash
python3 tools/proof_contract/check.py
python3 -m unittest discover -s tools/proof_contract -p 'test_*.py' -v
python3 tools/proof_contract/check.py --lean --report reports/proof-contract-current.json
python3 tools/proof_contract/check.py --lean --require-complete
```

The last command MUST fail while obligations are unresolved. A green boundary
check or green CI run is not a completed proof. When all bindings exist, the
checker constructs and kernel-checks the exact root from those bindings.

For comparison with an earlier trusted commit:

```bash
python3 tools/proof_contract/check.py --base <trusted-commit>
python3 tools/proof_contract/check.py --base <trusted-commit> --ref INDEX
```

`--bootstrap` is only for first adoption before the version exists in git.
`--baseline-file` can check against an externally preserved lock. Neither is a
routine way to accept a modified V1. The staged-content pre-commit hook uses
the previous committed checker. The CI workflow similarly loads the checker
from the trusted base before running the current source/leaf audit.

## Validation scope and limitations

This work uses focused source builds and the existing pinned dependency cache.
It neither clears caches nor rebuilds all reference packages. The checker uses
the shared compiler/verifier resource limits; it does not start model workers.
The source includes a real standard-sphere instance and a real one-step trace,
plus an unbundled-target equivalence test. Axiom audits are on compiled theorem
terms, not textual counts of proof holes.

The hooks and CI are engineering change control, not protection against an
administrator disabling hooks or altering repository settings. The workflow
file alone does not configure GitHub branch-protection requirements. No remote
settings, upstream pull requests, or original blueprint completion markers are
changed by this work.
