# Round 3 — accepted cap chain and actual-neck refinement

## Completed in this round
The two earlier finite batches returned five VERIFIED proofs. All five complete source files were read; their frozen prefixes/suffixes and captured SHA256 were checked. They were then independently recompiled into this round's private objects and their compiled targets audited again. All five passed with only propext, Classical.choice and Quot.sound. No Git integration or publication was performed.

The accepted statements are CapChartStatement, CapComplementStatement, MarkedGluingStatement, CapInteriorOpenStatement and ClosedCoverGluingStatement. Evidence: `five-source-recheck.json`, the five `*-compile.log` / `*-audit.log` pairs, and `semantic-review.json`.

`AcceptedFive.lean` binds the exact five types and actually consumes them. `checked_closedCut_connectedSum` now takes a real RegularClosedCut and produces an actual ConnectedSumPresentation without unresolved cap/gluing proof inputs. `public_after_five` has only the three major research producers remaining as explicit hypotheses. These statements passed compilation and transitive axiom checks; this does not establish those producers.

## New checked refinement
`Neck.lean` reuses the integrated sphere-side separation and positive half-collar. The coordinator proved the closure union/intersection identity directly. `closedCut_of_neck` constructs both RegularSide records and the exact RegularClosedCut from the SAME embedded collar, with identical central-sphere marking.

The two new open leaves are:
- SideInteriorAtlasStatement: identify the boundary-deleted closed side with the actual open subset and transfer its topological atlas.
- NegativeHalfCollarStatement: reflect the given collar, preserve its central slice, and produce the exact negative-side formula.

`NeckRoot.lean` composes these leaves into a finite neck certificate adapter, then into the original public TopologicalPoincareStatement. Its final theorem is `public_of_neck_frontier`. All parent checks pass with the allowed three axioms.

`CutInvariant.lean` additionally proves that the actual two capped factors inherit simple connectivity from the input, using the already bound connected-sum factor theorem rather than Poincare. This is useful for subsequent neck cuts. Its exact source/axiom results are in `CutInvariant-check.json`.

## Frozen snapshot
The new dependency graph has 28 nodes and five open frontier obligations: two ready topology leaves and three large research producers. Five previous leaves are PROVED_ISOLATED. The old V1 and earlier refinement snapshots were not edited. `frontier.lock.json` records the new source/object hashes, parent checks, task card hash and accepted proofs.

## Dispatch and boundaries
A new finite batch, `poincare-refinement-round3-20260927`, was registered via the shared lean_swarm CLI. Both tasks use exact `gpt-6-luna`, `xhigh`; compiler/verifier slots remain separate from model concurrency. The new workers are not proof-completion evidence until returned sources pass verification and semantic review. See `dispatch.json` and `final-status.json` for the most recent observation, not the pre-dispatch graph's READY label.

No automatic integration, new upstream work, force push, cache clear or full dependency rebuild occurred. Earlier worker tasks remain VERIFIED in the scheduler because local isolated acceptance is not Git integration.

Still open: actual topology-to-PL existence, compatible PL-to-smooth atlas construction, and the controlled-flow/finite-extinction/finite-event/terminal-classification producer. The new finite neck certificate is explicitly NOT a definition of Ricci flow. Its existence is not established by defining the certificate or proving an adapter.

The cap construction and new interior atlas task are TOPOLOGICAL. No claim is made that the selected cap atlas is smooth. Actual smooth-flow representatives, their homeomorphisms to these cap quotients, compatible parameters, and sufficient regularity remain required upstream.

The public 13-file V1 boundary check passed again; public smoothing and geometric_trace bindings remain absent. New checks reuse pinned dependency caches; they are not a full source rebuild of every library.
