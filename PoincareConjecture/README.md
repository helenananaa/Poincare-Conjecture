# Poincare-Conjecture

This is the repository's primary formalization project. Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../formalized-sources/` remain faithful reference
formalizations of books and articles. Results from those projects may inform
or support this development, but they do not define its organization.

## Status

The evolving six-chapter, seven-stage Morgan--Tian Blueprint currently contains 279
mathematical declarations and 854 direct prerequisite edges. The live structural
audit reports one terminal sink (`thm:poincare-conjecture`), all 279 declarations
reach it, and no cycles, forward edges, duplicate edges, unresolved references,
or isolated declarations. Counts are descriptive consequences of the current
mathematical decomposition; historical snapshots and generated audit dossiers
are not the deliverable for this task. The shared hgraph retains stale
historical Poincare records from superseded source revisions; they are excluded
from the active graph and are not live prerequisites.

The route is now a mathematically closed, source-backed candidate Blueprint
pending human expert review. Source comparison repaired the surgery spacetime
and cutoff domain, canonical-neighborhood continuation, the corrected Appendix
A.19/A.20/A.21/A.24 topology interfaces, explicit relative fiber and cap
incidence classification, surgery reconstruction and Corollary 15.4, and the
finite-net loop-width argument. The Hempel, Plateau--Morrey,
Douglas--Hildebrandt, and parabolic-flow results are retained as explicit
imported contracts with their exact registered Morgan--Tian/White/Topping/
Perelman locations and all hypotheses consumed by later nodes; their classical
source proofs remain part of the human review boundary. One live node,
`lem:fiber-saturation-from-spherical-frontier`, is now mapped to a checked Lean
theorem covering both clauses. The remaining main route is not formalized;
no complete Poincare proof or expert approval is claimed. See
`blueprint/review/fiber-saturation-lean-review.md` for the precise scope.

Chapter 3 is organized into two implementation stages: Stage 3, **Blow-Up
Limits, Kappa-Solutions, and Canonical Neighborhoods**, and Stage 4,
**Continuation of Controlled Ricci Flow with Surgery**.  The handoff is before
the first-failure extension argument; the remaining chapters retain their
existing order and roles.

## Closed-collar component extension

The main package also proves ambient-frontier pullback saturation, the cylinder
component formula, the embedded collar component interval, and transfer of a
component's relative frontier to the ambient frontier. The closed-collar
blueprint node is **not yet marked complete**: identifying an endpoint fiber
as a full ambient boundary component still requires the finite-family interface.
See `blueprint/review/closed-collar-components-lean-review.md` and run
`python3 tests/check_closed_collar.py` for the combined regression audit.

## Build

```bash
lake exe cache get
lake build
```

Graph synchronization and local website preview are documented in the root
`CONTRIBUTING.md`.

## Blueprint map

The project-local `Blueprint map` tab is generated from the live hgraph nodes
and `uses` edges. Regenerate it after changing the blueprint or synchronizing
the graph:

```bash
python3 blueprint/tools/build_blueprint_map.py
```

The generated `blueprint/blueprint-map-tab.html` is loaded only by this
project's blueprint tab; the built-in dependency graph remains the canonical
hgraph view. The map is a collapsed reader view of the same live semantic DAG,
not a smaller proof graph.

## Product-neck boundary pairing

The primary package now also proves the topological product branch of the
boundary-pairing interface: an actual closed-cylinder homeomorphism and the
identification of the two endpoint spheres as entire frontier components.
The new finite disjoint closed-family theorem supplies reusable component
separation. No mapping-torus classification or smooth diffeomorphism is claimed.
No additional blueprint node is marked complete. Details are in
`blueprint/review/product-boundary-pairing-lean-review.md`. Run
`python3 tests/check_product_pairing.py` for the cumulative build and audit.
