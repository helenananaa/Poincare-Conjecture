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

## Mapping-torus quotient interfaces

The primary package constructs the integer-deck quotient of a twisted cylinder,
proves the sharp short-strip injectivity criterion, constructs short-strip
image homeomorphisms, and excludes the full-period case when the projected
closure has nonempty topological frontier. Disjointness is derived for genuine
lifted components with a stated finite-strip description. The arbitrary
sphere-bundle and smooth-boundary bridges remain open, with no new blueprint
completion flag. See `blueprint/review/mapping-torus-lean-review.md` and run
`python3 tests/check_mapping_torus.py` for the cumulative audit.

## Actual quotient-region closure

The integer-deck development now derives the finite-strip description of an
actual lifted component, proves that its image is the whole connected region,
and identifies the actual closure before constructing its cylinder homeomorphism.
Topological regular-openness is an explicit boundary bridge; arbitrary smooth
sphere-bundle identification and the diffeomorphism upgrade remain open.
See `blueprint/review/torus-region-lean-review.md`. The cumulative verifier is
`python3 tests/check_torus_region.py`; no new blueprint node is marked complete.

## Intrinsic boundary bridge (conditional)

The primary package proves the intrinsic-boundary/ambient-frontier comparison
from explicit compatible ambient chart extensions, and converts the literal
source boundary equation to regular-openness. Canonical half-space witnesses
and a punctured-line counterexample are checked. The existence of such chart
extensions from a general smooth codimension-zero embedding remains unproved;
this does not replace the pending Lee Proposition 5.46 or complete a blueprint node.
See `blueprint/review/boundary-regularity-lean-review.md` and run
`python3 tests/check_boundary_regularity.py` for the cumulative verification.

## Smooth embedding boundary bridge

The local ambient set charts are now constructed from an actual equal-dimensional
C-infinity smooth embedding into a boundaryless model, rather than assumed.
Intrinsic interior and boundary are identified with the ambient image interior
and frontier; closed image (or properness) supplies the global boundary equality.
The smooth-closure adapter derives regular openness from the original intrinsic
boundary equation and connects it to the quotient-region theorem. It still does
not prove a smooth cylinder diffeomorphism or construct global sphere-bundle
coordinates. No further blueprint node is marked complete. See
`blueprint/review/smooth-embedding-boundary-lean-review.md` and run
`python3 tests/check_smooth_embedding.py` for the cumulative 115-declaration audit.

## Continuous periodic presentation

Global quotient coordinates can now be constructed from a supplied continuous
sphere presentation, its circle base projection, fiberwise injectivity and
one-step gluing. Openness is derived from compact fibers and Hausdorffness.
The smooth-closure region theorem consumes these coordinates without asking
for a preexisting global homeomorphism. This does not prove existence of a
periodic presentation for every abstract sphere bundle or smooth descent.
See `blueprint/review/circle-presentation-lean-review.md`; run
`python3 tests/check_presentation.py` for the 142-declaration cumulative audit.

## Smooth cylinder comparisons

The primary package now includes fixed-structure diffeomorphisms for standard
closed cylinders and product regions. The periodic-region upgrade explicitly
requires the given presentation to be a local smooth diffeomorphism; continuity
alone is not substituted for this premise. No additional blueprint completion
flag is set. See `blueprint/review/smooth-cylinder-lean-review.md` and run
`python3 tests/check_smooth_cylinder.py` for the cumulative audit.

## Abstract circle bundle: topological cut and gluing

`CircleBundle.abstract_sphere_bundle_closed_mappingTorus` starts from a standard
abstract `FiberBundle`, not a supplied periodic map. It constructs a cut-cylinder
parametrization, its endpoint homeomorphism, the exact seam relation, and a
base-compatible homeomorphism from the closed-cylinder quotient to the original
total space. This is a topological result, not yet a smooth periodic presentation.
See `blueprint/review/abstract-bundle-cut-lean-review.md`. Reproduce using
`python3 tests/check_abstract_bundle.py`. No new blueprint completion flag is set.

## Abstract bundle: real presentation and actual frontier components

The closed seam quotient is compared with the real-axis orbit quotient, yielding
a continuous real presentation directly from the abstract compact-fiber bundle.
The sphere specialization also classifies regular-region closures and proves
that their actual frontier consists of exactly two complete bundle fibers,
each an entire nonempty connected component. These remain topological results.
No arbitrary smooth interval trivialization is supplied or claimed. No additional
blueprint completion flags are set. See the `closed-real-bridge-lean-review.md`
and `abstract-boundary-components-lean-review.md` reviews. Reproduce with
`python3 tests/check_abstract_pairing.py --fresh`.

## Smooth real-interval trivialization

Local smooth bundle charts now produce a smooth trivialization covering any
closed real interval, via an explicit collar-matching coordinate correction.
The correction retains the base coordinate and has a proved smooth inverse.
The interval argument adapts Mathlib's topological exhaustion proof; it does
not claim that a previously chosen topological trivialization is smooth.
See `blueprint/review/smooth-interval-splice-lean-review.md`. Reproduce with
`python3 tests/check_smooth_splice.py --fresh`. No periodic smooth seam or
additional blueprint-node completion is claimed.

## Smooth periodic end matching

Local smooth real-base bundle charts, together with a given smooth deck
transformation covering translation by a positive period, now produce a
smooth period chart whose two end collars differ by a single constructed
fiber diffeomorphism. The inverse-chart seam formula and its local smooth
invertibility are also proved. These results retain the original structures.

They do not construct the smooth pullback atlas/deck map for an arbitrary
circle bundle or yet prove the smooth all-real periodic extension. No new
blueprint completion marker is added. See
`blueprint/review/smooth-periodic-endmatching-lean-review.md` and run
`python3 tests/check_periodic_endmatching.py --fresh` for cumulative verification.
