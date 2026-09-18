# Smooth covering pullbacks and natural deck transformations

Date: 2026-09-18. Parent: `01093642d2c53898779ba3bd62a7ca8ac784a069`.
This is a local statement audit, not external mathematical review or priority certification.

## Construction and original structures

`CoverLift.chartedSpace` gives the source of a local homeomorphism f a charted
structure by composing actual local sheets of f with the target's existing charts.
The source topology is unchanged. The target's topology, atlas and smooth structure
are unchanged. `CoverLift.isManifold` proves that these charts are smooth:
each transition is a restriction of a genuine original target-chart transition.
`CoverLift.isLocalDiffeomorph` constructs smooth local inverses for f in that atlas.
There is no arbitrary global homeomorphism used to redefine the target's structure.

`CoverPullback.Space c p` is the literal fiber product {(t,z) | c(t)=p(z)} in the
subspace topology of R × N. The forgetful projection is proved to be a local
homeomorphism whenever c is one and p is continuous. Surjectivity is separately
proved from surjectivity of c. A concrete sheet inverse uses a default point only
outside its stated target; this does not add a nonemptiness premise to the global theorem.

For c : Real -> AddCircle L, the natural deck map is literally (t,z) -> (t+L,z).
It has an explicit continuous inverse (t,z) -> (t-L,z). Smoothness then follows from
its projection identity and the local smooth inverses of the forgetful projection.
`contMDiff_of_localDiffeomorph_comp` proves this general smooth-lifting principle.
No smooth-deck map is supplied as a hypothesis.

## Native Bundle.Pullback interface

`bundleHomeomorph` compares the explicit fiber product with Mathlib's dependent
`TotalSpace F (c *ᵖ E)`. It uses the actual induced topology theorem from Mathlib;
no topology is guessed or redefined. Both projection formulas are checked.
`bundleChartedSpace`, `bundle_isManifold` and `bundle_lift_isLocalDiffeomorph`
apply directly to the native total space and its actual `Pullback.lift` map.
The comparison of the two source models is itself a checked diffeomorphism.
`nativeCircleDeck` constructs the deck diffeomorphism on the native pullback,
and proves that it fixes `Pullback.lift` and raises the real height by L.
These results allow arbitrary real L; positivity is needed later for the period
extension results, not for the smooth structure or the deck-map construction.

## Important scope boundary and sanity checks

The new result does NOT imply that the lifted height projection is smooth for an
arbitrary continuous p. The sanity suite proves this failure for p(x)=[abs(x)].
Its canonical lift x -> (abs(x),x) is smooth because its forgetful projection is
identity, while the height composite is abs and is not differentiable at zero.
Thus smooth compatibility of the original bundle's local fiber trivializations
cannot be silently dropped. Establishing that compatibility with the lifted atlas
is still required before the preceding real-period theorem applies to an arbitrary
abstract smooth sphere bundle. No new blueprint completion marker is added.
The new proofs do not classify a closed three-manifold or prove Poincare.

The new suite also checks a real smooth sphere cylinder, nontrivial positive
and negative deck shifts, surjectivity and the native dependent-fiber comparison.
The fixed Lean/Mathlib pins are unchanged. Run `python3 tests/check_cover_pullback.py --fresh`
from the primary package directory. The cumulative audit covers 328 declarations,
including 39 new definitions, abbreviations and theorems. All transitive axioms
must lie in {propext, Classical.choice, Quot.sound}; code placeholders and warnings
are rejected. Clean project builds reuse the pinned dependency cache.
