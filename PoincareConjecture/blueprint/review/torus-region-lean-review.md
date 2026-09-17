# Classification of an actual region in the integer-deck quotient

Date: 2026-09-17. Parent: `9af0300d063e59a33d919818f7fd7eea79958bbc`.
The saved parent report audited 69 declarations; its complete source hashes
were checked against the working tree before this extension. This is a local
statement audit, not upstream acceptance or independent expert review.

## Removed assumptions

The parent `lifted_strip_component_width_lt` still required a finite-strip
shape and a boundary condition on the image of the chosen component. The new
`lifted_component_finite_strip` derives finite width from a proper periodic
region: a missing real base point has missing integer translates on both sides
of every base component. Openness and real connectedness then identify the
component as an actual finite open interval. No compactness of a lifted
component is assumed.

`image_lifted_component_eq` proves that the chosen component projects onto the
ENTIRE connected quotient region. Intersecting projected components coincide
by the exact deck relation. Open projected components then give a separation
argument. Coverage is not an assumed conclusion or a path-lifting stub.

`closure_image_openStrip` proves the relevant equality of closures explicitly.
The projected closed strip has an open complement, namely the complementary
open strip. Half-open period representatives handle the identified endpoint.
Continuity alone would give only one inclusion; the other uses this closedness.

## Verified conclusion and remaining boundary

`region_short_strip` derives a,b with a<b and b-a<L, the full-region image
formula, and its actual closure formula. `region_closure_homeomorph` constructs
a homeomorphism from that closure to X × [0,1], for preconnected X. Nonempty
connected D supplies the necessary nonempty fiber witness internally.

The input is an open connected D, saturation of the pullback of its actual
topological frontier, and nonempty frontier of closure(D). The regular-open
condition D = interior(closure D) implies frontier(closure D) = frontier D.
`sphere_bundle_quotient_regular_region` uses that explicit condition with the
actual unit two-sphere and the blueprint twist convention (`Space phi.symm L`).
There is no assumption of finite strip shape or component-image coverage.

NOT proved here: that an arbitrary smooth sphere bundle is represented by this
quotient with the required smooth structure; the bridge from the blueprint's
intrinsic smooth-boundary condition to regular-openness; or the upgrade from
homeomorphism to diffeomorphism. No additional blueprint completion flag is set.
This contribution also does not claim a complete Poincare proof or mathematical
novelty of these classical topological facts.

## Verification

Unchanged pins: Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Run from the primary package:

```bash
python3 tests/check_torus_region.py
```

The cumulative audit covers 87 declarations (69 saved, 18 new). A concrete
antipodally twisted sphere quotient instantiates every input of the new closure
classification. A full-period negative test checks the essential boundary
obstruction. All prior sanity suites are rerun. The final run begins without
project build artifacts, while reusing the fixed Mathlib dependency cache.
Only the standard classical axiom set is allowed by the transitive audit.
