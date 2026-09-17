# Product-neck boundary pairing: local Lean review

Date: 2026-09-17. Parent: `d7e9cf8a83592307b118198bf258af36f93ced23`.
The parent closed-collar contribution was present in the working tree; its
31-declaration audit and source hashes were checked before this extension.
This review is a local statement audit, not upstream or independent expert approval.

## New mathematical content

`relativeClosedCylinderHomeomorph` explicitly removes the redundant relative
parameter subtype, assuming the full closed interval lies in the parameter domain.
`relativeClosedCylinderUnitHomeomorph` composes this map with Mathlib's affine
homeomorphism `[a,b]` to `[0,1]`. Both maps have checked inverses and continuity.

`sphere_product_closure_homeomorph` constructs a homeomorphism from the actual
relative closure of U to `Sphere2 × Icc (0 : Real) 1`. Its inputs are an open
order-connected real parameter domain, an open nonempty connected region U,
fiber-saturation of the actual relative frontier, and compactness of the relative
closure. The interval endpoints are produced by the previous geometric interface.
`neck_closure_homeomorph_unitCylinder` transports this result through supplied
genuine homeomorphic neck coordinates; it does not construct those coordinates.

`componentIn_disjoint_closed_union` and `componentIn_finite_disjoint_closed`
prove maximality, not merely connectedness, of the displayed closed components.
The finite-family theorem permits empty members, but a chosen component is based
at a point belonging to that member. Finiteness, closedness and disjointness are
explicit hypotheses; none is silently inferred from a picture of spheres.

`sphere_product_two_frontier_components` proves that the produced endpoint
fibers are disjoint entire connected components of `frontier U`, and that every
component based at a frontier point is one of those two fibers.
`relative_fiber_boundary_pairing_product` combines this result with the actual
closed-cylinder homeomorphism. `Sphere2` remains the unit sphere in Real^3.

## Relation to the blueprint

The target is the product alternative of `lem:relative-fiber-boundary-pairing`.
The current result is topological (`Homeomorph`), not a smooth diffeomorphism.
The closed sphere-bundle/mapping-torus alternative is not covered. No extra
blueprint completion flag is set, and no global Poincare theorem is claimed.

The new finite-family result supplies component-separation infrastructure for
the preceding closed-collar node. Identifying an actual endpoint fiber with a
member of the displayed ambient sphere family is still a separate interface;
whole-fiber membership in the frontier alone is not declared sufficient.

## Validation and reproduction

The unchanged pins are Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. From the primary package run:

```bash
python3 tests/check_product_pairing.py
```

The verifier runs the upstream build gate, both prior sanity suites, new concrete
product-cylinder examples, and a cumulative audit of 40 declarations (31 prior,
9 new). All transitive axiom sets must lie in
`{propext, Classical.choice, Quot.sound}`. New source placeholders and warnings
are rejected. The final validation starts without project build artifacts,
while using the pinned Mathlib dependency cache.
