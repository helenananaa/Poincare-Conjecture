# Relative open-product classification and recovered smooth atlas validation

Date: 2026-09-19. Last chat-delivered source: `01093642d2c53898779ba3bd62a7ca8ac784a069`.
The saved covering-pullback commit `5a85ceaf925e512a7f68767daed978283afaf6b2`
and the uncommitted smooth-atlas implementation were recovered from disk. Their
source hashes matched the previous 328- and 348-declaration reports. This work
rechecks that implementation; those 59 declarations are not newly authored here.

## New mathematical content

`relativeClosedCylinderDiffeomorph` compares the actual relative closure with
`X × Icc a b`. The source keeps its supplied manifold structure, the open real
parameter domain uses Mathlib's inherited atlas, and the target interval uses
its standard boundary charts. A closed-cylinder set equality is a premise only
of this helper; it is proved from the region hypotheses in the main theorem.

`relative_product_region_diffeomorph` accepts any open order-connected real
parameter domain J, not just all of Real. Compactness is for closure in `X × J`.
It derives the endpoints, interval shape and relative closure formula. The
conclusion is a genuine diffeomorphism to `X × Icc 0 1`. The closure inclusion
is a smooth embedding; no new atlas on the closure is installed.

Both smooth directions are checked through existing immersion predicates:
the open inclusion `X × J -> X × Real` and the standard closed-cylinder inclusion.
The unproved generic `IsSmoothEmbedding.comp` declaration is not invoked.

`relative_sphere_region_boundary_pairing` specializes to the real unit sphere
and combines the smooth classification with the already verified identification
of the two endpoint fibers as the entire relative-frontier components.
The other branch remains `abstract_smooth_sphere_bundle_boundary_pairing`, now
recovered and revalidated with the original locally smooth bundle-chart premises.
The two branches retain genuine relative frontiers and the original structures.

## Scope and verification

No Ricci-flow, surgery, all-neck fibration, or Poincare theorem is proved here.
The local implementation covers the product and circle-bundle classification
interfaces; no new blueprint completion marker or upstream acceptance is claimed.
In particular, construction of the fibered neck models from actual geometric
neck chains belongs to the next dependency layer, not to these input assumptions.

Run `python3 tests/check_relative_product.py --fresh` in the main package.
The cumulative audit covers 351 selected declarations: 348 recovered and three
new (one diffeomorphism definition and two theorems). Eighteen suites include
bounded and half-infinite open domains, the actual smooth closed-cylinder map,
its endpoint values, compact relative closure, and relative-versus-ambient frontier.
The last tests do not independently reconstruct a smooth structure on that
particular closure or substitute for semantic review of the theorem premises.
Clean main-package and separate-source builds share the fixed Mathlib dependency
cache. They are reproducibility checks, not independent expert validation.
