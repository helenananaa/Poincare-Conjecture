# Equal-dimensional smooth embeddings: intrinsic/ambient boundary

Date: 2026-09-17. Parent: `929fc4962bf7e9a8486baebdf3bfa28a518d7540`.
Local mathematical and source audit, not independent expert or upstream acceptance.

## Removed proof obligation

The preceding bridge required `HasAmbientModelCharts`. The new theorems instead
construct ambient charts from Mathlib's actual `Manifold.IsSmoothEmbedding`,
equality of finite real model-space dimensions, and a boundaryless AMBIENT MODEL.
The source has its given C-infinity manifold-with-corners structure.
No `HasAmbientModelCharts`, boundary equality, or regular-open assumption is used
in the local chart construction or in the basic boundary correspondence.

An immersion normal form initially has an auxiliary complement C. The continuous
linear equivalence E × C ≃ F makes C finite dimensional. Equal dimensions then
force C to be a subsingleton. This produces full-dimensional normal coordinates.
Topological embedding gives an ambient neighborhood whose full inverse image
lies in the source chart. Shrinking also in the model target yields an exact
local set model, excluding other source points from the neighborhood.

The normal-form source chart belongs to the maximal atlas, not necessarily the
preferred chart. `MaximalAtlasBoundary.lean` generalizes Mathlib's chart-invariance
proof to that atlas. Its adapted proof provenance and Apache-2.0 source are noted
in the module; no unfinished reference-library theorem is imported.

## Statements and remaining scope

`smoothEmbedding_interior_iff` and `smoothEmbedding_boundary_iff` compare the
actual intrinsic predicates to interior/frontier of the actual image.
`smoothEmbedding_interior_image` requires no closed-image assumption.
`smoothEmbedding_boundary_image` requires a closed image, since otherwise there
can be additional frontier limit points not in the image. The proper-map version
derives closedness and does not assume it as a boundary property.

For a smooth closed-domain inclusion, `closedDomain_boundary_image` proves the
mathematical boundary correspondence underlying the unfinished Lee 5.46 interface.
The source-library file is NOT patched or imported. Its broader owner API may
still need a separate adapter. In particular we require `J.Boundaryless`, not just
`BoundarylessManifold J N` for an arbitrary non-boundaryless model J.

`regularOpen_of_smoothClosure_boundary` derives regular openness from the original
intrinsic boundary equality. `sphere_region_of_smoothClosure` composes this with
the previously proved quotient classification through supplied genuine quotient
coordinates. It retains the quotient-coordinate identification, the original
intrinsic boundary equality, fiber saturation and nonempty frontier explicitly.
It does not assert a smooth cylinder diffeomorphism or construct the global
sphere-bundle representation. No additional blueprint node is marked complete.

## Validation

Use unchanged Lean 4.32.1 and Mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
Run `python3 tests/check_smooth_embedding.py` from the primary package.
The cumulative audit covers 115 declarations: 100 prior plus 15 new theorems.
Actual half-space inclusions are proved C-infinity smooth embeddings, and tests
cover the boundary, interior, ambient-chart existence and zero-dimensional case.
All printed axiom sets must lie in `{propext, Classical.choice, Quot.sound}`.
