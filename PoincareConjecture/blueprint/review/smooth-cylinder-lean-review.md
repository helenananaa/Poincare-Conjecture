# Smooth cylinder classification: local statement review

Parent commit: `b7e0d78bd82dcb2f3e8ada8fcca15bc9c81b15d5`.
This is a local formalization review, not independent or upstream acceptance.

## What is now proved

`diffeomorphOfEqualEmbeddingRange` identifies two smooth embedded parametrizations
with the same image. `ContMDiff.iff_comp_isImmersion` proves smoothness of the
comparison and its inverse, retaining all original charted structures.

`Icc_subtype_smoothEmbedding` proves that the inclusion of a nondegenerate real
closed interval is a smooth embedding with Mathlib's standard half-space charts.
The proof treats the left and right endpoint charts separately. It neither
changes the topology nor installs a pulled-back smooth structure.
`iccDiffeomorphUnit` upgrades the actual affine map `(t-a)/(b-a)` and its inverse.
`cylinderDiffeomorphUnit` takes its product with the identity on the given fiber.

`product_region_diffeomorph` applies to a nonempty connected open U in X × Real,
with saturated actual frontier and compact actual closure. The closure has a
given smooth manifold structure, and its inclusion must be a smooth embedding.
It constructs a diffeomorphism from that closure to the standard X × [0,1].
An arbitrary relative parameter domain J has not been silently replaced by Real.

## Periodic presentation and the exact extra smooth premise

`sphere_region_diffeomorph_of_smoothPresentation` starts from the previous
continuous periodic-presentation data, but replaces continuity of q by the
explicit stronger premise that q is a local smooth diffeomorphism for the
standard sphere-times-real structure and the given ambient structure.
The actual closure must still be smoothly embedded in the original ambient N;
the intrinsic boundary equality, equal dimensions and frontier conditions remain.

`presented_region_closedStrip` recovers a specific strip and its actual closure
image. `comparison_inverse_contMDiff` uses local smooth inverses of q to prove
the inverse comparison smooth. No global smooth inverse of q, smooth inverse
of the closure parametrization, or ambient comparison diffeomorphism is assumed.
The final target is the actual unit sphere times the standard closed unit interval.

A merely continuous presentation is not enough for this upgrade. The tests include
the smooth map t -> t^3, which is proved not to be a local diffeomorphism at all
points because its differential vanishes at zero. The canonical arbitrary
mapping-torus quotient is not assigned a new smooth structure in this extension.

## Validation and remaining work

Run `python3 tests/check_smooth_cylinder.py` from the primary package. This checks
159 cumulative declarations and nine sanity suites under the unchanged Lean
4.32.1 / Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` pins.
The new tests exercise endpoint normalization, the standard sphere cylinder,
a translated-interval comparison, boundary transport and the cubic obstruction.

No additional blueprint node is marked complete. Existence of periodic data from
an arbitrary abstract sphere bundle, derivation of the local-diffeomorphism
premise from a chosen bundle formalization, and the remaining full boundary-pairing
interfaces are still separate obligations. No full Poincare theorem is asserted.
