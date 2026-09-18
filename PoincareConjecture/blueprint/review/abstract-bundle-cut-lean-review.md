# Abstract circle bundle: cut trivialization and endpoint quotient

Date: 2026-09-18. Parent: `d15d97cf2dc9cfd73b6b5202b63539d79669e0e4`.
This is a local statement audit, not upstream or independent expert approval.

## Inputs and derived data

The final theorem uses Mathlib's standard `FiberBundle F E` over `AddCircle L`,
with `L > 0`, a compact nonempty model fiber F, and a Hausdorff original total space.
It assumes neither a global period map, a monodromy homeomorphism, a cut
trivialization, nor a preexisting mapping-torus comparison homeomorphism.
Fiber nonemptiness needed by the pullback construction is derived from F.

The real-axis pullback uses the actual covering map `t ↦ (t : AddCircle L)`.
`cutTrivialization` is selected from Mathlib's proved
`FiberBundle.exists_trivialization_Icc_subset`; its parameter interval is `[0,L]`.
The canonical pullback map and this trivialization produce `cutMap` on `F × [0,L]`.
Continuity, the base projection formula, fiberwise injectivity, full fiber range,
and surjectivity onto the original total space are all proved.

`monodromy` compares the two endpoint fiber charts, using equality transport
between the fibers over `[L]` and `[0]`. The equation is
`cutMap (x,L) = cutMap (monodromy x,0)`. Uniqueness is proved only relative to
this fixed cut parametrization; the monodromy is not claimed choice-independent.

## Relation and topological comparison

`Seam` is the explicit disjunction: equal points, top-to-bottom with the twist,
or the reverse endpoint pair. Its definition contains no bundle map or kernel.
`cutMap_eq_iff_seam` proves this is exactly the equality relation of the cut map,
so there are no hidden interior identifications.
`ClosedMappingTorus` is the genuine topological quotient by this relation.
The descended map is continuous and bijective. Compactness of the source and
Hausdorffness of the original total space prove its inverse continuous.
The final comparison preserves the base projection on every representative.
The sphere corollary uses the real unit sphere in Euclidean three-space.

## Deliberate scope limits

This result constructs a CLOSED-CYLINDER topological mapping-torus model.
It is not yet an identification with the existing infinite real-axis deck quotient.
No continuous extension of the cut parametrization to all real times is claimed.
The chosen interval trivialization is topological: the cited Mathlib theorem
does not assert membership in a smooth trivialization atlas. Consequently neither
the chosen monodromy nor the seam comparison is claimed smooth. This stage does
not discharge the locally-diffeomorphic-presentation input of the previous smooth
cylinder theorem. Smooth interval triviality and seam control remain to be proved.
No additional blueprint completion flag or full Poincare theorem is asserted.

## Validation

Run `python3 tests/check_abstract_bundle.py` in the primary package. It uses the
unchanged Lean 4.32.1 / Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` pins,
executes ten sanity suites, and audits 191 declarations. New examples include a
standard trivial sphere bundle, a discrete two-point fiber bundle, endpoint
identification and rejection of extra interior identifications. These are not
claimed to constitute an independent nontrivial smooth-bundle test.
