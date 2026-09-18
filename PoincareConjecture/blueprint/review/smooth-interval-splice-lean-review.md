# Smooth interval trivialization: local statement review

Date: 2026-09-18. Parent: `aeb9ef1661669ffc4927d95f9c62fb1ae5924ce5`.
This is a local review, not independent mathematical or upstream acceptance.

## Exact statement

`SmoothBundle.exists_smooth_trivialization_Icc` starts with a continuous map
`p : M -> Real` and, at every real base point, an actual
`Bundle.Trivialization F p` whose forward and inverse maps are C-infinity on
their genuine open domains in the supplied charted structures. It produces
an actual smooth trivialization whose base domain contains any prescribed
closed interval `[a,b]`. No global trivialization or endpoint compatibility
is input. No compactness, connectedness or linear structure of F is required.
The case b < a is allowed and handled as an empty interval.

`fiberBundle_exists_smooth_trivialization_Icc` specializes this statement to a
standard Mathlib `FiberBundle F E` over Real whose chosen atlas charts are
smooth in both directions. This uses the original bundle projection, topology
and supplied manifold structures. The output chart is not asserted to belong
to the original selected atlas; its smooth compatibility is proved directly.

`IsSmoothTrivialization` is exactly the pair of `ContMDiffOn` statements for
the existing trivialization and its inverse. It contains no interval existence,
global classification, boundary equality or period gluing field.

## Construction, not an added compatibility assumption

`seamClamp c d` is C-infinity, equals t on `[c-d,c+d]`, equals c outside
`(c-2d,c+2d)`, and has image in that latter open interval when d > 0.
The construction uses Mathlib's proved `Real.smoothTransition`.

For two overlapping actual smooth trivializations e and f, evaluate their
fiber coordinate change at `seamClamp c d t`. The product map preserves t;
only the argument at which the fiber change is evaluated is clamped. The
inverse is the reversed coordinate change at the same parameter. Both maps
are proved smooth, so this is a genuine product diffeomorphism even though
the scalar clamp itself is not injective.

The corrected second chart agrees exactly with the first throughout an open
collar of c. Agreement of their inverse charts is derived using their actual
inverse laws. The standard piecewise trivialization is then smooth on both
source and target. The left chart is unchanged on the left half of the splice.
The collar radius is obtained from openness of the overlap, not supplied to
the final `exists_smooth_splice` theorem.

The interval proof adapts Mathlib's Apache-2.0
`FiberBundle.exists_trivialization_Icc_subset` supremum argument, replacing
its point-matching topological splice with the proved smooth collar splice.
This is a formalization/extension of classical mathematics, with no novelty
or first-formalization priority claim.

## What remains

No claim is made that the earlier `cutTrivialization` selected by a topological
existence theorem is smooth. The new existence theorem constructs a new chart.
The smooth pullback atlas for the circle bundle, prescribed smooth collar germs
at both period ends, and a locally diffeomorphic periodic extension have not
been constructed here. In particular no complete abstract smooth mapping-torus
classification or Poincare theorem is claimed and no blueprint flag changes.
