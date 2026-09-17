# Intrinsic boundary / ambient frontier: conditional chart bridge

Date: 2026-09-17. Parent: `bcfed18b24464d7457d4a3fb52ca40e42b44f272`.
This is a local review, not independent expert or upstream approval.

## What is proved

`HasAmbientModelCharts I K` is an explicit local geometric condition. For each
point p of the actual subtype K, it supplies an ambient open partial homeomorphism
e to the normed model space, whose source contains p; e maps K locally to
`range I`; and e(p) agrees with the intrinsic extended chart at p.
It does not assume an equality of boundaries, an equality of interiors, or
regular-openness. `OpenPartialHomeomorph.IsImage` encodes the local set equality.

From these witnesses the code proves, using Mathlib's actual
`ModelWithCorners.IsInteriorPoint` and `IsBoundaryPoint`, that intrinsic interior
is exactly ambient interior, and (for K closed) that the image of the intrinsic
boundary under subtype inclusion is exactly the ambient frontier.

For an open region D, put K = closure D. Under those chart witnesses, the source
condition `Subtype.val '' I.boundary K = frontier D` is proved EQUIVALENT to
`D = interior (closure D)`. The sphere-quotient adapter now consumes that literal
intrinsic boundary equation rather than requiring regular-openness separately.
Its output is the previously constructed genuine topological cylinder homeomorphism.

Canonical chart-extension witnesses are constructed for the actual Euclidean
half-space in every positive dimension, and its intrinsic boundary is proved to
be the coordinate hyperplane. These witnesses are not empty types or extra axioms.

## What is NOT proved

The existence of compatible ambient chart extensions for EVERY properly smoothly
embedded codimension-zero manifold-with-boundary is not proved in this contribution.
That is a genuine remaining geometric theorem; the conditional chart bridge must
not be reported as an unconditional proof of Lee Proposition 5.46.

At the pinned upstream base, both declarations in
`formalized-sources/LeeSmooth/LeeSmoothLib/Ch05/Sec05_36/Proposition_5_46.lean`
still end in unproved placeholders. They are not imported into this contribution
and are not used to justify a global boundary conversion. Neither declaration is
replaced here. The final source-facing adapter retains `HasAmbientModelCharts`
as a visible hypothesis. No additional blueprint node is marked complete.
The sphere-bundle identification and smooth diffeomorphism obligations also remain.

## Verification

The dependency pins are unchanged: Lean 4.32.1, Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Run
`python3 tests/check_boundary_regularity.py` from the primary package.
The cumulative audit has 100 declarations: 87 previous, 10 new theorems,
2 definitions (one is an abbreviation) and 1 charted-space instance.
All transitive axioms must be contained in `{propext, Classical.choice, Quot.sound}`.
The new sanity suite includes actual half-space witnesses and the punctured-line
counterexample: nonempty frontier does not imply nonempty frontier of the closure.
No full-repository completion percentage is inferred from declaration counts.
