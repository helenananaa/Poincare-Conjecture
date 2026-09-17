# Continuous circle presentation and global quotient coordinates

Date: 2026-09-17. Parent: `ead5275cb109e93584744a28497fa247a2382cca`.
This is a local statement review, not independent expert or upstream approval.

## Exact hypotheses and newly derived results

The input is a continuous surjection q : X × Real → N, a continuous circle-valued
map π : N → AddCircle L, the equality π(q(x,t)) = [t], injectivity of q at each
fixed height, and one-step gluing. The final sphere adapter uses the source
convention q(x,t+L) = q(φ x,t), hence `Space φ.symm L` as before.

One-step invariance is extended to ALL integers, including negative ones.
`presentation_eq_iff_orbit` then proves the complete integer orbit equivalence
from the circle base and fiberwise injectivity. Exact orbit equivalence is not
assumed as a separate field, and gluing alone is not claimed sufficient.

The descended map is constructed with `Quotient.lift`. Injectivity, surjectivity,
continuity and openness give `presentationHomeomorph`; its commutation with q
and its uniqueness are proved. Set pullback through the inverse coordinates
commutes with the supplied q, so frontier saturation is not added again.

For compact X and Hausdorff N, openness and local-homeomorphism of q are derived
from continuity and the preceding fiber conditions. A short closed strip is
compact and injective; its image is embedded. The image of any complete cylinder
is exactly the inverse image under π of its circle heights. This makes short
open strip images open and yields local invertibility. Thus the final sphere
adapter assumes neither quotient openness nor a preexisting homeomorphism.

## Concrete models and regressions

`circleProjection` is defined on the actual deck quotient with values in the
existing AddCircle, with a continuity proof. The canonical quotient has injective
fixed-height fibers and short local charts. Descent on the canonical presentation
is proved to be the identity homeomorphism. The tests also instantiate global
coordinates for the independent product S² × AddCircle 4, use an actual antipodal
sphere twist and a negative deck iterate, and exhibit failure of fiber injectivity
for a projection which forgets a Bool fiber despite obeying one-step gluing.

## Source-facing integration and remaining scope

`sphere_region_of_presented_smoothClosure` no longer requires the previous
quotient-coordinate homeomorphism or the earlier regular-open assumption.
The original smooth structure on N, its closed-region smooth embedding,
equal-dimensional condition, intrinsic boundary equality and nonempty saturated
frontier remain explicit. The conclusion is a topological Homeomorph, not a
Diffeomorph obtained by transporting an artificial smooth structure.

This is a comparison theorem for a SUPPLIED periodic presentation. Constructing
q and a time-independent monodromy φ from an arbitrary sphere bundle remains
unproved here. Smoothness of the descending comparison and smooth closed-cylinder
classification also remain unproved. No additional blueprint completion flag is set.

## Reproduction

Keep Lean 4.32.1 and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.
From the primary package run `python3 tests/check_presentation.py`.
The cumulative audit covers 142 declarations (115 previous and 27 new), not
142 completed blueprint steps. All transitive axiom sets must lie within
`{propext, Classical.choice, Quot.sound}`. All eight sanity suites and the upstream
build gate must pass without warnings. The new declarations include three
definitions; the other twenty-four are theorems.
