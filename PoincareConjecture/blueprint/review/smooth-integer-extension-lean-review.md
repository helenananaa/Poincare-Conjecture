# Smooth integer extension: local statement review

Date: 2026-09-18. Parent: `684a8dd203bb5795415b43195e2d7889bf170a9c`.
This is a local review, not upstream acceptance or third-party verification.

## Exact input and output

The principal theorem `SmoothBundle.exists_equivariant_real_diffeomorph` takes
an actual continuous projection p : M -> Real, local genuine bundle charts
smooth in both directions, a supplied diffeomorphism T of M, a positive L,
and the height equation p(T(z)) = p(z) + L. All model and charted-space
structures remain the originally supplied ones. A period chart and smooth
fiber twist are constructed using the previously checked end-matching theorem.

The output is a fiber diffeomorphism phi and a global diffeomorphism
E : (Real x F) -> M satisfying p(E(t,x)) = t and, for every integer n,
E(t+n*L,x) = T^n(E(t,phi^n(x))). Negative periods are included.
No chosen global inverse, global smoothness, global trivialization, or
pre-existing smooth twist is an input.

M is the space over the real line, not the compact total space over the circle.
The theorem must not be restated as saying that a circle bundle itself is
homeomorphic to an infinite cylinder. A forgetful map to the circle-bundle
total space is a separate geometric construction.

## Proof mechanism

With n = floor(t/L), r = t-n*L, and P the inverse of the constructed period
chart, the explicit formula is E(t,x) = T^n(P(r,phi^n(x))). Integer powers use
Homeomorph's group operation; their forward and inverse smoothness are proved.
The period remainder lies in [0,L), also for negative t.

On the enlarged collar (-epsilon,L+epsilon), the formula equals P, using the
three possible period indices -1, 0 and 1 and the actual open-collar seam
identity. The integer translation law then gives agreement with a fixed smooth
chart on every translated enlarged interval. Local smooth invertibility follows
from a restricted partial diffeomorphism representing the same germ. The floor
function itself is never asserted continuous or differentiable.

Injectivity follows from the exact height equation and the inverse period
chart on one fiber. For surjectivity, move a point z back by T^(-floor(p(z)/L)),
read its period coordinates, and undo the corresponding fiber iterate. A
bijective local diffeomorphism then supplies a checked smooth global inverse.

## Remaining geometry

This does not construct the smooth pullback of an arbitrary abstract smooth
circle bundle, its smooth deck transformation T, or the smooth local inverse
of its forgetful projection. The existing topological pullback and arbitrary
topological twist are not silently declared smooth. No new blueprint node is
marked complete, and no Poincare final theorem is claimed.

## Verification

Pins remain Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
Run `python3 tests/check_integer_extension.py --fresh` from the primary package
in Linux or WSL. The runner locks this package's validation directory, rebuilds
the project, runs the previous fourteen sanity suites and the new suite, then
checks a cumulative 289-declaration transitive-axiom audit. All axiom sets must
be contained in `{propext, Classical.choice, Quot.sound}`.

The new tests distinguish floor from truncation at negative times, use a
non-involutive twist to check both seam directions, instantiate global local
smoothness, and construct the global diffeomorphism from two genuine local
charts and a time-dependent shear deck transformation. A separate instance
uses the standard smooth two-sphere. No mathematical priority is asserted.
