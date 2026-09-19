# Smooth collar cover to the actual complementary closure

Date: 2026-09-19. Baseline: 89be142.

## Inputs

Let N be a smooth manifold modeled on V × Real and X a preconnected smooth
manifold modeled on V. Let C be closed, N locally connected, and
D = connectedComponentIn C-complement p. Every point of frontier D is assumed
to be the central image of a genuine PartialDiffeomorph from X × Real to N
with source exactly X × (-1,1), and C is precisely the nonpositive side there.
The partial diffeomorphism carries actual maps, open source/target and smooth
forward/inverse maps. Neither local domain models nor a closure atlas are input.

## Construction

The normalized topological restriction is proved an open embedding. Collar
coordinates combine the inverse collar with a cross-section chart and the real
coordinate. Forward/inverse smoothness uses product-to-vector and vector-to-
product smoothness explicitly, respecting Lean's ModelProd type tags. The same
coordinates straighten closure D into the chosen model range.

The common model is the geometric half-space {z : V × Real | 0 <= z.2}, with
the usual induced topology. Its total inverse uses clamping only outside its
range; clamping is not asserted smooth. For any interior point of a closed
set, translating and shrinking an existing ambient smooth chart places its
image inside the model interior. Thus boundary models suffice to cover ALL
points; DomainAtlas then constructs a charted smooth structure on the existing
subspace topology, including a smooth inclusion and correct intrinsic boundary.
The collar cover also proves frontier(closure D) = frontier D and regular openness.

## Nonvacuity

Three regression goals construct an actual identity strip collar, prove the
actual upper complementary component and its boundary, and apply the entire
construction to this nonempty example. A concrete V = EuclideanSpace Real (Fin 2)
instance checks the three-dimensional boundary-bearing case.

## Retained obligations

The supplied smooth collar cover has not been produced from Ricci surgery or
from a general sphere embedding. The statement is not a global Poincare result.
Ambient model structures remain explicit inputs; adapting every surrounding
geometric package to this particular product model is not claimed automatic.
No main-route blueprint completion flag is added.
