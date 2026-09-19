# Finite oriented neck parameterizations to genuine smooth collars

Baseline: bd6dc4e. No new blueprint completion flag is set.

The new API normalizes any interior cut c of a finite neck with smooth maps
in both directions. It chooses an actual positive width strictly inside both
endpoints, permits either orientation, and preserves the central slice by an
explicit affine formula. An actual image equality describing the continuing
region supplies the side condition; closeness of metrics alone is never used
as a substitute for this condition.

The native sphere, one-dimensional Euclidean axis and the transported R3
model are not silently redefined. Standard smooth structures and subspace
topologies are retained. A separate direct-source check imports the real
MorganTianLib.Ch02.EpsilonNeck module; the sphere, cylinder model and finite
neck domain are definitionally equal, and the actual EpsilonNeckStructure.phi
field on an open ambient region supplies the parameterization.

The main package includes generic finite-neck and native-neck cut-cover
consumers producing the actual complementary closure's smooth structure,
smooth inclusion, intrinsic boundary correspondence and regular openness.
These consumers still assume the explicit cut relation and frontier coverage.
The direct source adapter preserves the source's arbitrary model I; the global
closure consumer uses the existing product ambient model, whose compatibility
with a concrete surgery manifold must still be supplied when applying it.

The two regressions exercise reversed off-center cuts, including the genuine
standard sphere/native-cylinder setting. The actual source adapter is checked
separately to avoid creating a backwards dependency of the main topology
package on the Riemannian source project.
