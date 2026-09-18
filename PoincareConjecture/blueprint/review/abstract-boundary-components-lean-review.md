# Actual boundary components of an abstract sphere-bundle region

Date: 2026-09-18. Built on the independently rechecked closed/real bridge.

`MappingTorus.region_frontier_circle_pair` takes the previously proved short
strip description and uses injectivity on its closed strip to compute the
actual frontier as the image of the two endpoint fibers. The strict width
bound proves that their circle heights are different. Image/closure commutation
is not assumed; the previously verified closure equality is used explicitly.

`abstract_sphere_bundle_frontier_pair` transports this equality back through
the base-preserving comparison to the original abstract bundle. Its conclusion
is an equality with the inverse image of two distinct points under the actual
`Bundle.TotalSpace.proj`, not with arbitrary sets chosen by a cylinder homeomorphism.

`abstract_sphere_bundle_fiber_connected` obtains genuine nonempty connected
fibers from standard local trivializations and the Euclidean sphere.
`abstract_sphere_bundle_boundary_components` additionally proves disjointness,
closedness in the ambient total space as an intermediate fact, and that each
of the two fibers is an entire connected component of the actual frontier.
There can be no other component because their union equals the frontier.

Inputs remain: a standard sphere FiberBundle over AddCircle L, Hausdorff total
space, L > 0, an open connected nonempty regular-open region D, nonempty frontier,
and frontier membership constant along actual bundle fibers. The earlier
smooth-closure boundary theorem can supply regular openness under its explicit
smooth embedding and intrinsic boundary equality assumptions. Neither a smooth
bundle trivialization nor the abstract-bundle diffeomorphism is claimed here.
