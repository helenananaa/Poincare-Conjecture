# Complementary frontier selection from genuine one-sided collars

Date: 2026-09-19. Parent: `8dd50bcdcc5efa4d85d34a8dcfb0311797c7f3e3`.
This contribution addresses a topological substep of
`lem:actual-disappearing-component-frontier-saturation`, not its entire statement.
No additional blueprint completion flag is set.

## Inputs and retained obligations

Let Y be Hausdorff and locally connected, C a closed subset, and p outside C.
The component D is Mathlib's actual `connectedComponentIn Cᶜ p`.
Assume D is not the entire ambient component `connectedComponent p`.
The actual frontier of C is covered by a finite pairwise-disjoint family of
central spheres S_i. For each sphere there is an open embedding
`f_i : Sphere2 × (-1,1) -> Y`, with S_i its central section and the exact
local side condition `f_i(x,t) ∈ C iff t ≤ 0`.
These are geometric collar data, not a global neck-chain product or fibration.
In particular, saturation of the frontier of D is NOT one of the inputs.

The theorem does not construct the collars from a smooth embedding. It does
not prove a continuing region satisfies these hypotheses, does not produce
strong Ricci necks, and does not yet construct the smooth manifold structure
on the complementary closure. Those remain separate geometric obligations.

## Outputs

`sphere_collared_complement_frontier_components` produces a nonempty finite
index subset A with frontier D equal to the union of S_i for i in A. Each
selected sphere is connected and an entire connected component of frontier D.
Every unselected sphere is disjoint from frontier D. No claim that A has exactly
two members is made; that requires additional all-neck/fibration information.

## Proof mechanism

Local connectedness makes complementary components open. Their frontier is
contained in frontier C, using closedness of connected components in the
relative complement, rather than assuming this inclusion.
In a collar the positive half is a connected subset of the complement. If a
central point is in frontier D, openness of the collar image and the definition
of closure force that half to meet D. Maximality of connected components then
puts the whole half in D. All central points are limits of this half and belong
to C, hence are frontier points of D. This derives whole-section saturation.
Finite closed disjoint-family separation, already proved in the project, then
identifies the selected sections as maximal frontier components.
Properness forces nonempty frontier, without requiring the ambient space to
be connected. The basic nonemptiness lemma needs no collar hypothesis.

## Validation and reuse

Run `python3 tests/check_complementary_frontier.py --fresh` from the primary
package. The unchanged pins are Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
The verifier rebuilds the package, runs all 19 sanity suites, checks the prior
351 and new 13 printed transitive dependencies (364 total), and checks source
hashes before and after. It also runs the upstream gate when present.
New tests instantiate actual sphere collars and the finite-selection result,
and check the empty-frontier whole-component case. The two build directories
reuse the same pinned Mathlib cache; this is not independent third-party review.
