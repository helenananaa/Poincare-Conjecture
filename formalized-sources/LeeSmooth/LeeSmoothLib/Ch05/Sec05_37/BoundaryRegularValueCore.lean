import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
import LeeSmoothLib.Ch05.Sec05_37.BoundaryRegularPreimageLinear
import LeeSmoothLib.Ch05.Sec05_37.CInfinityNeatSliceAtlas

/-!
# Problem 5-23: regular preimages for manifolds with boundary

The source in this theorem is deliberately the textbook finite-dimensional real half-space
model, not an arbitrary model with corners.  An arbitrary corners model can contain a quadrant,
where the claimed manifold-*with-boundary* conclusion is false.  The separation and countability
hypotheses are also explicit because they are part of the requested bundled output.

The boundary regularity predicate below does **not** use `mfderivWithin` on the boundary as a thin
subset of the ambient manifold.  Such an ambient-domain derivative is not canonical.  Instead it
restricts the actual manifold derivative to the standard boundary tangent hyperplane, the kernel
of the normal coordinate in a compatible half-space chart.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

namespace Manifold

universe uM uN

section BoundaryRegularValue

variable (n m : ℕ)
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

/-- Correct boundary regularity for a map from a standard half-space manifold.

At a boundary point, `mfderiv` is the actual derivative in compatible standard half-space and
Euclidean charts.  We restrict it along the continuous-linear inclusion
`ker (v ↦ v 0) ↪ ℝⁿ⁺¹`; this is the tangent hyperplane of the boundary.  In particular, this
definition makes no arbitrary choice of an ambient derivative of a function defined only on a
thin subset. -/
def IsBoundaryRegularValue (F : M → N) (c : N) : Prop :=
  ∀ x : M, x ∈ (𝓡∂ (n + 1)).boundary M → F x = c →
    Function.Surjective
      (restrictToStandardBoundaryTangent
        (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F x))

/-- Pointwise spelling of the corrected intrinsic boundary-regularity condition. -/
theorem isBoundaryRegularValue_iff (F : M → N) (c : N) :
    IsBoundaryRegularValue n m F c ↔
      ∀ x : M, x ∈ (𝓡∂ (n + 1)).boundary M → F x = c →
        Function.Surjective
          (restrictToStandardBoundaryTangent
            (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F x)) := by
  rfl

/-- At a boundary point, corrected boundary regularity makes the derivative of `(F,t)` onto,
where `t` is the source normal coordinate.  This is the linear input for the ordinary inverse
function theorem applied to an ambient extension. -/
theorem boundaryRegularValue_joint_derivative_surjective
    {F : M → N} {c : N} (hBoundary : IsBoundaryRegularValue n m F c)
    {x : M} (hxBoundary : x ∈ (𝓡∂ (n + 1)).boundary M) (hFx : F x = c) :
    Function.Surjective
      ((mfderiv (𝓡∂ (n + 1)) (𝓡 m) F x).prod
        (standardHalfSpaceNormal n)) := by
  exact surjective_prod_standardHalfSpaceNormal_of_restrict_surjective _
    (hBoundary x hxBoundary hFx)

end BoundaryRegularValue

section EmptyFiber

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- The empty subtype has an explicit `C∞` half-space atlas and its inclusion is a `C∞` smooth
embedding.  Unlike the old `SmoothManifoldWithBoundary` owner, this statement does not silently
ask for outer-top (real-analytic) regularity. -/
theorem empty_subtype_c_infinity_manifold_with_boundary_structure_into (k : ℕ) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (k + 1)) (∅ : Set M),
      ∃ hs : IsManifold (𝓡∂ (k + 1)) ∞ (∅ : Set M),
        let _ : ChartedSpace (EuclideanHalfSpace (k + 1)) (∅ : Set M) := cs
        let _ : IsManifold (𝓡∂ (k + 1)) ∞ (∅ : Set M) := hs
        IsSmoothEmbedding (𝓡∂ (k + 1)) (𝓡∂ (n + 1)) ∞
          ((↑) : (∅ : Set M) → M) := by
  let cs : ChartedSpace (EuclideanHalfSpace (k + 1)) (∅ : Set M) := ChartedSpace.empty _ _
  refine ⟨cs, ?_⟩
  let _ : ChartedSpace (EuclideanHalfSpace (k + 1)) (∅ : Set M) := cs
  let hs : IsManifold (𝓡∂ (k + 1)) ∞ (∅ : Set M) := inferInstance
  refine ⟨hs, ?_⟩
  let _ : IsManifold (𝓡∂ (k + 1)) ∞ (∅ : Set M) := hs
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

end EmptyFiber


end Manifold
