import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FixedLinearMetricCongruence
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_fixed_metric_congruence
    (A : E3 ≃L[ℝ] E3) :

    ∃ C : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3),
      ‖C‖ ≤ ‖A.toContinuousLinearMap‖^2 ∧
      ∀ (M : E3 →L[ℝ] E3) (v w : E3), inner ℝ (C M v) w = inner ℝ (M (A v)) (A w) :=
/- SWARM_PROOF_BEGIN -/
by
  let comp := ContinuousLinearMap.compL ℝ E3 E3 E3
  let right : (E3 →L[ℝ] E3) →L[ℝ] E3 →L[ℝ] E3 :=
    comp.flip A.toContinuousLinearMap
  let left : (E3 →L[ℝ] E3) →L[ℝ] E3 →L[ℝ] E3 :=
    comp (ContinuousLinearMap.adjoint A.toContinuousLinearMap)
  let C : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) := left.comp right
  have hAdj : ‖ContinuousLinearMap.adjoint A.toContinuousLinearMap‖ =
      ‖A.toContinuousLinearMap‖ := by
    exact ContinuousLinearMap.adjoint.norm_map _
  have hRight : ‖right‖ ≤ ‖A.toContinuousLinearMap‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro M
    change ‖M.comp A.toContinuousLinearMap‖ ≤
      ‖A.toContinuousLinearMap‖ * ‖M‖
    calc
      ‖M.comp A.toContinuousLinearMap‖ ≤ ‖M‖ * ‖A.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖A.toContinuousLinearMap‖ * ‖M‖ := by ring
  have hLeft : ‖left‖ ≤ ‖ContinuousLinearMap.adjoint A.toContinuousLinearMap‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro M
    change ‖(ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp M‖ ≤
      ‖ContinuousLinearMap.adjoint A.toContinuousLinearMap‖ * ‖M‖
    exact ContinuousLinearMap.opNorm_comp_le _ _
  refine ⟨C, ?_, ?_⟩
  · calc
      ‖C‖ ≤ ‖left‖ * ‖right‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ContinuousLinearMap.adjoint A.toContinuousLinearMap‖ *
          ‖A.toContinuousLinearMap‖ :=
        mul_le_mul hLeft hRight (norm_nonneg _) (norm_nonneg _)
      _ = ‖A.toContinuousLinearMap‖ ^ 2 := by rw [hAdj]; ring
  · intro M v w
    change inner ℝ
        ((ContinuousLinearMap.adjoint A.toContinuousLinearMap) ((M.comp A.toContinuousLinearMap) v)) w =
      inner ℝ (M (A v)) (A w)
    rw [ContinuousLinearMap.adjoint_inner_left]
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FixedLinearMetricCongruence
