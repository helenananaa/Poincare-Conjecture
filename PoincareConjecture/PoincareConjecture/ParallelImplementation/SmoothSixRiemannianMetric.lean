import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixRiemannianMetric
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_smooth_six_metric
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      (∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w) ∧
      ∀ (x : E3) (i j : Idx), g.metricInner x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) = metricCoefficients u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  have hA : ContDiff ℝ ∞ (metricOp E u) := by
    unfold metricOp
    exact contDiff_const.add (E.contDiff.comp hu)
  have hE_sym (q : E6) (v w : E3) :
      inner ℝ (E q v) w = inner ℝ v (E q w) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    simp_rw [hE]
    simp [Fin.sum_univ_succ, symmetricSixMatrix]
    ring
  have hsym : ∀ (x v w : E3),
      inner ℝ (metricOp E u x v) w = inner ℝ (metricOp E u x w) v := by
    intro x v w
    change inner ℝ (v + E (u x) v) w = inner ℝ (w + E (u x) w) v
    simp only [inner_add_left]
    rw [real_inner_comm v w, hE_sym (u x) v w, real_inner_comm v (E (u x) w)]
  obtain ⟨g, hg⟩ := PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric.exists_positive_operator_metric
    (metricOp E u) hA hsym hpos
  refine ⟨g, hg, ?_⟩
  intro x i j
  rw [hg x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
  rw [hsym x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
  have hentry :
      (metricOp E u x (EuclideanSpace.single j 1)) i = metricCoefficients u x i j := by
    simp [metricOp, metricCoefficients, hE]
  rw [show inner ℝ (metricOp E u x (EuclideanSpace.single j 1))
      (EuclideanSpace.single i 1) =
        (metricOp E u x (EuclideanSpace.single j 1)) i by
        simp [PiLp.inner_apply]]
  exact hentry
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixRiemannianMetric
