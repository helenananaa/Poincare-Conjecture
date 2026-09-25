import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicRicciIdentification
import PoincareConjecture.ParallelImplementation.SmoothSixDeTurckVector
import PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicLieIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicDeTurckIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_six_intrinsic_deturck_identification
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∃ W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
        (∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w) ∧
        (∀ (x : E3) (k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W x) = deturckField E u x k) ∧
        (∀ (x : E3) (i j : Idx), MorganTianLib.ricciTensorAt g x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = actualRicci E u x i j) ∧
        (∀ (x : E3) (i j : Idx), MorganTianLib.metricLieDerivativeAt g W x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = actualLie E u x i j) ∧
        ∀ (x : E3) (i j : Idx), MorganTianLib.ricciDeTurckVariation g W x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
          -2*actualRicci E u x i j + actualLie E u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨g, hg, hric⟩ :=
    PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicRicciIdentification.exists_six_intrinsic_ricci_identification
      E hE u hu hpos
  obtain ⟨W, hW⟩ :=
    PoincareConjecture.ParallelImplementation.SmoothSixDeTurckVector.exists_smooth_deturck_vector
      E hE u hu hpos
  have hlie :=
    PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicLieIdentification.six_intrinsic_lie_identification
      E hE u hu hpos g hg W hW
  refine ⟨g, W, hg, hW, hric, hlie, ?_⟩
  intro x i j
  change -2 * MorganTianLib.ricciTensorAt g x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      MorganTianLib.metricLieDerivativeAt g W x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
    -2 * actualRicci E u x i j + actualLie E u x i j
  rw [hric x i j, hlie x i j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicDeTurckIdentification
