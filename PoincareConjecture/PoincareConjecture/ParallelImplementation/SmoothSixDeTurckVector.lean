import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import PoincareConjecture.ParallelImplementation.SmoothSixChristoffelField
import PoincareConjecture.ParallelImplementation.SmoothOperatorInverse
import PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixDeTurckVector
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_smooth_deturck_vector
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
      ∀ (x : E3) (k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W x) = deturckField E u x k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hmetric : ContDiff ℝ ∞ (fun x : E3 => metricOp E u x) := by
    change ContDiff ℝ ∞ (fun x : E3 => (1 : E3 →L[ℝ] E3) + E (u x))
    exact contDiff_const.add (E.contDiff.comp hu)
  have hunit : ∀ x : E3, IsUnit (metricOp E u x) := by
    intro x
    apply PositiveOperatorInvertible.positive_operator_isUnit
    intro v hv
    exact hpos x v hv
  have hinv : ContDiff ℝ ∞ (fun x : E3 => Ring.inverse (metricOp E u x)) :=
    SmoothOperatorInverse.smooth_operator_inverse (A := fun x => metricOp E u x)
      hmetric hunit
  have hinvCoeff : ∀ i j : Idx,
      ContDiff ℝ ∞ (fun x : E3 => inverseCoefficients E u x i j) := by
    intro i j
    have hv : ContDiff ℝ ∞ (fun x : E3 =>
        Ring.inverse (metricOp E u x) (EuclideanSpace.single j 1)) :=
      hinv.clm_apply contDiff_const
    change ContDiff ℝ ∞ (fun x : E3 =>
      (Ring.inverse (metricOp E u x) (EuclideanSpace.single j 1)) i)
    exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := i)).comp hv
  have hchrist := SmoothSixChristoffelField.smooth_six_christoffel
      E hE u hu hpos
  have hcoord : ∀ k : Idx, ContDiff ℝ ∞ (fun x : E3 => deturckField E u x k) := by
    intro k
    change ContDiff ℝ ∞ (fun x : E3 =>
      ∑ a : Idx, ∑ b : Idx,
        inverseCoefficients E u x a b * christoffelField E u x k a b)
    apply ContDiff.sum
    intro a ha
    apply ContDiff.sum
    intro b hb
    exact (hinvCoeff a b).mul (hchrist k a b)
  let W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3 :=
    ⟨fun x => WithLp.toLp 2 (fun k : Idx => deturckField E u x k), by
      rw [contMDiff_vectorSpace_iff_contDiff]
      apply (contDiff_piLp 2).2
      exact hcoord⟩
  refine ⟨W, ?_⟩
  intro x k
  simp [W, PiLp.proj_apply]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixDeTurckVector
