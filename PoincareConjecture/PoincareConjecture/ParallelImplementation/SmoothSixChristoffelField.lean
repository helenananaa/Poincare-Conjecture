import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
import PoincareConjecture.ParallelImplementation.SmoothOperatorInverse
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixChristoffelField
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem smooth_six_christoffel
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∀ k i j : Idx, ContDiff ℝ ∞ (fun x : E3 => christoffelField E u x k i j) :=
/- SWARM_PROOF_BEGIN -/
by
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
  have hfirst : ∀ a i j : Idx,
      ContDiff ℝ ∞ (fun x : E3 => firstCoefficients u x a i j) := by
    intro a i j
    have hv : ContDiff ℝ ∞ (fun x : E3 =>
        fderiv ℝ u x (EuclideanSpace.single a 1)) :=
      (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    fin_cases i <;> fin_cases j <;>
      simp [firstCoefficients, symmetricSixMatrix] <;>
      exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2)).comp hv
  have hlower : ∀ l i j : Idx,
      ContDiff ℝ ∞ (fun x : E3 =>
        lowerChristoffel (firstCoefficients u x) l i j) := by
    intro l i j
    simp only [lowerChristoffel]
    exact contDiff_const.mul
      (((hfirst i j l).add (hfirst j i l)).sub (hfirst l i j))
  intro k i j
  simp only [christoffelField, christoffel]
  fun_prop
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixChristoffelField
