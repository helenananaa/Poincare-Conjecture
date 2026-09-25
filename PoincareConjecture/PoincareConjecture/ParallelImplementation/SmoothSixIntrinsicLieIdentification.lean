import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import PoincareConjecture.ParallelImplementation.SixActualMetricJets
import PoincareConjecture.ParallelImplementation.SixMetricValueCurveDerivative
import PoincareConjecture.ParallelImplementation.SymmetricSixMatrixLinear
import PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative
import PoincareConjecture.ParallelImplementation.EuclideanMetricLieCoordinates
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicLieIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem six_intrinsic_lie_identification
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v)
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (hg : ∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w)
    (W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (hW : ∀ (x : E3) (k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W x) = deturckField E u x k) :

    ∀ (x : E3) (i j : Idx), MorganTianLib.metricLieDerivativeAt g W x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = actualLie E u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i j
  let π : Idx → E3 →L[ℝ] ℝ := fun k =>
    PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k
  have hmetricCoeff (y : E3) (a b : Idx) :
      g.metricInner y (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
        metricCoefficients u y a b := by
    rw [hg]
    have hentry :
        (metricOp E u y (EuclideanSpace.single a 1)) b =
          metricCoefficients u y a b := by
      fin_cases a <;> fin_cases b <;>
        simp [metricOp, metricCoefficients, hE, symmetricSixMatrix]
    rw [show inner ℝ (metricOp E u y (EuclideanSpace.single a 1))
        (EuclideanSpace.single b 1) =
          (metricOp E u y (EuclideanSpace.single a 1)) b by
        simp [PiLp.inner_apply]]
    exact hentry

  have hjets :=
    PoincareConjecture.ParallelImplementation.SixActualMetricJets.actual_metric_coordinate_jets
      u (hu.of_le (show (2 : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) x
  have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
  have hmetricDiff (a b : Idx) : DifferentiableAt ℝ
      (fun y : E3 => g.metricInner y
        (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) x := by
    rw [show (fun y : E3 => g.metricInner y
        (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) =
        (fun y : E3 => metricCoefficients u y a b) by
          funext y
          exact hmetricCoeff y a b]
    fin_cases a <;> fin_cases b <;>
      simp [metricCoefficients, symmetricSixMatrix] <;> fun_prop
  have hmetricDeriv (c a b : Idx) :
      fderiv ℝ (fun y : E3 => g.metricInner y
        (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) x
          (EuclideanSpace.single c 1) = firstCoefficients u x c a b := by
    let v : E3 := EuclideanSpace.single c 1
    have hcurve0 := hjets.1 c a b
    have hcurve : HasDerivAt
        (fun t : ℝ => g.metricInner (x + t • v)
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1))
        (firstCoefficients u x c a b) 0 := by
      have hcurveFun : (fun t : ℝ => g.metricInner (x + t • v)
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) =
          (fun t : ℝ => metricCoefficients u (x + t • v) a b) := by
        funext t
        exact hmetricCoeff (x + t • v) a b
      rw [hcurveFun]
      simpa [metricCoefficients, firstCoefficients, v] using hcurve0
    calc
      fderiv ℝ (fun y : E3 => g.metricInner y
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) x
            (EuclideanSpace.single c 1) =
          deriv (fun t : ℝ => g.metricInner (x + t • v)
            (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) 0 := by
              simpa [v] using
                (PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative.fderiv_eq_coordinate_deriv
                  (fun y : E3 => g.metricInner y
                    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1))
                  x c (hmetricDiff a b))
      _ = firstCoefficients u x c a b := hcurve.deriv

  have hWcoord (y : E3) (k : Idx) : π k (W y) = deturckField E u y k :=
    hW y k
  have hWline (k a : Idx) :
      deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single a 1))) 0 =
        deriv (fun t : ℝ => deturckField E u (x + t • EuclideanSpace.single a 1) k) 0 := by
    apply congrArg (fun f : ℝ → ℝ => deriv f 0)
    funext t
    exact hWcoord (x + t • EuclideanSpace.single a 1) k

  have hformula :=
    PoincareConjecture.ParallelImplementation.EuclideanMetricLieCoordinates.metric_lie_coordinate_formula
      g W x i j
  calc
    MorganTianLib.metricLieDerivativeAt g W x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        ∑ k : Idx,
          (π k (W x) * fderiv ℝ (fun y : E3 => g.metricInner y
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x
                (EuclideanSpace.single k 1) +
            g.metricInner x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) *
              deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single i 1))) 0 +
            g.metricInner x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
              deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single j 1))) 0) := hformula
    _ = actualLie E u x i j := by
      rw [actualLie]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hWcoord x k, hmetricDeriv k i j,
        hmetricCoeff x k j, hmetricCoeff x i k,
        hWline k i, hWline k j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicLieIdentification
