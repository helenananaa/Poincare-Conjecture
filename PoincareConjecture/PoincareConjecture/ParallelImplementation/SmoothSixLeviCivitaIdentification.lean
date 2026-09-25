import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
import PoincareConjecture.ParallelImplementation.SymmetricSixMatrixLinear
import PoincareConjecture.ParallelImplementation.SixActualMetricJets
import PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible
import PoincareConjecture.ParallelImplementation.SmoothSixRiemannianMetric
import PoincareConjecture.ParallelImplementation.EuclideanLeviCivitaCoefficients
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixLeviCivitaIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_six_levicivita_identification
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∃ V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
        (∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w) ∧
        (∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) ∧
        ∀ (x : E3) (i j k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((g.leviCivitaConnection.cov (V i) (V j)) x) =
          christoffelField E u x k i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨g, hg, hcoeff⟩ :=
    PoincareConjecture.ParallelImplementation.SmoothSixRiemannianMetric.exists_smooth_six_metric
      E hE u hu hpos
  obtain ⟨V, hV, hcoordinate⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanLeviCivitaCoefficients.exists_intrinsic_coordinate_coefficients
  refine ⟨g, V, hg, hV, ?_⟩
  intro x i j k

  let A : E3 →L[ℝ] E3 := metricOp E u x
  have hunit : IsUnit A := by
    apply PoincareConjecture.ParallelImplementation.PositiveOperatorInvertible.positive_operator_isUnit
    intro v hv
    exact hpos x v hv
  let b : E3 →L[ℝ] E3 := Ring.inverse A
  have hab : A * b = 1 := by
    exact Ring.isUnit_iff_mul_inverse_cancel.mp hunit
  have hba : b * A = 1 := by
    exact (Ring.isUnit_iff_inverse_mul_cancel A).mp hunit
  have hAlg :=
    PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra.six_inverse_coordinate_algebra
      E hE (u x) b (by simpa [A, b, metricOp] using hab)
        (by simpa [A, b, metricOp] using hba)

  have hInv : ∀ a c : Idx,
      (∑ l : Idx, inverseCoefficients E u x a l *
        g.metricInner x (EuclideanSpace.single l 1) (EuclideanSpace.single c 1)) =
        if a = c then 1 else 0 := by
    intro a c
    have hleft := hAlg.2.2.2 a c
    calc
      (∑ l : Idx, inverseCoefficients E u x a l *
          g.metricInner x (EuclideanSpace.single l 1) (EuclideanSpace.single c 1)) =
          ∑ l : Idx, (b (EuclideanSpace.single l 1)) a *
            metricCoefficients u x l c := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hcoeff x l c]
              rfl
      _ = if a = c then 1 else 0 := by
        simpa [inverseCoefficients, metricCoefficients, b, A, metricOp] using hleft

  have hjets :=
    PoincareConjecture.ParallelImplementation.SixActualMetricJets.actual_metric_coordinate_jets
      u (hu.of_le (show (2 : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) x
  have hd : ∀ a p q : Idx,
      fderiv ℝ (fun y : E3 => g.metricInner y
        (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single a 1) = firstCoefficients u x a p q := by
    intro a p q
    let v : E3 := EuclideanSpace.single a 1
    have hmetricFun : (fun y : E3 => g.metricInner y
        (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)) =
        (fun y : E3 => metricCoefficients u y p q) := by
      funext y
      exact hcoeff y p q
    have hcurve0 := hjets.1 a p q
    have hcurve : HasDerivAt
        (fun t : ℝ => g.metricInner (x + t • v)
          (EuclideanSpace.single p 1) (EuclideanSpace.single q 1))
        (firstCoefficients u x a p q) 0 := by
      have hcurveFun : (fun t : ℝ => g.metricInner (x + t • v)
          (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)) =
          (fun t : ℝ => metricCoefficients u (x + t • v) p q) := by
        funext t
        exact hcoeff (x + t • v) p q
      rw [hcurveFun]
      simpa [metricCoefficients, firstCoefficients, v] using hcurve0
    have huDiff : Differentiable ℝ u := hu.differentiable (by simp)
    have hcoeffDiff : DifferentiableAt ℝ
        (fun y : E3 => metricCoefficients u y p q) x := by
      fin_cases p <;> fin_cases q <;>
        simp [metricCoefficients, symmetricSixMatrix] <;> fun_prop
    have hmetricDiff : DifferentiableAt ℝ
        (fun y : E3 => g.metricInner y
          (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)) x := by
      rw [hmetricFun]
      exact hcoeffDiff
    have hF : HasFDerivAt
        (fun y : E3 => g.metricInner y
          (EuclideanSpace.single p 1) (EuclideanSpace.single q 1))
        (fderiv ℝ (fun y : E3 => g.metricInner y
          (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)) x) x :=
      hmetricDiff.hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa [v] using (hasDerivAt_id' (0 : ℝ)).smul_const v |>.const_add x
    have hchain := hF.comp_hasDerivAt_of_eq 0 hline (by simp)
    have heq := hcurve.unique hchain
    simpa [v] using heq.symm

  have hconn := hcoordinate g x (inverseCoefficients E u x) (firstCoefficients u x)
    hInv hd i j k
  change (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ)
      ((g.leviCivitaConnection.cov (V i) (V j)) x) = _
  rw [hconn]
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixLeviCivitaIdentification
