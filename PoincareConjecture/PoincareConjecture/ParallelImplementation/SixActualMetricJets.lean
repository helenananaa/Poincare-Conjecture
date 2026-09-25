import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.SixMetricValueCurveDerivative
import PoincareConjecture.ParallelImplementation.SixMetricGradientCurveDerivative
import PoincareConjecture.ParallelImplementation.SixActualHessianSymmetry
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixActualMetricJets
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem actual_metric_coordinate_jets
    (u : E3 → E6) (hu : ContDiff ℝ 2 u) (x : E3) :

    let g : E3 → Mat := fun y i j => (if i = j then 1 else 0) + symmetricSixMatrix (u y) i j
    let d : E3 → First := fun y a i j => symmetricSixMatrix (fderiv ℝ u y (EuclideanSpace.single a 1)) i j
    let dd : Second := fun a b i j => symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j
    (∀ a i j, HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.single a 1) i j) (d x a i j) 0) ∧
    (∀ a b i j, HasDerivAt (fun t : ℝ => d (x + t • EuclideanSpace.single a 1) b i j) (dd a b i j) 0) ∧
    (∀ y i j, g y i j = g y j i) ∧ (∀ y a i j, d y a i j = d y a j i) ∧
    (∀ a b i j, dd a b i j = dd b a i j) ∧ (∀ a b i j, dd a b i j = dd a b j i) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  let A : E3 → E3 →L[ℝ] E6 := fun y => fderiv ℝ u y
  let H : E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ (fderiv ℝ u) x
  have hu' : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hA : HasFDerivAt A H x := by
    have hcont : ContDiff ℝ 1 (fderiv ℝ u) :=
      hu.fderiv_right (m := 1) (by norm_num)
    have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hcont.differentiable (by simp)).differentiableAt
    have hh := hdiff.hasFDerivAt
    simpa [A, H] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a i j
    have hval :=
      PoincareConjecture.ParallelImplementation.SixMetricValueCurveDerivative.six_value_curve_derivative
        u (fderiv ℝ u x) x hu'
    have h := hval a i j
    change HasDerivAt
      (fun t : ℝ => (if i = j then 1 else 0) +
        symmetricSixMatrix (u (x + t • EuclideanSpace.single a 1)) i j)
      (symmetricSixMatrix (fderiv ℝ u x (EuclideanSpace.single a 1)) i j) 0
    exact h.const_add (if i = j then 1 else 0)
  · intro a b i j
    have hgrad :=
      PoincareConjecture.ParallelImplementation.SixMetricGradientCurveDerivative.six_gradient_curve_derivative
        A H x hA
    have h := hgrad a b i j
    simpa [A, H] using h
  · intro y i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricSixMatrix]
  · intro y a i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricSixMatrix]
  · intro a b i j
    have hsym :=
      PoincareConjecture.ParallelImplementation.SixActualHessianSymmetry.actual_six_hessian_symmetry
        u x hu.contDiffAt
    exact congrArg (fun q : E6 => symmetricSixMatrix q i j) (hsym.1 _ _)
  · intro a b i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricSixMatrix]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixActualMetricJets
