import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OperatorInverseLocalDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem operator_inverse_local_derivative
    (g : E3 → (E3 →L[ℝ] E3)) (g' : E3 →L[ℝ] (E3 →L[ℝ] E3))
    (x : E3) (hg : HasFDerivAt g g' x) (hunit : IsUnit (g x)) :

    (∃ D : E3 →L[ℝ] (E3 →L[ℝ] E3), HasFDerivAt (fun y => Ring.inverse (g y)) D x ∧
      ∀ v : E3, D v = -(Ring.inverse (g x) * g' v * Ring.inverse (g x))) ∧
      ∀ᶠ y in 𝓝 x, g y * Ring.inverse (g y) = 1 ∧ Ring.inverse (g y) * g y = 1 :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · let D : E3 →L[ℝ] (E3 →L[ℝ] E3) :=
      (-ContinuousLinearMap.mulLeftRight ℝ (E3 →L[ℝ] E3)
        (Ring.inverse (g x)) (Ring.inverse (g x))).comp g'
    refine ⟨D, ?_, ?_⟩
    · have hinv : HasFDerivAt Ring.inverse
          (-ContinuousLinearMap.mulLeftRight ℝ (E3 →L[ℝ] E3)
            (Ring.inverse (g x)) (Ring.inverse (g x))) (g x) := by
        rcases hunit with ⟨u, hu⟩
        rw [← hu]
        simpa [Ring.inverse_unit] using
          (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
      simpa [D, Function.comp_def] using hinv.comp x hg
    · intro v
      simp [D, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
  · have hunit_eventually : ∀ᶠ y in 𝓝 x, IsUnit (g y) := by
      have hunit_nhds : {z : E3 →L[ℝ] E3 | IsUnit z} ∈ 𝓝 (g x) :=
        Units.isOpen.mem_nhds hunit
      exact hg.continuousAt.eventually_mem hunit_nhds
    filter_upwards [hunit_eventually] with y hy
    exact ⟨Ring.isUnit_iff_mul_inverse_cancel.mp hy,
      (Ring.isUnit_iff_inverse_mul_cancel (g y)).mp hy⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OperatorInverseLocalDerivative
