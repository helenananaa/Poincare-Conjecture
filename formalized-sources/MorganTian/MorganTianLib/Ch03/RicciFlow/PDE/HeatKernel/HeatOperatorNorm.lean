import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatOperator

open Set MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** Positive-time heat operators preserve constants and have norm exactly one, not a strict contraction factor. -/
theorem exists_three_dimensional_heat_operator_norm_one :
    ∃ A : ℝ → ((E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ)), ∀ t : ℝ, 0 < t →
      (∀ (f : E3 →ᵇ ℝ) (x : E3),
        Integrable (fun y : E3 => euclideanHeatKernel 3 t y * f (x - y)) volume ∧
        A t f x = ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) ∧
      A t (BoundedContinuousFunction.const E3 (1 : ℝ)) =
        BoundedContinuousFunction.const E3 (1 : ℝ) ∧ ‖A t‖ = 1 := by
  obtain ⟨A, hA⟩ := exists_three_dimensional_bounded_heat_operator
  refine ⟨A, ?_⟩
  intro t ht
  have hfix : A t (BoundedContinuousFunction.const E3 (1 : ℝ)) =
      BoundedContinuousFunction.const E3 (1 : ℝ) := by
    apply BoundedContinuousFunction.ext
    intro x
    rw [(hA t ht).2 (BoundedContinuousFunction.const E3 (1 : ℝ)) x |>.2]
    simpa only [BoundedContinuousFunction.const_apply, mul_one] using
      ((euclideanHeatKernel_mass_semigroup 3).1 t ht).2
  refine ⟨(hA t ht).2, hfix, le_antisymm (hA t ht).1 ?_⟩
  have h := (A t).le_opNorm (BoundedContinuousFunction.const E3 (1 : ℝ))
  simpa [hfix] using h

end MorganTianLib.ParabolicPDE
