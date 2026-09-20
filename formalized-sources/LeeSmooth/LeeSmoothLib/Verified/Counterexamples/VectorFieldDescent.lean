import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace VectorFieldDescentObstruction

/-- A descended coefficient with these two half-line values is necessarily absolute value. -/
theorem coefficient_eq_abs_of_halfLine_rules {Y : ℝ → ℝ}
    (hpos : ∀ t, 0 ≤ t → Y t = t)
    (hneg : ∀ t, 0 ≤ t → Y (-t) = t) : Y = abs := by
  funext x
  by_cases hx : 0 ≤ x
  · exact (hpos x hx).trans (abs_of_nonneg hx).symm
  · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    calc
      Y x = -x := by simpa only [neg_neg] using hneg (-x) (neg_nonneg.mpr hxle)
      _ = |x| := (abs_of_nonpos hxle).symm

/-- Scalar obstruction underlying the two-half-line descent counterexample. This lemma
checks the coefficient obstruction, not the entire manifold/tangent-bundle encoding. -/
theorem no_differentiable_descent_of_halfLine_rules :
    ¬ ∃ Y : ℝ → ℝ, DifferentiableAt ℝ Y 0 ∧
      (∀ t, 0 ≤ t → Y t = t) ∧ (∀ t, 0 ≤ t → Y (-t) = t) := by
  rintro ⟨Y, hY, hpos, hneg⟩
  have heq := coefficient_eq_abs_of_halfLine_rules hpos hneg
  exact not_differentiableAt_abs_zero (by simpa only [heq] using hY)

end VectorFieldDescentObstruction
