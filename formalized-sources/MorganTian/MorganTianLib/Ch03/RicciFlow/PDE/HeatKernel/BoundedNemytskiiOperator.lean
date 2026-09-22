import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedDuhamelNonlinearDifference
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "HeatSpace" => (ℝ × E3) →ᵇ ℝ
/-- Construct the actual bounded nonlinear composition map with its norm and Lipschitz bounds. -/
theorem bounded_nemytskii_operator (N : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|) :
    ∃ A : HeatSpace → HeatSpace,
      (∀ u p, A u p = N (u p)) ∧
      (∀ u, ‖A u‖ ≤ |N 0|+L*‖u‖) ∧
      ∀ u v, ‖A u-A v‖ ≤ L*‖u-v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun a b : ℝ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN a b)
  have hNcont : Continuous N := hNlip.continuous
  have hC (u : HeatSpace) : 0 ≤ |N 0| + L * ‖u‖ := by
    positivity
  have hcont (u : HeatSpace) : Continuous (fun p : ℝ × E3 => N (u p)) :=
    hNcont.comp u.continuous
  have hbound (u : HeatSpace) : ∀ p : ℝ × E3, ‖N (u p)‖ ≤ |N 0| + L * ‖u‖ := by
    intro p
    rw [Real.norm_eq_abs]
    calc
      |N (u p)| ≤ |N (u p) - N 0| + |N 0| := by
        calc
          |N (u p)| = |(N (u p) - N 0) + N 0| := by congr 1; ring
          _ ≤ |N (u p) - N 0| + |N 0| := abs_add_le _ _
      _ ≤ L * |u p| + |N 0| := by
        gcongr
        simpa using hN (u p) 0
      _ ≤ |N 0| + L * ‖u‖ := by
        have hu : |u p| ≤ ‖u‖ := by
          rw [← Real.norm_eq_abs]
          exact u.norm_coe_le_norm p
        calc
          L * |u p| + |N 0| = |N 0| + L * |u p| := add_comm _ _
          _ ≤ |N 0| + L * ‖u‖ := by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_left hu hL) |N 0|)
  let A : HeatSpace → HeatSpace := fun u =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (u p)) (hcont u) (|N 0| + L * ‖u‖) (hbound u)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro u p
    rfl
  · intro u
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (hcont u) (hC u) (hbound u)
  · intro u v
    have hdiffcont : Continuous (fun p : ℝ × E3 => N (u p) - N (v p)) :=
      (hcont u).sub (hcont v)
    have hdiffnonneg : 0 ≤ L * ‖u - v‖ := mul_nonneg hL (norm_nonneg _)
    have hdiffbound : ∀ p : ℝ × E3,
        ‖N (u p) - N (v p)‖ ≤ L * ‖u - v‖ := by
      intro p
      rw [Real.norm_eq_abs]
      have hp : |u p - v p| ≤ ‖u - v‖ := by
        rw [← Real.norm_eq_abs]
        exact (u - v).norm_coe_le_norm p
      exact (hN (u p) (v p)).trans
        (mul_le_mul_of_nonneg_left hp hL)
    let D : HeatSpace := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (u p) - N (v p)) hdiffcont (L * ‖u - v‖) hdiffbound
    have hD : ‖D‖ ≤ L * ‖u - v‖ :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
        hdiffcont hdiffnonneg hdiffbound
    have hpoint : ∀ p : ℝ × E3, (A u - A v) p = D p := by
      intro p
      rfl
    calc
      ‖A u - A v‖ = ‖D‖ := by
        apply congrArg norm
        apply BoundedContinuousFunction.ext
        exact hpoint
      _ ≤ L * ‖u - v‖ := hD
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
