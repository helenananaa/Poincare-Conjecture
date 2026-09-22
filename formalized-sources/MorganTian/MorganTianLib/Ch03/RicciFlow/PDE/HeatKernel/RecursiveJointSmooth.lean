import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Smoothness of the actual product Gaussian in joint positive-time and space variables. -/
theorem euclideanHeatKernel_joint_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) => euclideanHeatKernel n p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  unfold euclideanHeatKernel
  refine contDiffOn_prod ?_
  intro i hi p hp
  rcases p with ⟨t, x⟩
  have ht : 0 < t := hp.1
  have hsqrt_arg : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) => 4 * Real.pi * q.1) (t, x) := by
    fun_prop
  have hsqrt_arg_ne : 4 * Real.pi * t ≠ 0 := by
    positivity
  have hsqrt := hsqrt_arg.sqrt hsqrt_arg_ne
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := by
    positivity
  have hinv : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt (4 * Real.pi * q.1))⁻¹) (t, x) :=
    hsqrt.inv hsqrt_ne
  have hcoord : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.2 i) (t, x) := by
    fun_prop
  have hsq : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.2 i) ^ 2) (t, x) :=
    hcoord.pow 2
  have hden : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) => 4 * q.1) (t, x) := by
    fun_prop
  have hden_ne : 4 * t ≠ 0 := by
    positivity
  have hexp_arg : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        -((q.2 i) ^ 2) / (4 * q.1)) (t, x) :=
    hsq.neg.div hden hden_ne
  have hkernel : ContDiffAt ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        gaussianHeatKernel q.1 (q.2 i)) (t, x) := by
    unfold gaussianHeatKernel
    exact hinv.mul hexp_arg.exp
  exact hkernel.contDiffWithinAt
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
