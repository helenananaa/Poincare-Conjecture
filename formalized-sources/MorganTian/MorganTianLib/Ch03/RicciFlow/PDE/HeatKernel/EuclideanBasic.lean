import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** The actual product Gaussian in Euclidean dimension n, including
three-dimensional coordinate domains needed for the Ricci--DeTurck equation. -/
def euclideanHeatKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i : Fin n, gaussianHeatKernel t (x i)

theorem euclideanHeatKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < euclideanHeatKernel n t x := by
  unfold euclideanHeatKernel
  exact Finset.prod_pos (fun i _ => gaussianHeatKernel_pos ht (x i))

end MorganTianLib.ParabolicPDE
