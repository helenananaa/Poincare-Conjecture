import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ActualHeatPicardMap
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
/-- Existence and uniqueness for an actual nonlinear integral equation, with no assumed solver. -/
theorem semilinear_mild_exists_unique (f : E3 →ᵇ ℝ) (hf : UniformContinuous f)
    (N : ℝ → ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : T*L < 1)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|) :
    ∃! u : HeatSpace, ∀ p : ℝ × E3, u p =
      (if max 0 (min T p.1) = 0 then f p.2 else
        ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)) y * f (p.2-y)) +
      ∫ s in (0:ℝ)..max 0 (min T p.1), ∫ y : E3,
        euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (u (s,p.2-y)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Φ, hΦ, hΦlip⟩ := actual_heat_picard_map f hf N L T hL hT hN
  let K : NNReal := (T * L).toNNReal
  have hTL : 0 ≤ T * L := mul_nonneg hT hL
  have hKlt : K < 1 := by
    simpa [K] using (Real.toNNReal_lt_one.mpr hLT)
  have hΦlip' : LipschitzWith K Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa [dist_eq_norm, K, Real.coe_toNNReal _ hTL] using hΦlip u v
  let hcontract : ContractingWith K Φ := ⟨hKlt, hΦlip'⟩
  let c : HeatSpace := ContractingWith.fixedPoint Φ hcontract
  have hc : Φ c = c := by
    exact hcontract.fixedPoint_isFixedPt
  refine ⟨c, ?_, ?_⟩
  · intro p
    calc
      c p = Φ c p := by rw [hc]
      _ = _ := hΦ c p
  · intro u hu
    have hu' : Φ u = u := by
      apply BoundedContinuousFunction.ext
      intro p
      exact (hΦ u p).trans (hu p).symm
    exact hcontract.fixedPoint_unique hu'
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
