import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedFreeHeatField
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
/-- A real Picard map built from initial heat evolution and nonlinear Duhamel integration. -/
theorem actual_heat_picard_map (f : E3 →ᵇ ℝ) (hf : UniformContinuous f)
    (N : ℝ → ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|) :
    ∃ Φ : HeatSpace → HeatSpace,
      (∀ u p, Φ u p =
        (if max 0 (min T p.1) = 0 then f p.2 else
          ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)) y * f (p.2-y)) +
        ∫ s in (0:ℝ)..max 0 (min T p.1), ∫ y : E3,
          euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (u (s,p.2-y))) ∧
      ∀ u v, ‖Φ u-Φ v‖ ≤ T*L*‖u-v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨P, hPnorm, hP⟩ := clipped_free_heat_field f hf T hT
  obtain ⟨D, hD, hDnorm, hDlip⟩ := clipped_duhamel_operator T hT
  obtain ⟨A, hA, hAnorm, hAlip⟩ := bounded_nemytskii_operator N L hL hN
  let Φ : HeatSpace → HeatSpace := fun u => P + D (A u)
  have hsub (u v : HeatSpace) :
      Φ u - Φ v = D (A u) - D (A v) := by
    ext p
    dsimp [Φ]
    ring
  refine ⟨Φ, ?_, ?_⟩
  · intro u p
    rw [show Φ u p = P p + D (A u) p by rfl, hP p, hD (A u) p]
    simp_rw [hA]
  · intro u v
    rw [hsub]
    calc
      ‖D (A u) - D (A v)‖ ≤ T * ‖A u - A v‖ := hDlip _ _
      _ ≤ T * (L * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (hAlip u v) hT
      _ = T * L * ‖u - v‖ := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
